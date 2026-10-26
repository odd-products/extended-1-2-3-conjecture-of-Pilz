import WeightedPilz.ProductCoefficients
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-! Weighted coefficients at uniquely represented integer powers. The divisor
restriction in the representation set is a proved computational simplification. -/

namespace WeightedPilz.Arithmetic

/-- Unordered degree-`j` factorizations, with irrelevant nondivisors removed. -/
def powerRepresentations (A : Finset ℕ) (j m : ℕ) : Finset (Sym ℕ j) :=
  ((A.filter (fun a => a ∣ m)).sym j).filter (fun s => s.val.prod = m)

theorem powerRepresentations_eq (A : Finset ℕ) (j m : ℕ) :
    powerRepresentations A j m = (A.sym j).filter (fun s => s.val.prod = m) := by
  ext s
  simp only [powerRepresentations, Finset.mem_filter, Finset.mem_sym_iff]
  constructor
  · rintro ⟨hA, hm⟩
    exact ⟨fun a ha => (hA a ha).1, hm⟩
  · rintro ⟨hA, hm⟩
    refine ⟨?_, hm⟩
    intro a ha
    exact ⟨hA a ha, hm ▸ Multiset.dvd_prod ha⟩

theorem powerRepresentations_mono {A B : Finset ℕ} (hAB : A ⊆ B) (j m : ℕ) :
    powerRepresentations A j m ⊆ powerRepresentations B j m := by
  rw [powerRepresentations_eq, powerRepresentations_eq]
  intro s hs
  obtain ⟨hs, hm⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_sym_iff.mpr
    (fun a ha => hAB (Finset.mem_sym_iff.mp hs a ha)), hm⟩

end WeightedPilz.Arithmetic

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]

private theorem prod_monomials_nat (s : Multiset ℕ) (c : ℕ → K)
    (hs : ∀ a ∈ s, a ≠ 0) :
    (s.map (fun a => monomial a.factorization (c a))).prod =
      monomial s.prod.factorization (s.map c).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (by simp)
    have hs' : ∀ b ∈ s, b ≠ 0 := fun b hb => hs b (by simp [hb])
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hs' 0 h rfl)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [ih hs', monomial_mul, Nat.factorization_mul ha hprod]

private theorem multinomial_ne_zero_of_factorial (s : Multiset ℕ)
    (hs : (s.card.factorial : K) ≠ 0) : (s.multinomial : K) ≠ 0 := by
  have hid : (∏ a ∈ s.toFinsupp.support, (s.toFinsupp a).factorial) *
      s.multinomial = s.card.factorial := by
    have hsum : (∑ a ∈ s.toFinsupp.support, s.toFinsupp a) = s.card :=
      Multiset.toFinsupp_sum_eq s
    simpa only [Multiset.multinomial, Finsupp.multinomial_eq, hsum] using
      Nat.multinomial_spec s.toFinsupp.support s.toFinsupp
  intro hzero
  have h := congrArg (fun a : ℕ => (a : K)) hid
  dsimp only at h
  rw [Nat.cast_mul, hzero, mul_zero] at h
  exact hs h.symm

/-- The multinomial coefficient formula, with exact integer multiplicative fibers. -/
theorem coeff_polynomialOf_pow (A : Finset ℕ) (c : ℕ → K) (j : ℕ)
    (hA : ∀ a ∈ A, 0 < a) {m : ℕ} (hm : 0 < m) :
    coeff m.factorization (polynomialOf A c ^ j) =
      ∑ s ∈ Arithmetic.powerRepresentations A j m,
        (s.val.multinomial : K) * (s.val.map c).prod := by
  classical
  unfold polynomialOf
  rw [Finset.sum_pow, coeff_sum, Arithmetic.powerRepresentations_eq,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : ∀ a ∈ s.val, a ≠ 0 := fun a ha =>
    ne_of_gt (hA a (Finset.mem_sym_iff.mp hs a ha))
  rw [prod_monomials_nat s.val c hs']
  change coeff m.factorization
    (C (s.val.multinomial : K) * monomial s.val.prod.factorization (s.val.map c).prod) = _
  rw [C_mul_monomial, coeff_monomial]
  have hprod : s.val.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hs' 0 h rfl)
  have heq : s.val.prod.factorization = m.factorization ↔ s.val.prod = m :=
    ⟨Nat.factorization_inj hprod (ne_of_gt hm), congrArg Nat.factorization⟩
  simp only [heq]

/-- A unique unordered multiplicative representation cannot cancel when `j!`
is nonzero, independently of the nonzero weights. -/
theorem coeff_pow_ne_zero_of_unique_representation (A : Finset ℕ) (c : ℕ → K)
    (j : ℕ) (hA : ∀ a ∈ A, 0 < a) (hc : ∀ a ∈ A, c a ≠ 0)
    (hfac : (j.factorial : K) ≠ 0) {m : ℕ} (hm : 0 < m)
    (hrep : (Arithmetic.powerRepresentations A j m).card = 1) :
    coeff m.factorization (polynomialOf A c ^ j) ≠ 0 := by
  classical
  obtain ⟨s, hsingle⟩ := Finset.card_eq_one.mp hrep
  have hs : s ∈ Arithmetic.powerRepresentations A j m := by
    rw [hsingle]
    exact Finset.mem_singleton_self _
  rw [Arithmetic.powerRepresentations_eq] at hs
  have hsA := (Finset.mem_filter.mp hs).1
  rw [coeff_polynomialOf_pow A c j hA hm, hsingle, Finset.sum_singleton]
  apply mul_ne_zero
  · exact multinomial_ne_zero_of_factorial s.val (by simpa only [s.property] using hfac)
  · apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨a, ha, hca⟩ := Multiset.mem_map.mp hzero
    exact hc a (Finset.mem_sym_iff.mp hsA a ha) hca

/-- A certified set of unique power products injects into the actual weighted support. -/
theorem weight_pow_ge_unique_products (A T : Finset ℕ) (c : ℕ → K) (j : ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hc : ∀ a ∈ A, c a ≠ 0)
    (hfac : (j.factorial : K) ≠ 0) (hT : ∀ m ∈ T, 0 < m)
    (hrep : ∀ m ∈ T, (Arithmetic.powerRepresentations A j m).card = 1) :
    T.card ≤ weight (polynomialOf A c ^ j) := by
  have hinj : Set.InjOn Nat.factorization (↑T : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.factorization_inj (ne_of_gt (hT a ha)) (ne_of_gt (hT b hb)) hab
  rw [← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro d hd
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
  exact mem_support_iff.mpr
    (coeff_pow_ne_zero_of_unique_representation A c j hA hc hfac (hT m hm) (hrep m hm))

end WeightedPilz
