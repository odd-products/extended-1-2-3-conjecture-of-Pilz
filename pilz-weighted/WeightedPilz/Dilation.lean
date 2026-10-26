import WeightedPilz.Support
import WeightedPilz.Distance
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MvPolynomial.Expand

/-!
# Exponent dilation and residue classes

The finite-support decomposition used in `lem:exponent-dilation` is valid over
any coefficient semiring. In particular it does not extract coefficient roots.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {σ R : Type*} [CommSemiring R]

/-- Multiply every exponent by the same natural number. -/
def scaleExponent (q : ℕ) (d : σ →₀ ℕ) : σ →₀ ℕ := q • d

@[simp] theorem scaleExponent_apply (q : ℕ) (d : σ →₀ ℕ) (i : σ) :
    scaleExponent q d i = q * d i := by simp [scaleExponent]

theorem scaleExponent_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (scaleExponent (σ := σ) q) := by
  intro a b h
  ext i
  have hi := congrArg (fun d : σ →₀ ℕ => d i) h
  simpa only [scaleExponent_apply, Nat.mul_left_cancel_iff hq] using hi

/-- Exponent substitution, keeping coefficients fixed. -/
def dilate (q : ℕ) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  Finsupp.mapDomain (scaleExponent q) P

@[simp] theorem dilate_zero (q : ℕ) : dilate q (0 : MvPolynomial σ R) = 0 :=
  Finsupp.mapDomain_zero

@[simp] theorem dilate_monomial (q : ℕ) (d : σ →₀ ℕ) (c : R) :
    dilate q (monomial d c) = monomial (scaleExponent q d) c :=
  Finsupp.mapDomain_single

@[simp] theorem dilate_add (q : ℕ) (P Q : MvPolynomial σ R) :
    dilate q (P + Q) = dilate q P + dilate q Q :=
  Finsupp.mapDomain_add

@[simp] theorem dilate_mul (q : ℕ) (P Q : MvPolynomial σ R) :
    dilate q (P * Q) = dilate q P * dilate q Q := by
  let f : (σ →₀ ℕ) →+ (σ →₀ ℕ) :=
    { toFun := scaleExponent q
      map_zero' := smul_zero q
      map_add' := fun x y => nsmul_add x y q }
  exact AddMonoidAlgebra.mapDomain_mul f P Q

@[simp] theorem dilate_C (q : ℕ) (c : R) :
    dilate q (C c : MvPolynomial σ R) = C c := by
  change dilate q (monomial 0 c) = monomial 0 c
  rw [dilate_monomial]
  simp [scaleExponent]

@[simp] theorem dilate_X (q : ℕ) (i : σ) :
    dilate q (X i : MvPolynomial σ R) = X i ^ q := by
  change dilate q (monomial (Finsupp.single i 1) 1) =
    (monomial (Finsupp.single i 1) 1 : MvPolynomial σ R) ^ q
  rw [dilate_monomial, monomial_pow, one_pow]
  rfl

/-- Identification with mathlib's literal substitution `X i ↦ X i ^ q`. -/
theorem dilate_eq_expand (q : ℕ) (P : MvPolynomial σ R) :
    dilate q P = MvPolynomial.expand q P := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [dilate_C, MvPolynomial.expand_C]
  | add P Q hP hQ => rw [dilate_add, map_add, hP, hQ]
  | mul_X P i hP => rw [dilate_mul, map_mul, hP, dilate_X, MvPolynomial.expand_X]

theorem dilate_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (dilate (σ := σ) (R := R) q) :=
  Finsupp.mapDomain_injective (scaleExponent_injective hq)

@[simp] theorem dilate_eq_zero_iff {q : ℕ} (hq : 0 < q) (P : MvPolynomial σ R) :
    dilate q P = 0 ↔ P = 0 := by
  constructor
  · intro h
    apply dilate_injective hq
    simpa using h
  · rintro rfl
    exact dilate_zero q

theorem support_dilate {q : ℕ} (hq : 0 < q) (P : MvPolynomial σ R) :
    (dilate q P).support = P.support.image (scaleExponent q) := by
  classical
  exact Finsupp.mapDomain_support_of_injective (scaleExponent_injective hq) P

@[simp] theorem weight_dilate {q : ℕ} (hq : 0 < q) (P : MvPolynomial σ R) :
    weight (dilate q P) = weight P := by
  classical
  unfold weight
  rw [support_dilate hq]
  exact Finset.card_image_of_injective _ (scaleExponent_injective hq)

/-- Coordinatewise quotient and remainder for exponent vectors. -/
def quotientExponent (q : ℕ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun n => n / q) (Nat.zero_div q)

def residueExponent (q : ℕ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun n => n % q) (Nat.zero_mod q)

@[simp] theorem quotientExponent_apply (q : ℕ) (d : σ →₀ ℕ) (i : σ) :
    quotientExponent q d i = d i / q := rfl

@[simp] theorem residueExponent_apply (q : ℕ) (d : σ →₀ ℕ) (i : σ) :
    residueExponent q d i = d i % q := rfl

/-- Projection onto one full exponent residue class. -/
def residuePart (q : ℕ) (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    MvPolynomial σ R := by
  classical
  exact Finsupp.filter (fun d => residueExponent q d = α) P

@[simp] theorem coeff_residuePart (q : ℕ) (P : MvPolynomial σ R)
    (α d : σ →₀ ℕ) :
    coeff d (residuePart q P α) =
      if residueExponent q d = α then coeff d P else 0 := by
  classical
  rfl

@[simp] theorem support_residuePart (q : ℕ) (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    (residuePart q P α).support = P.support.filter (fun d => residueExponent q d = α) := by
  classical
  rfl

theorem support_residuePart_subset (q : ℕ) (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    (residuePart q P α).support ⊆ P.support := by
  classical
  rw [support_residuePart]
  exact Finset.filter_subset _ _

theorem weight_residuePart_le (q : ℕ) (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    weight (residuePart q P α) ≤ weight P :=
  Finset.card_le_card (support_residuePart_subset q P α)

@[simp] theorem residuePart_add (q : ℕ) (P Q : MvPolynomial σ R) (α : σ →₀ ℕ) :
    residuePart q (P + Q) α = residuePart q P α + residuePart q Q α := by
  classical
  exact Finsupp.filter_add

theorem residuePart_monomial (q : ℕ) (d : σ →₀ ℕ) (c : R) (α : σ →₀ ℕ) :
    residuePart q (monomial d c) α =
      if residueExponent q d = α then monomial d c else 0 := by
  classical
  by_cases h : residueExponent q d = α
  · rw [if_pos h]
    exact Finsupp.filter_single_of_pos _ h
  · rw [if_neg h]
    exact Finsupp.filter_single_of_neg _ h

/-- Divide exponents in a residue class by `q`; coefficients remain unchanged. -/
def residueRoot (q : ℕ) (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    MvPolynomial σ R := Finsupp.mapDomain (quotientExponent q) (residuePart q P α)

theorem residue_add_scale_quotient (q : ℕ) (d α : σ →₀ ℕ)
    (h : residueExponent q d = α) : α + scaleExponent q (quotientExponent q d) = d := by
  ext i
  have hi := congrArg (fun a : σ →₀ ℕ => a i) h
  simp only [residueExponent_apply] at hi
  simp only [Finsupp.add_apply, scaleExponent_apply, quotientExponent_apply, ← hi]
  exact Nat.mod_add_div (d i) q

theorem monomial_one_mul_eq_mapDomain (α : σ →₀ ℕ) (P : MvPolynomial σ R) :
    monomial α 1 * P = Finsupp.mapDomain (fun d => α + d) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [monomial_mul, one_mul]
      exact Finsupp.mapDomain_single.symm
  | add P Q hP hQ =>
      rw [mul_add, hP, hQ, Finsupp.mapDomain_add]

theorem residuePart_eq_monomial_mul_dilate (q : ℕ) (P : MvPolynomial σ R)
    (α : σ →₀ ℕ) :
    residuePart q P α = monomial α 1 * dilate q (residueRoot q P α) := by
  symm
  rw [monomial_one_mul_eq_mapDomain, dilate, residueRoot]
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  calc
    Finsupp.mapDomain ((fun d => α + d) ∘ scaleExponent q ∘ quotientExponent q)
        (residuePart q P α) = Finsupp.mapDomain id (residuePart q P α) := by
      apply Finsupp.mapDomain_congr
      intro d hd
      exact residue_add_scale_quotient q d α (Finset.mem_filter.mp hd).2
    _ = residuePart q P α := Finsupp.mapDomain_id

theorem residuePart_support_disjoint (q : ℕ) (P : MvPolynomial σ R)
    (α β : σ →₀ ℕ) (hne : α ≠ β) :
    Disjoint (residuePart q P α).support (residuePart q P β).support := by
  classical
  rw [support_residuePart, support_residuePart]
  apply Finset.disjoint_left.mpr
  intro d hα hβ
  exact hne ((Finset.mem_filter.mp hα).2.symm.trans (Finset.mem_filter.mp hβ).2)

theorem exists_nonzero_residuePart (q : ℕ) (P : MvPolynomial σ R) (hP : P ≠ 0) :
    ∃ α, residuePart q P α ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hP
  refine ⟨residueExponent q d, ?_⟩
  intro hz
  have hm : d ∈ (residuePart q P (residueExponent q d)).support :=
    Finset.mem_filter.mpr ⟨hd, rfl⟩
  simp [hz] at hm

theorem residuePart_monomial_mul_of_divisible (q : ℕ) (s : σ →₀ ℕ) (c : R)
    (P : MvPolynomial σ R) (α : σ →₀ ℕ) (hs : residueExponent q s = 0) :
    residuePart q (monomial s c * P) α = monomial s c * residuePart q P α := by
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
      have heq : residueExponent q (s + d) = residueExponent q d := by
        ext i
        have hi := congrArg (fun e : σ →₀ ℕ => e i) hs
        simp only [residueExponent_apply, Finsupp.zero_apply] at hi
        simp [residueExponent_apply, Finsupp.add_apply, Nat.add_mod, hi]
      rw [monomial_mul, residuePart_monomial, residuePart_monomial, heq]
      split_ifs <;> simp [monomial_mul]
  | add P Q hP hQ =>
      simp only [mul_add, residuePart_add, hP, hQ]

theorem residuePart_dilate_mul (q : ℕ) (P H : MvPolynomial σ R) (α : σ →₀ ℕ) :
    residuePart q (dilate q P * H) α = dilate q P * residuePart q H α := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [dilate_monomial]
      apply residuePart_monomial_mul_of_divisible
      ext i
      simp
  | add P Q hP hQ =>
      simp only [dilate_add, add_mul, residuePart_add, hP, hQ]

theorem residuePart_dilate_mul_eq (q : ℕ) (P H : MvPolynomial σ R) (α : σ →₀ ℕ) :
    residuePart q (dilate q P * H) α =
      monomial α 1 * dilate q (P * residueRoot q H α) := by
  rw [residuePart_dilate_mul, residuePart_eq_monomial_mul_dilate, dilate_mul]
  ac_rfl

theorem weight_residuePart_dilate_mul {q : ℕ} (hq : 0 < q)
    (P H : MvPolynomial σ R) (α : σ →₀ ℕ) :
    weight (residuePart q (dilate q P * H) α) = weight (P * residueRoot q H α) := by
  classical
  rw [residuePart_dilate_mul_eq, weight_monomial_mul, weight_dilate hq]

theorem support_monomial_dilate {q : ℕ} (hq : 0 < q)
    (P : MvPolynomial σ R) (α : σ →₀ ℕ) :
    (monomial α 1 * dilate q P).support =
      P.support.image (fun d => α + scaleExponent q d) := by
  have h : (monomial α 1 * dilate q P).support =
      (dilate q P).support.map (addLeftEmbedding α) :=
    AddMonoidAlgebra.support_single_mul _ 1 (by simp) α
  rw [h, support_dilate hq, Finset.map_eq_image, Finset.image_image]
  rfl

theorem residueRoot_support_lift {q : ℕ} (hq : 0 < q)
    (P : MvPolynomial σ R) (α d : σ →₀ ℕ)
    (hd : d ∈ (residueRoot q P α).support) :
    α + scaleExponent q d ∈ P.support := by
  apply support_residuePart_subset q P α
  rw [residuePart_eq_monomial_mul_dilate, support_monomial_dilate hq]
  exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

/-- Every polynomial is the finite sum of its full exponent residue classes. -/
theorem sum_residueParts (q : ℕ) (P : MvPolynomial σ R) :
    (∑ α ∈ P.support.image (residueExponent q), residuePart q P α) = P := by
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d ∈ P.support
  · have hidx : residueExponent q d ∈ P.support.image (residueExponent q) :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    rw [Finset.sum_eq_single (residueExponent q d)]
    · simp
    · intro α _ hne
      simp [Ne.symm hne]
    · exact fun h => (h hidx).elim
  · have hz := MvPolynomial.notMem_support_iff.mp hd
    simp [hz]

/-- The unique-residue expression used in the manuscript's dilation proof. -/
theorem residue_decomposition (q : ℕ) (P : MvPolynomial σ R) :
    P = ∑ α ∈ P.support.image (residueExponent q),
      monomial α 1 * dilate q (residueRoot q P α) := by
  calc
    P = ∑ α ∈ P.support.image (residueExponent q), residuePart q P α :=
      (sum_residueParts q P).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro α _
      exact residuePart_eq_monomial_mul_dilate q P α

/-- `lem:exponent-dilation`: dilating all exponents preserves minimum weight. -/
theorem distance_dilate {K : Type*} [Field K] {q : ℕ} (hq : 0 < q)
    (P : MvPolynomial σ K) : distance (dilate q P) = distance P := by
  apply Nat.le_antisymm
  · obtain ⟨H, hH, hmin⟩ := exists_weight_eq_distance P
    have hDH : dilate q H ≠ 0 := fun h => hH ((dilate_eq_zero_iff hq H).mp h)
    have h := distance_le_weight_mul (dilate q P) (dilate q H) hDH
    rwa [← dilate_mul, weight_dilate hq, hmin] at h
  · apply (le_distance_iff _ _).mpr
    intro H hH
    obtain ⟨α, hα⟩ := exists_nonzero_residuePart q H hH
    have hroot : residueRoot q H α ≠ 0 := by
      intro hz
      apply hα
      rw [residuePart_eq_monomial_mul_dilate, hz, dilate_zero, mul_zero]
    calc
      distance P ≤ weight (P * residueRoot q H α) :=
        distance_le_weight_mul P _ hroot
      _ = weight (residuePart q (dilate q P * H) α) :=
        (weight_residuePart_dilate_mul hq P H α).symm
      _ ≤ weight (dilate q P * H) := weight_residuePart_le _ _ _

/-- The same theorem using mathlib's substitution notation. -/
theorem distance_expand {K : Type*} [Field K] {q : ℕ} (hq : 0 < q)
    (P : MvPolynomial σ K) : distance (MvPolynomial.expand q P) = distance P := by
  rw [← dilate_eq_expand, distance_dilate hq]

end WeightedPilz
