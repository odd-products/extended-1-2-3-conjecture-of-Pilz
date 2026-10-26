import WeightedPilz.InitialExtraction
import WeightedPilz.RowWeights
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! The distance consequence of the coprime two-row extraction. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K]

theorem weight_product_of_three_option_rows (P H : MvPolynomial (Option σ) K)
    (hspan : (optionEquivLeft K σ P).natTrailingDegree <
      (optionEquivLeft K σ P).natDegree) (hH : H ≠ 0)
    (hrows : 3 ≤ (optionEquivLeft K σ (P * H)).support.card) :
    distance (optionEquivLeft K σ P).trailingCoeff +
      distance (optionEquivLeft K σ P).leadingCoeff + 1 ≤ weight (P * H) := by
  classical
  let E := optionEquivLeft K σ
  let Q := E P
  let V := E H
  let W := E (P * H)
  let lo := Q.natTrailingDegree + V.natTrailingDegree
  let hi := Q.natDegree + V.natDegree
  have hV : V ≠ 0 := by
    intro hz
    exact hH (E.injective (hz.trans (map_zero E).symm))
  have hlow := distance_le_weight_mul Q.trailingCoeff V.trailingCoeff
    (mt Polynomial.trailingCoeff_eq_zero.mp hV)
  have hhigh := distance_le_weight_mul Q.leadingCoeff V.leadingCoeff
    (mt Polynomial.leadingCoeff_eq_zero.mp hV)
  have horder := Polynomial.natTrailingDegree_le_natDegree V
  have hne : lo ≠ hi := by
    change Q.natTrailingDegree < Q.natDegree at hspan
    dsimp [lo, hi]
    omega
  have hcard : ({lo, hi} : Finset ℕ).card < W.support.card := by
    have hpair := Finset.card_le_two (a := lo) (b := hi)
    change 3 ≤ W.support.card at hrows
    omega
  obtain ⟨m, hm, hmout⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hmne : m ≠ lo ∧ m ≠ hi := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hmout
  have hmlo := hmne.1
  have hmhi := hmne.2
  have hmid : 1 ≤ weight (W.coeff m) := Nat.succ_le_iff.mpr (by
    simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using
      Polynomial.mem_support_iff.mp hm)
  have hs := weight_option_slices_le (P * H) {lo, hi, m}
  have hs' : weight (W.coeff lo) + weight (W.coeff hi) + weight (W.coeff m) ≤
      weight (P * H) := by
    simpa only [Finset.sum_insert, Finset.sum_singleton,
      Finset.mem_insert, Finset.mem_singleton, hne, hmlo.symm, hmhi.symm,
      or_self, not_false_eq_true, add_assoc] using hs
  have hmap : W = Q * V := map_mul E P H
  have hl : W.coeff lo = Q.trailingCoeff * V.trailingCoeff := by
    rw [hmap]
    exact Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree
  have hh : W.coeff hi = Q.leadingCoeff * V.leadingCoeff := by
    rw [hmap]
    exact Polynomial.coeff_mul_degree_add_degree Q V
  rw [hl, hh] at hs'
  change distance Q.trailingCoeff + distance Q.leadingCoeff + 1 ≤ weight (P * H)
  omega

section PolynomialAlgebra
variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
open Polynomial

theorem linear_isRelPrime_X (R D : A) (hR : R ≠ 0) :
    IsRelPrime (Polynomial.C R + Polynomial.C D * Polynomial.X) Polynomial.X := by
  have h := (isRelPrime_constant_of_unit_coeff (Polynomial.X : Polynomial A) R hR 1
    (by simp)).symm
  exact h.add_mul_right_left (Polynomial.C D)

theorem coprime_linear_shifted_two_row_extraction (R D U V : A)
    (hR : R ≠ 0) (hD : D ≠ 0) (hV : V ≠ 0) (hcop : IsRelPrime R D)
    (i j : ℕ) (hij : i < j)
    (hdiv : (Polynomial.C R + Polynomial.C D * Polynomial.X) ∣
      (Polynomial.C U * Polynomial.X ^ i + Polynomial.C V * Polynomial.X ^ j)) :
    ∃ M : A, M ≠ 0 ∧ V = D ^ (j - i) * M ∧ U = -((-R) ^ (j - i) * M) := by
  have hfactor : (Polynomial.C U * Polynomial.X ^ i + Polynomial.C V * Polynomial.X ^ j) =
      (Polynomial.C U + Polynomial.C V * Polynomial.X ^ (j - i)) * Polynomial.X ^ i := by
    have hp : (Polynomial.X : Polynomial A) ^ j = Polynomial.X ^ (j - i) * Polynomial.X ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hij.le]
    rw [hp]
    ring
  rw [hfactor] at hdiv
  have hd := (linear_isRelPrime_X R D hR).pow_right.dvd_of_dvd_mul_right hdiv
  exact coprime_linear_factor_two_row_extraction R D U V hD hV hcop (j - i) hd

end PolynomialAlgebra

private theorem weight_signed_power_mul (R M : MvPolynomial σ K) (k : ℕ) :
    weight (-((-R) ^ k * M)) = weight (R ^ k * M) := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_pow]
    simp only [weight, support_neg]
  · rw [hk.neg_pow, neg_mul, neg_neg]

/-- Every nonzero multiple of a linear binomial extension has weight at
least `a + 3` under the power hypothesis of `lem:initial-extraction`.
The set `S` can be a singleton (the manuscript's variable `x`). -/
theorem binomial_extension_distance [DecidableEq σ] (S : Set σ)
    (R D : MvPolynomial σ K) (hR : R ≠ 0)
    (hDvars : (D.vars : Set σ) ⊆ S) (hD : 2 ≤ weight D)
    (hcop : IsRelPrime R D) (a : ℕ) (hbase : a ≤ distance R)
    (hpower : ∀ (k : ℕ), 0 < k → ∀ M : MvPolynomial σ K,
      M ≠ 0 → (M.vars : Set σ) ⊆ S → a < weight (R ^ k * M)) :
    a + 3 ≤ distance ((optionEquivLeft K σ).symm
      (Polynomial.C R + Polynomial.C D * Polynomial.X)) := by
  classical
  let E := optionEquivLeft K σ
  let Q : Polynomial (MvPolynomial σ K) := Polynomial.C R + Polynomial.C D * Polynomial.X
  let P := E.symm Q
  have hEP : E P = Q := E.apply_symm_apply Q
  have hD0 : D ≠ 0 := by intro hz; simp [hz, weight] at hD
  have hQD : Q.natDegree = 1 := by
    simpa only [Q, add_comm] using Polynomial.natDegree_linear hD0 (b := R)
  have hQt : Q.natTrailingDegree = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero.mpr
    right
    simpa [Q] using hR
  have hQtc : Q.trailingCoeff = R := by simp [Polynomial.trailingCoeff, hQt, Q]
  have hQlc : Q.leadingCoeff = D := by
    simpa only [Q, add_comm] using Polynomial.leadingCoeff_linear hD0 (b := R)
  have hQ0 : Q ≠ 0 := by intro hz; simp [hz] at hQD
  have hP0 : P ≠ 0 := by intro hz; apply hQ0; rw [← hEP, hz, map_zero]
  have hspan : (E P).natTrailingDegree < (E P).natDegree := by rw [hEP, hQt, hQD]; decide
  have hDd : 2 ≤ distance D := nonmonomial_distance_two D hD
  apply (le_distance_iff P _).mpr
  intro H hH
  by_contra hsmall
  have hw : weight (P * H) ≤ a + 2 := by omega
  let W := E (P * H)
  have hW0 : W ≠ 0 := by
    intro hz
    exact mul_ne_zero hP0 hH (E.injective (hz.trans (map_zero E).symm))
  have hWdiv : Q ∣ W := by
    refine ⟨E H, ?_⟩
    change E (P * H) = Q * E H
    rw [map_mul, hEP]
  have hrows : W.support.card ≤ 2 := by
    by_contra hn
    have hthree : 3 ≤ W.support.card := by omega
    have hb := weight_product_of_three_option_rows P H hspan hH hthree
    change distance (E P).trailingCoeff + distance (E P).leadingCoeff + 1 ≤ _ at hb
    rw [hEP, hQtc, hQlc] at hb
    omega
  have hc0 : W.support.card ≠ 0 := fun hz => hW0 (Polynomial.card_support_eq_zero.mp hz)
  have hc1 : W.support.card ≠ 1 := by
    intro hone
    obtain ⟨i, U, hU, hrepr⟩ := Polynomial.card_support_eq_one.mp hone
    have hdiv : Q ∣ Polynomial.C U :=
      (linear_isRelPrime_X R D hR).pow_right.dvd_of_dvd_mul_right (hrepr ▸ hWdiv)
    have hz : (Polynomial.C U : Polynomial (MvPolynomial σ K)) = 0 :=
      Polynomial.eq_zero_of_dvd_of_natDegree_lt hdiv (by rw [Polynomial.natDegree_C, hQD]; decide)
    exact hU (Polynomial.C_eq_zero.mp hz)
  have hc2 : W.support.card = 2 := by omega
  obtain ⟨i, j, hij, U, V, hU, hV, hrepr⟩ := Polynomial.card_support_eq_two.mp hc2
  have hcoeffU : W.coeff i = U := by
    rw [hrepr]
    simp [Polynomial.coeff_C_mul_X_pow, hij.ne, hij.ne.symm]
  have hcoeffV : W.coeff j = V := by
    rw [hrepr]
    simp [Polynomial.coeff_C_mul_X_pow, hij.ne, hij.ne.symm]
  have hsum := weight_two_slices (P * H) i j hij.ne
  change weight (W.coeff i) + weight (W.coeff j) ≤ _ at hsum
  rw [hcoeffU, hcoeffV] at hsum
  obtain ⟨M, hM, hVM, hUM⟩ := coprime_linear_shifted_two_row_extraction R D U V
    hR hD0 hV hcop i j hij (hrepr ▸ hWdiv)
  have hk : 0 < j - i := Nat.sub_pos_of_lt hij
  have hbottom : a ≤ weight U := by
    rw [hUM, weight_signed_power_mul]
    obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [hk', pow_succ', mul_assoc]
    exact hbase.trans (distance_le_weight_mul R (R ^ k * M)
      (mul_ne_zero (pow_ne_zero k hR) hM))
  have htop : weight V ≤ 3 := by omega
  obtain ⟨β, M₀, hM₀, hfactor, hM₀vars⟩ := small_power_product_single_base_slice S D M
    hDvars hD hM (j - i) hk (hVM ▸ htop)
  have hstrong : a < weight U := by
    rw [hUM, weight_signed_power_mul, hfactor, mul_left_comm, weight_monomial_mul]
    exact hpower (j - i) hk M₀ hM₀ hM₀vars
  have htoplow : 2 ≤ weight V := by
    rw [hVM]
    obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [hk', pow_succ', mul_assoc]
    exact nonmonomial_weight_mul_two D (D ^ k * M) hD
      (mul_ne_zero (pow_ne_zero k hD0) hM)
  omega

end WeightedPilz
