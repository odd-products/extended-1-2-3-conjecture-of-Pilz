import WeightedPilz.LinearExtensionOps
import WeightedPilz.PolynomialPowerRows
import WeightedPilz.UnivariateWeight
import WeightedPilz.CoreNine
import WeightedPilz.LinearPowerThreeRows

/-! A nondistinguished power of a nondegenerate affine triangle has six terms. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem weight_pow_bound_of_nondistinguished_reduced {σ : Type*}
    (P : MvPolynomial σ K) (b p : ℕ) [hpK : ExpChar K p]
    (hbound : ∀ n : ℕ, 2 ≤ n → (n : K) ≠ 0 → b ≤ weight (P ^ n))
    {n : ℕ} (hn : 0 < n) (hnd : ∀ e : ℕ, n ≠ p ^ e) : b ≤ weight (P ^ n) := by
  cases hpK with
  | zero =>
    have hn1 : n ≠ 1 := by simpa using hnd 0
    exact hbound n (by omega) (Nat.cast_ne_zero.mpr (ne_of_gt hn))
  | prime hp =>
    letI : ExpChar K p := ExpChar.prime hp
    obtain ⟨e, h, hnp, hfactor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hn) p hp.ne_one
    have hh : 2 ≤ h := by
      by_contra hsmall
      interval_cases h
      · simp at hfactor
        omega
      · exact hnd e (by simpa using hfactor)
    have hhK : (h : K) ≠ 0 := fun hz => hnp ((CharP.cast_eq_zero_iff K p h).mp hz)
    rw [hfactor, Nat.mul_comm, pow_mul, weight_pow_expChar]
    exact hbound h hh hhK

theorem polynomial_reduced_power_three_of_positive_degree (P : Polynomial K)
    (h0 : P.coeff 0 ≠ 0) (h1 : P.coeff 1 ≠ 0) (hdeg : 1 ≤ P.natDegree)
    {n : ℕ} (hn : 2 ≤ n) (hnK : (n : K) ≠ 0) : 3 ≤ (P ^ n).support.card := by
  classical
  have hP : P ≠ 0 := fun hz => h0 (by rw [hz, Polynomial.coeff_zero])
  have ht : 2 ≤ n * P.natDegree := by simpa using Nat.mul_le_mul hn hdeg
  have hc0 : (P ^ n).coeff 0 ≠ 0 := by
    rw [polynomial_coeff_zero_pow]
    exact pow_ne_zero _ h0
  have hc1 : (P ^ n).coeff 1 ≠ 0 := by
    rw [polynomial_coeff_one_pow]
    exact mul_ne_zero (mul_ne_zero hnK h1) (pow_ne_zero _ h0)
  have hct : (P ^ n).coeff (n * P.natDegree) ≠ 0 := by
    rw [Polynomial.coeff_pow_mul_natDegree]
    exact pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hP)
  have hs : ({0, 1, n * P.natDegree} : Finset ℕ) ⊆ (P ^ n).support := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact Polynomial.mem_support_iff.mpr hc0
    · exact Polynomial.mem_support_iff.mpr hc1
    · exact Polynomial.mem_support_iff.mpr hct
  have hcard : ({0, 1, n * P.natDegree} : Finset ℕ).card = 3 := by
    simp [show 0 ≠ n * P.natDegree by omega, show 1 ≠ n * P.natDegree by omega]
  rw [← hcard]
  exact Finset.card_le_card hs

def affineTriangle (a b c : K) : MvPolynomial (Option PUnit.{1}) K :=
  linearExtension ((pUnitAlgEquiv.{_, 0} K).symm
    (Polynomial.C a + Polynomial.C b * Polynomial.X)) (C c)

theorem affineTriangle_power_six_reduced (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) (hnK : (n : K) ≠ 0) :
    6 ≤ weight (affineTriangle a b c ^ n) := by
  let U := pUnitAlgEquiv.{_, 0} K
  let A : Polynomial K := Polynomial.C a + Polynomial.C b * Polynomial.X
  let R := U.symm A
  have hA0 : A.coeff 0 ≠ 0 := by simpa [A] using ha
  have hA1 : A.coeff 1 ≠ 0 := by simpa [A] using hb
  have hdeg : A.natDegree = 1 := by
    simpa only [A, add_comm] using Polynomial.natDegree_linear hb (b := a)
  have hlo : 3 ≤ weight (R ^ n) := by
    rw [← map_pow, weight_pUnitAlgEquiv_symm]
    exact polynomial_reduced_power_three_of_positive_degree A hA0 hA1 (by omega) hn hnK
  have hmid : 2 ≤ weight ((n : MvPolynomial PUnit.{1} K) * R * C c ^ (n - 1)) := by
    have heq : (n : MvPolynomial PUnit.{1} K) * R * C c ^ (n - 1) =
        C ((n : K) * c ^ (n - 1)) * R := by
      rw [map_mul, map_pow]
      simp only [map_natCast]
      ring
    rw [heq, C_apply, weight_scalar_monomial_mul 0 (mul_ne_zero hnK (pow_ne_zero _ hc))]
    exact (distance_pUnit_symm_two A hA0 hA1).trans (distance_le_weight _)
  have hD : (C c : MvPolynomial PUnit.{1} K) ≠ 0 := C_ne_zero.mpr hc
  have hhi : 1 ≤ weight ((C c : MvPolynomial PUnit.{1} K) ^ n) := by
    have hne := pow_ne_zero n hD
    exact Nat.succ_le_iff.mpr (by
      simpa [weight, Finset.card_pos, MvPolynomial.support_nonempty] using hne)
  have hsum := linearExtension_power_three_rows R (C c) hD hn
  change 6 ≤ weight (linearExtension R (C c) ^ n)
  omega

theorem affineTriangle_nondistinguished_power_six (a b c : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (p : ℕ) [ExpChar K p]
    {n : ℕ} (hn : 0 < n) (hnd : ∀ e : ℕ, n ≠ p ^ e) :
    6 ≤ weight (affineTriangle a b c ^ n) :=
  weight_pow_bound_of_nondistinguished_reduced _ 6 p
    (fun n hn hnK => affineTriangle_power_six_reduced a b c ha hb hc hn hnK) hn hnd

theorem interval_three_nondistinguished_power_six (c : ℕ → K) (hc : NonzeroWeights 3 c)
    (p : ℕ) [ExpChar K p] {n : ℕ} (hn : 0 < n) (hnd : ∀ e : ℕ, n ≠ p ^ e) :
    6 ≤ weight (interval 3 c ^ n) := by
  have heq : interval 3 c = rename coreNineVariables (affineTriangle (c 1) (c 2) (c 3)) := by
    have hset : Finset.Icc 1 3 = {1, 2, 3} := by decide
    have h2 : (2 : ℕ).factorization = Finsupp.single 2 1 := Nat.prime_two.factorization
    have h3 : (3 : ℕ).factorization = Finsupp.single 3 1 :=
      (by decide : Nat.Prime 3).factorization
    simp [interval, polynomialOf, hset, h2, h3, affineTriangle, linearExtension,
      pUnitAlgEquiv_symm_apply, coreNineVariables,
      ← C_apply, ← C_mul_X_pow_eq_monomial] <;> ring
  rw [heq, ← map_pow, weight_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact affineTriangle_nondistinguished_power_six _ _ _
    (hc 1 (by decide)) (hc 2 (by decide)) (hc 3 (by decide)) p hn hnd

end WeightedPilz
