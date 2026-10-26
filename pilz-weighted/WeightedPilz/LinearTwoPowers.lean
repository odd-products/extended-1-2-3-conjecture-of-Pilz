import WeightedPilz.InitialTenShape
import WeightedPilz.ShiftedPowerRows

/-! Two unequal powers of a linear extension with base monomial coefficients. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K]

theorem polynomial_linear_pow_expChar (R D : MvPolynomial σ K)
    (p e : ℕ) [ExpChar K p] :
    (Polynomial.C R + Polynomial.C D * Polynomial.X) ^ (p ^ e) =
      Polynomial.C (R ^ (p ^ e)) + Polynomial.C (D ^ (p ^ e)) * Polynomial.X ^ (p ^ e) := by
  letI : ExpChar (MvPolynomial σ K) p :=
    expChar_of_injective_ringHom (MvPolynomial.C_injective (σ := σ) (R := K)) p
  letI : ExpChar (Polynomial (MvPolynomial σ K)) p :=
    expChar_of_injective_ringHom Polynomial.C_injective p
  rw [add_pow_expChar_pow, mul_pow, ← map_pow, ← map_pow]

theorem linearExtension_two_base_powers_eight [DecidableEq σ]
    (R D : MvPolynomial σ K) (hR : R ≠ 0) (hD : D ≠ 0)
    (hRd : 4 ≤ distance R) (hDd : 2 ≤ distance D)
    (p : ℕ) [ExpChar K p]
    (hDpower : ∀ k : ℕ, 0 < k → weight (D ^ k) ≤ 2 → ∃ e : ℕ, k = p ^ e)
    (hrows : ∀ G : MvPolynomial (Option σ) K, G ≠ 0 → linearExtension R D ∣ G →
      weight G ≤ 7 → 3 ≤ (optionEquivLeft K σ G).support.card)
    (M N : MvPolynomial σ K) (hM : weight M = 1) (hN : weight N = 1)
    {i j : ℕ} (hi : 0 < i) (hij : i < j) :
    8 ≤ weight (rename some M * linearExtension R D ^ i +
      rename some N * linearExtension R D ^ j) := by
  classical
  let E := linearExtension R D
  let Q : Polynomial (MvPolynomial σ K) := Polynomial.C R + Polynomial.C D * Polynomial.X
  let G := rename some M * E ^ i + rename some N * E ^ j
  let W := optionEquivLeft K σ G
  have hj : 0 < j := by omega
  have hM0 : M ≠ 0 := by intro hz; simp [hz, weight] at hM
  have hN0 : N ≠ 0 := by intro hz; simp [hz, weight] at hN
  have hQdeg : Q.natDegree = 1 := by
    simpa only [Q, add_comm] using Polynomial.natDegree_linear hD (b := R)
  have hQlc : Q.leadingCoeff = D := by
    simpa only [Q, add_comm] using Polynomial.leadingCoeff_linear hD (b := R)
  have hQ0 : Q ≠ 0 := by intro hz; simp [hz] at hQdeg
  have hmap : W = Polynomial.C M * Q ^ i + Polynomial.C N * Q ^ j := by
    simp only [W, G, map_add, map_mul, map_pow, optionEquivLeft_rename_some,
      E, optionEquiv_linearExtension, Q]
  have hconst : W.coeff 0 = M * R ^ i + N * R ^ j := by
    rw [hmap]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, polynomial_coeff_zero_pow]
    simp [Q]
  have hc0 : W.coeff 0 ≠ 0 := by
    rw [hconst]
    exact two_monomial_base_powers_constant_ne_zero R M N hR (by omega) hM hN hij
  have hG : G ≠ 0 := by
    intro hz
    exact hc0 (by simp [W, hz])
  have hWtd : W.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hc0)
  have hpdeg (k : ℕ) : (Q ^ k).natDegree = k := by rw [Polynomial.natDegree_pow, hQdeg, mul_one]
  have htop (k : ℕ) : (Q ^ k).coeff k = D ^ k := by
    simpa only [hQdeg, mul_one, hQlc] using Polynomial.coeff_pow_mul_natDegree Q k
  have hWtop : W.coeff j = N * D ^ j := by
    rw [hmap, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hpdeg]; exact hij), htop]
    simp
  have hWdeg : W.natDegree = j := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [hmap]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · rw [Polynomial.natDegree_C_mul hM0, hpdeg]
        exact hij.le
      · rw [Polynomial.natDegree_C_mul hN0, hpdeg]
    · rw [hWtop]
      exact mul_ne_zero hN0 (pow_ne_zero j hD)
  have hdvd : E ∣ G := by
    apply dvd_add
    · exact dvd_mul_of_dvd_right (dvd_pow_self E (Nat.ne_of_gt hi)) _
    · exact dvd_mul_of_dvd_right (dvd_pow_self E (Nat.ne_of_gt hj)) _
  by_contra hsmall
  have hw : weight G ≤ 7 := by change ¬8 ≤ weight G at hsmall; omega
  obtain ⟨mid, _, _, hs, _, hm, htopw⟩ :=
    linearExtension_small_multiple_shape R D hR hD hRd hDd G hG hdvd (hrows G hG hdvd hw) hw
  change W.support = {W.natTrailingDegree, mid, W.natDegree} at hs
  change weight (W.coeff mid) = 1 at hm
  change weight W.leadingCoeff = 2 at htopw
  rw [hWtd, hWdeg] at hs
  have hDcost : weight (D ^ j) ≤ 2 := by
    have heq : weight W.leadingCoeff = weight (D ^ j) := by
      rw [Polynomial.leadingCoeff, hWdeg, hWtop, mul_comm]
      exact FreshData.weight_mul_of_weight_one _ _ hN
    omega
  obtain ⟨e, he⟩ := hDpower j hj hDcost
  have hcoefj : (Q ^ j).coeff i = 0 := by
    rw [he]
    rw [show Q = Polynomial.C R + Polynomial.C D * Polynomial.X from rfl,
      polynomial_linear_pow_expChar R D p e]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X_pow,
      if_neg (show i ≠ 0 by omega), if_neg (show i ≠ p ^ e by omega),
      if_neg (show p ^ e ≠ i by omega), zero_add]
  have hWi : W.coeff i = M * D ^ i := by
    rw [hmap, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      htop, hcoefj]
    simp
  have hcost : 2 ≤ weight (W.coeff i) := by
    rw [hWi, mul_comm, FreshData.weight_mul_of_weight_one _ _ hM]
    have h := hDd.trans (distance_le_weight_mul D (D ^ (i - 1)) (pow_ne_zero _ hD))
    rwa [← pow_succ', Nat.sub_add_cancel hi] at h
  have him : i ∈ W.support := by
    apply Polynomial.mem_support_iff.mpr
    intro hz
    simp [hz, weight] at hcost
  rw [hs] at him
  simp only [Finset.mem_insert, Finset.mem_singleton] at him
  have himid : i = mid := by rcases him with h | h | h <;> omega
  rw [himid, hm] at hcost
  omega

end WeightedPilz
