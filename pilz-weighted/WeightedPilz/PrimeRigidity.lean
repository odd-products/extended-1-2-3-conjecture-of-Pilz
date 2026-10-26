import WeightedPilz.FreshRigidity
import WeightedPilz.Rescale
import WeightedPilz.Basic

/-! Scalar equality at a prime interval index. The predecessor field bound is
an explicit dependency until the complete interval theorem is assembled. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- The strict fresh-coordinate classification is unchanged by an arbitrary
nonzero weight on the fresh variable. -/
theorem sharp_completion_weighted_coordinate_rigidity (p : ℕ) [ExpChar K p]
    (A : MvPolynomial σ K) (z : σ) (a : K) (ha : a ≠ 0) (hA : A ≠ 0)
    (hind : ∀ d ∈ A.support, d z = 0) (hmany : 2 ≤ weight A)
    (hminA : distance A = weight A)
    (G : MvPolynomial σ K) (hG : G ≠ 0) (hdvd : A + C a * X z ∣ G)
    (hw : weight G = weight A + 1) :
    ∃ (e : ℕ) (d : σ →₀ ℕ) (c : K), c ≠ 0 ∧
      G = monomial d c * (A + C a * X z) ^ p ^ e := by
  classical
  let u : σ → Kˣ := fun i ↦ if i = z then (Units.mk0 a ha)⁻¹ else 1
  have hRA : rescale u A = A := by
    ext d
    rw [coeff_rescale]
    by_cases hd : d ∈ A.support
    · have hprod : d.prod (fun i n ↦ (u i : K) ^ n) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hiz : i ≠ z := by
          intro hiz
          subst i
          exact (Finsupp.mem_support_iff.mp hi) (hind d hd)
        simp [u, hiz]
      rw [hprod, mul_one]
    · rw [notMem_support_iff.mp hd, zero_mul]
  have hRP : rescale u (A + C a * X z) = A + X z := by
    rw [map_add, hRA, map_mul, rescale_C, rescale_X]
    simp only [u, if_pos rfl, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  have hRG : rescale u G ≠ 0 := fun hz ↦ hG ((rescale_eq_zero u G).mp hz)
  have hRdvd : A + X z ∣ rescale u G := by
    rw [← hRP]
    exact map_dvd (rescale u) hdvd
  obtain ⟨e, d, c, hc, hform⟩ := sharp_completion_coordinate_rigidity p A z hA
    hind hmany hminA (rescale u G) hRG hRdvd (by simpa using hw)
  let a' := c * d.prod (fun i n ↦ ((u i)⁻¹ : Kˣ).val ^ n)
  have ha' : a' ≠ 0 := mul_ne_zero hc
    (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ pow_ne_zero _ ((u i)⁻¹).ne_zero))
  have hback : rescale (fun i ↦ (u i)⁻¹) (A + X z) = A + C a * X z := by
    rw [← hRP, rescale_inv_rescale]
  refine ⟨e, d, a', ha', ?_⟩
  calc
    G = rescale (fun i ↦ (u i)⁻¹) (rescale u G) := (rescale_inv_rescale u G).symm
    _ = monomial d a' * (A + C a * X z) ^ p ^ e := by
      rw [hform, map_mul, map_pow, rescale_monomial, hback]

theorem prime_index_predecessor_independent (ℓ : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights (ℓ - 1) c) :
    ∀ d ∈ (interval (ℓ - 1) c).support, d ℓ = 0 := by
  intro d hd
  rw [support_interval _ _ hc] at hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hdiv
  have hapos : 0 < a := (Finset.mem_Icc.mp ha).1
  have hle := Nat.le_of_dvd hapos hdiv
  have haupper := (Finset.mem_Icc.mp ha).2
  omega

theorem interval_prime_eq_predecessor (ℓ : ℕ) (hℓ : ℓ.Prime) (c : ℕ → K) :
    interval ℓ c = interval (ℓ - 1) c + C (c ℓ) * X ℓ := by
  have heq : ℓ - 1 + 1 = ℓ := by have := hℓ.two_le; omega
  have h := interval_succ (ℓ - 1) c
  rw [heq, hℓ.factorization] at h
  simpa only [X, C_mul_monomial, mul_one] using h

/-- Polynomial scalar prime-index equality, with exactly the predecessor
instance of the field theorem exposed as a dependency. -/
theorem prime_index_rigidity_of_predecessor_bound (p ℓ : ℕ) [ExpChar K p]
    (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ) (c : ℕ → K)
    (hc : NonzeroWeights ℓ c) (hfield : IntervalBound (ℓ - 1) c)
    (G : Poly K) (hG : G ≠ 0) (hdvd : interval ℓ c ∣ G) (hw : weight G = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℕ) (a : K), a ≠ 0 ∧
      G = monomial d a * interval ℓ c ^ p ^ e := by
  classical
  have hcprev : NonzeroWeights (ℓ - 1) c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
      (Finset.mem_Icc.mp ha).2.trans (Nat.sub_le _ _)⟩)
  have hpredpos : 0 < ℓ - 1 := by omega
  have hA : interval (ℓ - 1) c ≠ 0 := interval_ne_zero c hpredpos hcprev
  have hminA : distance (interval (ℓ - 1) c) = weight (interval (ℓ - 1) c) := by
    apply le_antisymm (distance_le_weight _)
    rw [weight_interval _ _ hcprev]
    exact (le_distance_iff _ _).mpr hfield
  have hcℓ : c ℓ ≠ 0 := hc ℓ (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  rw [interval_prime_eq_predecessor ℓ hℓ c] at hdvd ⊢
  apply sharp_completion_weighted_coordinate_rigidity p _ ℓ (c ℓ) hcℓ hA
    (prime_index_predecessor_independent ℓ c hcprev)
    (by rw [weight_interval _ _ hcprev]; omega) hminA G hG hdvd
  rw [weight_interval _ _ hcprev, hw]
  omega

/-- The cofactor has the matching exponent one lower, with the same scalar
monomial as the output. -/
theorem prime_index_multiplier_rigidity_of_predecessor_bound (p ℓ : ℕ) [ExpChar K p]
    (hℓ : ℓ.Prime) (hthree : 3 ≤ ℓ) (c : ℕ → K)
    (hc : NonzeroWeights ℓ c) (hfield : IntervalBound (ℓ - 1) c)
    (H : Poly K) (hH : H ≠ 0) (hw : weight (interval ℓ c * H) = ℓ) :
    ∃ (e : ℕ) (d : ℕ →₀ ℕ) (a : K), a ≠ 0 ∧
      interval ℓ c * H = monomial d a * interval ℓ c ^ p ^ e ∧
      H = monomial d a * interval ℓ c ^ (p ^ e - 1) := by
  have hP : interval ℓ c ≠ 0 := interval_ne_zero c (by omega) hc
  obtain ⟨e, d, a, ha, hform⟩ := prime_index_rigidity_of_predecessor_bound p ℓ hℓ
    hthree c hc hfield _ (mul_ne_zero hP hH) (dvd_mul_right _ _) hw
  refine ⟨e, d, a, ha, hform, ?_⟩
  apply mul_left_cancel₀ hP
  rw [hform]
  have hpow : p ^ e = (p ^ e - 1) + 1 := by
    have := expChar_pow_pos K p e
    omega
  conv_lhs => rw [hpow]
  rw [pow_succ]
  ring

end WeightedPilz
