import WeightedPilz.InitialLateExtension
import WeightedPilz.Initial

/-! Three- and four-term interval rows used by the later initial cores. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem interval_three_eq (c : ℕ → K) :
    interval 3 c = C (c 1) + C (c 2) * X 2 + C (c 3) * X 3 := by
  have hs : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have h2 := Nat.prime_two.factorization
  have h3 := (by decide : Nat.Prime 3).factorization
  simp [interval, polynomialOf, hs, h2, h3, ← C_apply,
    ← C_mul_X_pow_eq_monomial] <;> ring

theorem interval_four_eq (c : ℕ → K) :
    interval 4 c = C (c 1) + C (c 2) * X 2 + C (c 4) * X 2 ^ 2 + C (c 3) * X 3 := by
  have hs : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have h2 := Nat.prime_two.factorization
  have h3 := (by decide : Nat.Prime 3).factorization
  have h4 : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using Nat.prime_two.factorization_pow (k := 2)
  simp [interval, polynomialOf, hs, h2, h3, h4, ← C_apply,
    ← C_mul_X_pow_eq_monomial] <;> ring

def initialSmallRowBottom (m : ℕ) (c : ℕ → K) : Poly K :=
  C (c 1) + C (c 2) * X 2 + if m = 4 then C (c 4) * X 2 ^ 2 else 0

theorem initial_small_row_expansion (m : ℕ) (hm : m = 3 ∨ m = 4) (c : ℕ → K) :
    interval m c = initialSmallRowBottom m c + C (c 3) * X 3 := by
  rcases hm with rfl | rfl
  · simpa [initialSmallRowBottom] using interval_three_eq c
  · simpa [initialSmallRowBottom] using interval_four_eq c

theorem initial_small_bottom_vars (m : ℕ) (c : ℕ → K) :
    (initialSmallRowBottom m c).vars ⊆ {2} := by
  have hlinear : (C (c 2) * X 2 : Poly K).vars ⊆ {2} :=
    (vars_mul _ _).trans (by simp)
  have hquad : (C (c 4) * X 2 ^ 2 : Poly K).vars ⊆ {2} := by
    apply (vars_mul _ _).trans
    simpa using vars_pow (X (R := K) 2) 2
  unfold initialSmallRowBottom
  apply (vars_add_subset _ _).trans
  apply Finset.union_subset
  · exact (vars_add_subset _ _).trans (by simpa using hlinear)
  · split_ifs <;> simp_all

theorem initial_degree_zero_of_vars_subset {P : Poly K} {T : Finset ℕ}
    (hvars : P.vars ⊆ T) {p : ℕ} (hp : p ∉ T) : P.degreeOf p = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply degreeOf_le_iff.mpr
  intro d hd
  exact Nat.le_of_eq (mem_support_notMem_vars_zero hd (fun h => hp (hvars h)))

theorem initial_small_row_degree_zero (m : ℕ) (hm : m = 3 ∨ m = 4)
    (c : ℕ → K) (p : ℕ) (hp : 3 < p) : (interval m c).degreeOf p = 0 := by
  apply initial_degree_zero_of_vars_subset (T := {2, 3})
  · rw [initial_small_row_expansion m hm c]
    apply (vars_add_subset _ _).trans
    apply Finset.union_subset
    · exact (initial_small_bottom_vars m c).trans (by simp)
    · exact (vars_mul _ _).trans (by simp)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

theorem initial_small_bottom_distance (m : ℕ) (c : ℕ → K)
    (h1 : c 1 ≠ 0) (h2 : c 2 ≠ 0) : 2 ≤ distance (initialSmallRowBottom m c) := by
  apply nonmonomial_distance_two
  have hs0 : (Finsupp.single 2 1 : ℕ →₀ ℕ) ≠ 0 := by
    intro h
    have := congrArg (fun d : ℕ →₀ ℕ => d 2) h
    simpa using this
  have hs2 : (Finsupp.single 2 2 : ℕ →₀ ℕ) ≠ Finsupp.single 2 1 := by
    intro h
    have := congrArg (fun d : ℕ →₀ ℕ => d 2) h
    simpa using this
  have h0 : coeff (0 : ℕ →₀ ℕ) (initialSmallRowBottom m c) = c 1 := by
    by_cases hm : m = 4 <;> simp [initialSmallRowBottom, hm, coeff_C_mul, coeff_X_pow]
  have hx : coeff (Finsupp.single 2 1) (initialSmallRowBottom m c) = c 2 := by
    by_cases hm : m = 4 <;> simp [initialSmallRowBottom, hm, coeff_C_mul, coeff_X_pow,
      hs0, Ne.symm hs0, hs2]
  have hsub : {0, Finsupp.single 2 1} ⊆ (initialSmallRowBottom m c).support := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · apply mem_support_iff.mpr
      rwa [h0]
    · apply mem_support_iff.mpr
      rwa [hx]
  have hh := Finset.card_le_card hsub
  simpa [weight, hs0, Ne.symm hs0] using hh

theorem initial_small_row_distance (m : ℕ) (hm : m = 3 ∨ m = 4)
    (c : ℕ → K) (hc : NonzeroWeights m c) : distance (interval m c) = m :=
  distance_interval_eq_of_le_eight m (by omega) c hc

theorem initial_small_row_power_lower (m : ℕ) (hm : m = 3 ∨ m = 4)
    (c : ℕ → K) (hc : NonzeroWeights m c) (k : ℕ) (hk : 0 < k) :
    m ≤ weight (interval m c ^ k) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hP : interval m c ≠ 0 := interval_ne_zero c (by omega) hc
  have h := distance_le_weight_mul (interval m c) (interval m c ^ l) (pow_ne_zero _ hP)
  rw [initial_small_row_distance m hm c hc] at h
  simpa only [pow_succ'] using h

theorem initial_small_row_power_mul_four (m : ℕ) (hm : m = 3 ∨ m = 4)
    (c : ℕ → K) (hc : NonzeroWeights m c) (M : Poly K) (hM : M ≠ 0)
    (hvars : M.vars ⊆ {2}) (hweight : 2 ≤ weight M) (k : ℕ) (hk : 0 < k) :
    4 ≤ weight (interval m c ^ k * M) := by
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ m) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  let A := initialSmallRowBottom m c
  have hAdist : 2 ≤ distance A := initial_small_bottom_distance m c (hnz 1 (by omega)) (hnz 2 (by omega))
  have hA : A ≠ 0 := by
    intro hz
    simp only [hz, distance_zero] at hAdist
    omega
  have hlow : 2 ≤ weight (A ^ k * M) := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have h := distance_le_weight_mul A (A ^ l * M) (mul_ne_zero (pow_ne_zero _ hA) hM)
    exact hAdist.trans (by simpa only [pow_succ', mul_assoc] using h)
  have htop : weight ((C (c 3) : Poly K) ^ k * M) = weight M := by
    rw [← map_pow]
    exact weight_scalar_monomial_mul 0 (pow_ne_zero _ (hnz 3 (by omega))) M
  have h := linear_core_power_mul_endpoints 3 A (C (c 3)) M
    (C_ne_zero.mpr (hnz 3 (by omega)))
    (initial_degree_zero_of_vars_subset (initial_small_bottom_vars m c) (by simp))
    (degreeOf_C _ _) (initial_degree_zero_of_vars_subset hvars (by simp)) hk
  rw [htop, ← initial_small_row_expansion m hm c] at h
  omega

theorem initial_small_row_isRelPrime_x_only (m : ℕ) (hm : m = 3 ∨ m = 4)
    (c : ℕ → K) (hc : NonzeroWeights m c) (D : Poly K) (hD : D ≠ 0)
    (hvars : D.vars ⊆ {2}) : IsRelPrime (interval m c) D := by
  rw [initial_small_row_expansion m hm c]
  apply linear_core_isRelPrime_of_top 3 _ _ D hD
    (initial_degree_zero_of_vars_subset (initial_small_bottom_vars m c) (by simp))
    (degreeOf_C _ _) (initial_degree_zero_of_vars_subset hvars (by simp))
  have hu : IsUnit (C (c 3) : Poly K) :=
    (isUnit_iff_ne_zero.mpr (hc 3 (Finset.mem_Icc.mpr (by omega)))).map C.toMonoidHom
  intro d hd _
  exact isUnit_of_dvd_unit hd hu

end WeightedPilz
