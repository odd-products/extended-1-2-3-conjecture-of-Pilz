import WeightedPilz.CoreSixteen
import WeightedPilz.InitialLateProfiles
import WeightedPilz.AffineNondistinguished

/-! The common distance and power estimates for cores fifteen and sixteen. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem baseTwelve_profile (c : ℕ → K) (hc : NonzeroWeights 12 c) :
    InitialCoreProfile (baseTwelve c) {2, 3} 4 7 6 := by
  refine ⟨baseTwelve_distance_four c hc, fun k hk => baseTwelve_power_seven c hc hk, ?_, ?_⟩
  · intro k hk M hM hvars
    exact baseTwelve_power_mul_six c hc M hM (by intro z hz; simpa using hvars hz) hk
  · intro z hz
    unfold baseTwelve at hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hz)
    cases i <;> simp [coreNineVariables]

theorem baseSixteen_profile (c : ℕ → K) (hc : NonzeroWeights 16 c) :
    InitialCoreProfile (baseSixteen c) {2, 3} 4 7 6 := by
  refine ⟨baseSixteen_distance_four c hc, fun k hk => baseSixteen_power_seven c hc hk, ?_, ?_⟩
  · intro k hk M hM hvars
    exact baseSixteen_power_mul_six c hc M hM (by intro z hz; simpa using hvars hz) hk
  · intro z hz
    rw [baseSixteen_rename] at hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hz)
    cases i <;> simp [coreNineVariables]

theorem arithmeticFiveRow_eq_interval (c : ℕ → K) :
    arithmeticFiveRow c = interval 3 (fun a => c (5 * a)) := by
  rw [interval_three_eq]
  simp [arithmeticFiveRow]

theorem arithmeticBinomial_vars (p : ℕ) (c : ℕ → K) :
    (arithmeticBinomial p c).vars ⊆ {2} := by
  apply (vars_add_subset _ _).trans
  apply Finset.union_subset
  · simp
  · exact (vars_mul _ _).trans (by simp)

theorem arithmeticBinomial_distance_two (p : ℕ) (c : ℕ → K)
    (hp : c p ≠ 0) (hp2 : c (2 * p) ≠ 0) :
    2 ≤ distance (arithmeticBinomial p c) := by
  have h := initial_small_bottom_distance 3 (fun a => c (p * a))
    (by simpa using hp) (by simpa only [Nat.mul_comm] using hp2)
  simpa [initialSmallRowBottom, arithmeticBinomial, Nat.mul_comm] using h

theorem nonzeroWeights_five_row (c : ℕ → K) (hc : NonzeroWeights 15 c) :
    NonzeroWeights 3 (fun a => c (5 * a)) := by
  intro a ha
  apply hc
  have h := Finset.mem_Icc.mp ha
  exact Finset.mem_Icc.mpr (by omega)

theorem affine_binomial_core_distance_ten (A : Poly K)
    (hA : InitialCoreProfile A {2, 3} 4 7 6)
    (c : ℕ → K) (hc : NonzeroWeights 15 c) :
    10 ≤ distance ((A + arithmeticFiveRow c * X 5) + arithmeticBinomial 7 c * X 7) := by
  let D := arithmeticBinomial 7 c
  let L := interval 3 (fun a => c (5 * a))
  have hLcoeff := nonzeroWeights_five_row c hc
  have hDdist : 2 ≤ distance D := arithmeticBinomial_distance_two 7 c
    (hc 7 (by decide)) (hc 14 (by decide))
  have hD : D ≠ 0 := by intro hz; simp [hz, distance_zero] at hDdist
  have hDvars : D.vars ⊆ {2} := arithmeticBinomial_vars 7 c
  have hDweight := hDdist.trans (distance_le_weight D)
  have hF : InitialCoreProfile (A + L * X 5) {5, 2, 3} 7 10 10 := by
    simpa using
      hA.linear_extend (by decide) (by simp) 5 (by simp) 3 (Or.inl rfl) _ hLcoeff
  have hcopLD : IsRelPrime L D :=
    initial_small_row_isRelPrime_x_only 3 (Or.inl rfl) _ hLcoeff D hD hDvars
  have hcop : IsRelPrime (A + L * X 5) D :=
    linear_core_isRelPrime_of_top 5 A L D hD
      (initial_degree_zero_of_vars_subset hA.vars_subset (by simp))
      (initial_small_row_degree_zero 3 (Or.inl rfl) _ 5 (by decide))
      (initial_degree_zero_of_vars_subset hDvars (by simp)) hcopLD
  have h := hF.binomial_extend (by decide) (by decide) 7 (by simp) (by decide)
    D hDvars hDweight hcop
  rw [arithmeticFiveRow_eq_interval]
  exact h

theorem affine_binomial_core_nondistinguished_power_sixteen (A : Poly K)
    (hA : InitialCoreProfile A {2, 3} 4 7 6)
    (c : ℕ → K) (hc : NonzeroWeights 15 c) (p : ℕ) [ExpChar K p]
    {n : ℕ} (hn : 0 < n) (hnd : ∀ e : ℕ, n ≠ p ^ e) :
    16 ≤ weight (((A + arithmeticFiveRow c * X 5) + arithmeticBinomial 7 c * X 7) ^ n) := by
  let D := arithmeticBinomial 7 c
  let L := interval 3 (fun a => c (5 * a))
  have hLcoeff := nonzeroWeights_five_row c hc
  have hL : L ≠ 0 := interval_ne_zero _ (by decide) hLcoeff
  have hDdist : 2 ≤ distance D := arithmeticBinomial_distance_two 7 c
    (hc 7 (by decide)) (hc 14 (by decide))
  have hD : D ≠ 0 := by intro hz; simp [hz, distance_zero] at hDdist
  have hDvars : D.vars ⊆ {2} := arithmeticBinomial_vars 7 c
  have hLpower : 6 ≤ weight (L ^ n) :=
    interval_three_nondistinguished_power_six _ hLcoeff p hn hnd
  have hDpower : 3 ≤ weight (D ^ n) :=
    (Nat.add_le_add_right hDdist 1).trans
      (power_gap p D (hDdist.trans (distance_le_weight D)) hn hnd)
  have hFpower : 13 ≤ weight ((A + L * X 5) ^ n) := by
    have h := linear_core_power_endpoints 5 A L hL
      (initial_degree_zero_of_vars_subset hA.vars_subset (by simp))
      (initial_small_row_degree_zero 3 (Or.inl rfl) _ 5 (by decide)) hn
    have hb := hA.power_lower n hn
    omega
  have hFvars : (A + L * X 5).vars ⊆ {5, 2, 3} := by
    apply (vars_add_subset _ _).trans
    apply Finset.union_subset
    · exact hA.vars_subset.trans (by simp)
    · apply (vars_mul _ _).trans
      apply Finset.union_subset
      · exact (initial_small_row_vars 3 (Or.inl rfl) _).trans (by simp)
      · simp
  have h := linear_core_power_endpoints 7 (A + L * X 5) D hD
    (initial_degree_zero_of_vars_subset hFvars (by simp))
    (initial_degree_zero_of_vars_subset hDvars (by simp)) hn
  rw [arithmeticFiveRow_eq_interval]
  change 16 ≤ weight (((A + L * X 5) + D * X 7) ^ n)
  omega

theorem intervalCore_fifteen_distance_ten (c : ℕ → K) (hc : NonzeroWeights 15 c) :
    10 ≤ distance (intervalCore 15 c) := by
  have hc12 : NonzeroWeights 12 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by
      have := (Finset.mem_Icc.mp ha).2
      omega⟩)
  rw [intervalCore_fifteen_decomposition]
  exact affine_binomial_core_distance_ten _ (baseTwelve_profile c hc12) c hc

theorem intervalCore_sixteen_distance_ten (c : ℕ → K) (hc : NonzeroWeights 16 c) :
    10 ≤ distance (intervalCore 16 c) := by
  have hc15 : NonzeroWeights 15 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by
      have := (Finset.mem_Icc.mp ha).2
      omega⟩)
  rw [intervalCore_sixteen_decomposition]
  exact affine_binomial_core_distance_ten _ (baseSixteen_profile c hc) c hc15

theorem intervalCore_fifteen_nondistinguished_power_sixteen (c : ℕ → K)
    (hc : NonzeroWeights 15 c) (p : ℕ) [ExpChar K p]
    {n : ℕ} (hn : 0 < n) (hnd : ∀ e : ℕ, n ≠ p ^ e) :
    16 ≤ weight (intervalCore 15 c ^ n) := by
  have hc12 : NonzeroWeights 12 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by
      have := (Finset.mem_Icc.mp ha).2
      omega⟩)
  rw [intervalCore_fifteen_decomposition]
  exact affine_binomial_core_nondistinguished_power_sixteen _ (baseTwelve_profile c hc12) c hc p hn hnd

theorem intervalCore_sixteen_nondistinguished_power_sixteen (c : ℕ → K)
    (hc : NonzeroWeights 16 c) (p : ℕ) [ExpChar K p]
    {n : ℕ} (hn : 0 < n) (hnd : ∀ e : ℕ, n ≠ p ^ e) :
    16 ≤ weight (intervalCore 16 c ^ n) := by
  have hc15 : NonzeroWeights 15 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by
      have := (Finset.mem_Icc.mp ha).2
      omega⟩)
  rw [intervalCore_sixteen_decomposition]
  exact affine_binomial_core_nondistinguished_power_sixteen _ (baseSixteen_profile c hc) c hc15 p hn hnd

end WeightedPilz
