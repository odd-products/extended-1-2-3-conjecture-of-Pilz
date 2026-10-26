import WeightedPilz.InitialLateBases
import WeightedPilz.InitialLateRows
import WeightedPilz.InitialCoreExtension
import WeightedPilz.ShortFreshTest

/-! Simultaneous distance and power bounds for adjoining the initial linear rows. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

structure InitialCoreProfile (P : Poly K) (T : Finset ℕ) (d b a : ℕ) : Prop where
  distance_lower : d ≤ distance P
  power_lower : ∀ k, 0 < k → b ≤ weight (P ^ k)
  power_mul_lower : ∀ k, 0 < k → ∀ M : Poly K, M ≠ 0 → M.vars ⊆ {2} →
    a ≤ weight (P ^ k * M)
  vars_subset : P.vars ⊆ T

theorem lateBase_profile (n : ℕ) (hn : n = 18 ∨ n = 24)
    (c : ℕ → K) (hc : NonzeroWeights n c) :
    InitialCoreProfile (lateBase n c) {2, 3} 5 7 6 := by
  refine ⟨lateBase_distance_five n hn c hc,
    fun k hk => lateBase_power_seven n hn c hc hk, ?_, ?_⟩
  · intro k hk M hM hvars
    exact lateBase_power_mul_six n hn c hc M hM (by
      intro z hz
      simpa only [Finset.mem_singleton, Set.mem_singleton_iff] using hvars hz) hk
  · intro z hz
    unfold lateBase at hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hz)
    cases i <;> simp [coreNineVariables]

theorem initial_small_row_vars (m : ℕ) (hm : m = 3 ∨ m = 4) (c : ℕ → K) :
    (interval m c).vars ⊆ {2, 3} := by
  rw [initial_small_row_expansion m hm c]
  apply (vars_add_subset _ _).trans
  apply Finset.union_subset
  · exact (initial_small_bottom_vars m c).trans (by simp)
  · exact (vars_mul _ _).trans (by simp)

theorem InitialCoreProfile.linear_extend {A : Poly K} {T : Finset ℕ} {d b a : ℕ}
    (hA : InitialCoreProfile A T d b a) (hd : 0 < d)
    (hT : ({2, 3} : Finset ℕ) ⊆ T) (p : ℕ) (hp : p ∉ T)
    (m : ℕ) (hm : m = 3 ∨ m = 4) (c : ℕ → K) (hc : NonzeroWeights m c) :
    InitialCoreProfile (A + interval m c * X p) (insert p T)
      (d + m) (b + m) (min (b + m) (a + 4)) := by
  have hp2 : p ≠ 2 := by
    intro he
    apply hp
    simpa only [he] using hT (by simp : 2 ∈ ({2, 3} : Finset ℕ))
  have hA0 : A ≠ 0 := by
    intro hz
    have h := hA.distance_lower
    rw [hz, distance_zero] at h
    omega
  have hR0 : interval m c ≠ 0 := interval_ne_zero c (by omega) hc
  have hAdegree : A.degreeOf p = 0 := initial_degree_zero_of_vars_subset hA.vars_subset hp
  have hRvars : (interval m c).vars ⊆ T := (initial_small_row_vars m hm c).trans hT
  have hRdegree : (interval m c).degreeOf p = 0 := initial_degree_zero_of_vars_subset hRvars hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := linear_core_distance p A (interval m c) hA0 hR0 hAdegree hRdegree
    rw [initial_small_row_distance m hm c hc] at h
    exact (Nat.add_le_add_right hA.distance_lower m).trans h
  · intro k hk
    have h := linear_core_power_endpoints p A (interval m c) hR0 hAdegree hRdegree hk
    exact (Nat.add_le_add (hA.power_lower k hk)
      (initial_small_row_power_lower m hm c hc k hk)).trans h
  · intro k hk M hM hvars
    have hMdegree : M.degreeOf p = 0 :=
      initial_degree_zero_of_vars_subset hvars (by simpa using hp2)
    have h := linear_core_power_mul_endpoints p A (interval m c) M hR0
      hAdegree hRdegree hMdegree hk
    by_cases hMone : weight M = 1
    · rw [FreshData.weight_mul_of_weight_one _ M hMone,
        FreshData.weight_mul_of_weight_one _ M hMone] at h
      exact (min_le_left _ _).trans ((Nat.add_le_add (hA.power_lower k hk)
        (initial_small_row_power_lower m hm c hc k hk)).trans h)
    · have hMtwo : 2 ≤ weight M := by have := weight_pos hM; omega
      exact (min_le_right _ _).trans ((Nat.add_le_add (hA.power_mul_lower k hk M hM hvars)
        (initial_small_row_power_mul_four m hm c hc M hM hvars hMtwo k hk)).trans h)
  · apply (vars_add_subset _ _).trans
    apply Finset.union_subset
    · exact hA.vars_subset.trans (Finset.subset_insert _ _)
    · apply (vars_mul _ _).trans
      apply Finset.union_subset
      · exact hRvars.trans (Finset.subset_insert _ _)
      · simp

theorem InitialCoreProfile.binomial_extend {A : Poly K} {T : Finset ℕ} {d b a : ℕ}
    (hA : InitialCoreProfile A T d b a) (hd : 0 < d) (hda : d < a)
    (p : ℕ) (hp : p ∉ T) (hp2 : p ≠ 2) (D : Poly K)
    (hDvars : D.vars ⊆ {2}) (hDweight : 2 ≤ weight D) (hcop : IsRelPrime A D) :
    d + 3 ≤ distance (A + D * X p) := by
  have hA0 : A ≠ 0 := by
    intro hz
    have h := hA.distance_lower
    rw [hz, distance_zero] at h
    omega
  apply binomial_core_extension_distance p {2} A D hA0
    (initial_degree_zero_of_vars_subset hA.vars_subset hp)
    (initial_degree_zero_of_vars_subset hDvars (by simpa using hp2))
    (by intro z hz; simpa only [Finset.mem_singleton, Set.mem_singleton_iff] using hDvars hz)
    hDweight hcop d hA.distance_lower
  intro k hk M hM hvars
  exact hda.trans_le (hA.power_mul_lower k hk M hM (by
    intro z hz
    simpa only [Finset.mem_singleton, Set.mem_singleton_iff] using hvars hz))

end WeightedPilz
