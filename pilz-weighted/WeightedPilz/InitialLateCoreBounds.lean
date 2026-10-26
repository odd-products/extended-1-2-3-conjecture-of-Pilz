import WeightedPilz.InitialLateProfiles
import WeightedPilz.InitialLateDecomposition

/-! The actual weighted core-distance bounds at eighteen through twenty-four. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

private theorem late_weights_restrict {n m : ℕ} (hmn : m ≤ n)
    (c : ℕ → K) (hc : NonzeroWeights n c) : NonzeroWeights m c := by
  intro a ha
  obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
  exact hc a (Finset.mem_Icc.mpr ⟨ha1, ham.trans hmn⟩)

private theorem late_weights_scaled {n m t : ℕ} (ht : 0 < t) (htm : t * m ≤ n)
    (c : ℕ → K) (hc : NonzeroWeights n c) : NonzeroWeights m (fun a => c (t * a)) := by
  intro a ha
  obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
  apply hc (t * a)
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos ht ha1, (Nat.mul_le_mul_left t ham).trans htm⟩

theorem initial_two_row_vars (c : ℕ → K) : (interval 2 c).vars ⊆ {2} := by
  rw [initial_interval_2_expansion]
  apply (vars_add_subset _ _).trans
  apply Finset.union_subset
  · simp
  · exact (vars_mul _ _).trans (by simp)

private theorem late_linear_coprime (A : Poly K) (T : Finset ℕ)
    (hAvars : A.vars ⊆ T) (hT : ({2, 3} : Finset ℕ) ⊆ T)
    (p : ℕ) (hp : p ∉ T) (m : ℕ) (hm : m = 3 ∨ m = 4)
    (f : ℕ → K) (hf : NonzeroWeights m f) (D : Poly K) (hD : D ≠ 0)
    (hDvars : D.vars ⊆ {2}) : IsRelPrime (A + interval m f * X p) D := by
  have hp2 : p ≠ 2 := by
    intro he
    apply hp
    simpa only [he] using hT (by simp : 2 ∈ ({2, 3} : Finset ℕ))
  exact linear_core_isRelPrime_of_top p A (interval m f) D hD
    (initial_degree_zero_of_vars_subset hAvars hp)
    (initial_degree_zero_of_vars_subset ((initial_small_row_vars m hm f).trans hT) hp)
    (initial_degree_zero_of_vars_subset hDvars (by simpa using hp2))
    (initial_small_row_isRelPrime_x_only m hm f hf D hD hDvars)

private theorem late_first_profile (b m n : ℕ) (hb : b = 18 ∨ b = 24)
    (hm : m = 3 ∨ m = 4) (hbn : b ≤ n) (h5m : 5 * m ≤ n)
    (c : ℕ → K) (hc : NonzeroWeights n c) :
    InitialCoreProfile (lateBase b c + interval m (fun a => c (5 * a)) * X 5)
      (insert 5 {2, 3}) (5 + m) (7 + m) (min (7 + m) 10) := by
  have hbase := lateBase_profile b hb c (late_weights_restrict hbn c hc)
  simpa only [Nat.reduceAdd] using hbase.linear_extend (by decide) (by intro a ha; exact ha)
    5 (by decide) m hm (fun a => c (5 * a)) (late_weights_scaled (by decide) h5m c hc)

private theorem late_second_profile (b n : ℕ) (hb : b = 18 ∨ b = 24)
    (hbn : b ≤ n) (hn : 21 ≤ n) (c : ℕ → K) (hc : NonzeroWeights n c) :
    InitialCoreProfile
      (lateBase b c + interval 4 (fun a => c (5 * a)) * X 5 +
        interval 3 (fun a => c (7 * a)) * X 7)
      (insert 7 (insert 5 {2, 3})) 12 14 14 := by
  have hfirst : InitialCoreProfile
      (lateBase b c + interval 4 (fun a => c (5 * a)) * X 5)
      (insert 5 {2, 3}) 9 11 10 :=
    late_first_profile b 4 n hb (by omega) hbn (by omega) c hc
  simpa only [Nat.reduceAdd, min_self] using hfirst.linear_extend (by decide)
    (by simp) 7 (by decide) 3 (by omega) (fun a => c (7 * a))
    (late_weights_scaled (by decide) (by omega) c hc)

theorem intervalCore_18_distance_lower (c : ℕ → K) (hc : NonzeroWeights 18 c) :
    11 ≤ distance (intervalCore 18 c) := by
  have hbase := lateBase_profile 18 (by omega) c hc
  have hfirst : InitialCoreProfile
      (lateBase 18 c + interval 3 (fun a => c (5 * a)) * X 5)
      (insert 5 {2, 3}) 8 10 10 :=
    late_first_profile 18 3 18 (by omega) (by omega) (by omega) (by omega) c hc
  let D := interval 2 (fun a => c (7 * a))
  have hDweights : NonzeroWeights 2 (fun a => c (7 * a)) :=
    late_weights_scaled (by decide) (by omega) c hc
  have hD : D ≠ 0 := interval_ne_zero _ (by decide) hDweights
  have hDvars : D.vars ⊆ {2} := initial_two_row_vars _
  have hDweight : 2 ≤ weight D := by rw [weight_interval 2 _ hDweights]
  have hcop := late_linear_coprime (lateBase 18 c) {2, 3} hbase.vars_subset (by intro a ha; exact ha)
    5 (by decide) 3 (by omega) (fun a => c (5 * a))
    (late_weights_scaled (by decide) (by omega) c hc) D hD hDvars
  rw [intervalCore_18_late_decomposition]
  exact hfirst.binomial_extend (by decide) (by decide) 7 (by decide) (by decide)
    D hDvars hDweight hcop

theorem intervalCore_20_distance_lower (c : ℕ → K) (hc : NonzeroWeights 20 c) :
    12 ≤ distance (intervalCore 20 c) := by
  have hbase := lateBase_profile 18 (by omega) c (late_weights_restrict (by omega) c hc)
  have hfirst : InitialCoreProfile
      (lateBase 18 c + interval 4 (fun a => c (5 * a)) * X 5)
      (insert 5 {2, 3}) 9 11 10 :=
    late_first_profile 18 4 20 (by omega) (by omega) (by omega) (by omega) c hc
  let D := interval 2 (fun a => c (7 * a))
  have hDweights : NonzeroWeights 2 (fun a => c (7 * a)) :=
    late_weights_scaled (by decide) (by omega) c hc
  have hD : D ≠ 0 := interval_ne_zero _ (by decide) hDweights
  have hDvars : D.vars ⊆ {2} := initial_two_row_vars _
  have hDweight : 2 ≤ weight D := by rw [weight_interval 2 _ hDweights]
  have hcop := late_linear_coprime (lateBase 18 c) {2, 3} hbase.vars_subset (by intro a ha; exact ha)
    5 (by decide) 4 (by omega) (fun a => c (5 * a))
    (late_weights_scaled (by decide) (by omega) c hc) D hD hDvars
  rw [intervalCore_20_late_decomposition]
  exact hfirst.binomial_extend (by decide) (by decide) 7 (by decide) (by decide)
    D hDvars hDweight hcop

theorem intervalCore_21_distance_lower (c : ℕ → K) (hc : NonzeroWeights 21 c) :
    12 ≤ distance (intervalCore 21 c) := by
  rw [intervalCore_21_late_decomposition]
  exact (late_second_profile 18 21 (by omega) (by omega) (by omega) c hc).distance_lower

theorem intervalCore_22_distance_lower (c : ℕ → K) (hc : NonzeroWeights 22 c) :
    15 ≤ distance (intervalCore 22 c) := by
  have hfirst := late_first_profile 18 4 22 (by omega) (by omega) (by omega) (by omega) c hc
  have hsecond := late_second_profile 18 22 (by omega) (by omega) (by omega) c hc
  let D := interval 2 (fun a => c (11 * a))
  have hDweights : NonzeroWeights 2 (fun a => c (11 * a)) :=
    late_weights_scaled (by decide) (by omega) c hc
  have hD : D ≠ 0 := interval_ne_zero _ (by decide) hDweights
  have hDvars : D.vars ⊆ {2} := initial_two_row_vars _
  have hDweight : 2 ≤ weight D := by rw [weight_interval 2 _ hDweights]
  have hcop := late_linear_coprime _ (insert 5 {2, 3}) hfirst.vars_subset (by simp)
    7 (by decide) 3 (by omega) (fun a => c (7 * a))
    (late_weights_scaled (by decide) (by omega) c hc) D hD hDvars
  rw [intervalCore_22_late_decomposition]
  exact hsecond.binomial_extend (by decide) (by decide) 11 (by decide) (by decide)
    D hDvars hDweight hcop

theorem intervalCore_24_distance_lower (c : ℕ → K) (hc : NonzeroWeights 24 c) :
    15 ≤ distance (intervalCore 24 c) := by
  have hfirst := late_first_profile 24 4 24 (by omega) (by omega) (by omega) (by omega) c hc
  have hsecond := late_second_profile 24 24 (by omega) (by omega) (by omega) c hc
  let D := interval 2 (fun a => c (11 * a))
  have hDweights : NonzeroWeights 2 (fun a => c (11 * a)) :=
    late_weights_scaled (by decide) (by omega) c hc
  have hD : D ≠ 0 := interval_ne_zero _ (by decide) hDweights
  have hDvars : D.vars ⊆ {2} := initial_two_row_vars _
  have hDweight : 2 ≤ weight D := by rw [weight_interval 2 _ hDweights]
  have hcop := late_linear_coprime _ (insert 5 {2, 3}) hfirst.vars_subset (by simp)
    7 (by decide) 3 (by omega) (fun a => c (7 * a))
    (late_weights_scaled (by decide) (by omega) c hc) D hD hDvars
  rw [intervalCore_24_late_decomposition]
  exact hsecond.binomial_extend (by decide) (by decide) 11 (by decide) (by decide)
    D hDvars hDweight hcop

end WeightedPilz
