import WeightedPilz.CoreNine
import WeightedPilz.BivariatePower
import WeightedPilz.BivariatePowerMultiplier

/-! The two quadratic bases used in the initial intervals eighteen to twenty-four. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def lateBaseBottom (c : ℕ → K) : Polynomial K :=
  coreNineBottom c + Polynomial.C (c 16) * Polynomial.X ^ 4

def lateBaseMiddle (n : ℕ) (c : ℕ → K) : Polynomial K :=
  Polynomial.C (c 3) + Polynomial.C (c 6) * Polynomial.X +
    Polynomial.C (c 12) * Polynomial.X ^ 2 +
    if n = 24 then Polynomial.C (c 24) * Polynomial.X ^ 3 else 0

def lateBaseTop (c : ℕ → K) : Polynomial K :=
  Polynomial.C (c 9) + Polynomial.C (c 18) * Polynomial.X

def lateBase (n : ℕ) (c : ℕ → K) : Poly K :=
  rename coreNineVariables
    (bivariateQuadratic (lateBaseBottom c) (lateBaseMiddle n c) (lateBaseTop c))

theorem lateBase_expansion (n : ℕ) (c : ℕ → K) :
    lateBase n c =
      C (c 1) + C (c 2) * X 2 + C (c 4) * X 2 ^ 2 + C (c 8) * X 2 ^ 3 +
      C (c 16) * X 2 ^ 4 +
      (C (c 3) + C (c 6) * X 2 + C (c 12) * X 2 ^ 2 +
        if n = 24 then C (c 24) * X 2 ^ 3 else 0) * X 3 +
      (C (c 9) + C (c 18) * X 2) * X 3 ^ 2 := by
  have h : bivariateQuadratic (lateBaseBottom c) (lateBaseMiddle n c) (lateBaseTop c) =
      C (c 1) + C (c 2) * X (some ()) + C (c 4) * X (some ()) ^ 2 +
      C (c 8) * X (some ()) ^ 3 + C (c 16) * X (some ()) ^ 4 +
      (C (c 3) + C (c 6) * X (some ()) + C (c 12) * X (some ()) ^ 2 +
        if n = 24 then C (c 24) * X (some ()) ^ 3 else 0) * X none +
      (C (c 9) + C (c 18) * X (some ())) * X none ^ 2 := by
    apply (optionEquivLeft K PUnit).injective
    by_cases hn : n = 24 <;>
      simp [bivariateQuadratic, lateBaseBottom, coreNineBottom, lateBaseMiddle,
        lateBaseTop, hn, pUnitAlgEquiv_symm_apply, optionEquivLeft_C,
        optionEquivLeft_X_some, optionEquivLeft_X_none]
  rw [lateBase, h]
  by_cases hn : n = 24 <;> simp [coreNineVariables, hn]

theorem lateBaseBottom_natDegree (c : ℕ → K) (hc : c 16 ≠ 0) :
    (lateBaseBottom c).natDegree = 4 := by
  dsimp [lateBaseBottom, coreNineBottom]
  compute_degree <;> first | exact hc | decide

theorem lateBase_distance_five (n : ℕ) (hn : n = 18 ∨ n = 24)
    (c : ℕ → K) (hc : NonzeroWeights n c) : 5 ≤ distance (lateBase n c) := by
  have hn18 : 18 ≤ n := by omega
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ n) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hB : lateBaseMiddle n c ≠ 0 := by
    intro hz
    have h0 := congrArg (fun P : Polynomial K => P.coeff 0) hz
    apply hnz 3 (by omega)
    rcases hn with rfl | rfl <;> simpa [lateBaseMiddle] using h0
  have hAdeg := lateBaseBottom_natDegree c (hnz 16 (by omega))
  have hDdeg : (lateBaseTop c).natDegree = 1 := by
    dsimp [lateBaseTop]
    compute_degree <;> first | exact hnz 18 (by omega) | decide
  have hBdeg : (lateBaseMiddle n c).natDegree = if n = 24 then 3 else 2 := by
    rcases hn with rfl | rfl <;> simp only [lateBaseMiddle, reduceIte, add_zero] <;>
      compute_degree <;> first | exact hnz 12 (by omega) | exact hnz 24 (by omega) | decide
  have h := bivariateQuadratic_distance_five
    (lateBaseBottom c) (lateBaseMiddle n c) (lateBaseTop c)
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 1 (by omega))
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 2 (by omega)) hB
    (by simpa [lateBaseTop] using hnz 9 (by omega))
    (by simpa [lateBaseTop] using hnz 18 (by omega)) (by
      rw [hAdeg, hDdeg, hBdeg]
      split_ifs <;> decide)
  rw [lateBase, distance_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

theorem lateBase_power_seven (n : ℕ) (hn : n = 18 ∨ n = 24)
    (c : ℕ → K) (hc : NonzeroWeights n c) {k : ℕ} (hk : 0 < k) :
    7 ≤ weight (lateBase n c ^ k) := by
  have hn18 : 18 ≤ n := by omega
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ n) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  have hB0 : (lateBaseMiddle n c).coeff 0 ≠ 0 := by
    rcases hn with rfl | rfl <;> simpa [lateBaseMiddle] using hnz 3 (by omega)
  have hB1 : (lateBaseMiddle n c).coeff 1 ≠ 0 := by
    rcases hn with rfl | rfl <;> simpa [lateBaseMiddle] using hnz 6 (by omega)
  have h := bivariateQuadratic_power_seven
    (lateBaseBottom c) (lateBaseMiddle n c) (lateBaseTop c)
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 1 (by omega))
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 2 (by omega))
    (by rw [lateBaseBottom_natDegree c (hnz 16 (by omega))]; decide) hB0 hB1
    (by simpa [lateBaseTop] using hnz 9 (by omega))
    (by simpa [lateBaseTop] using hnz 18 (by omega)) hk
  rw [lateBase, ← map_pow,
    weight_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

theorem lateBase_power_mul_six (n : ℕ) (hn : n = 18 ∨ n = 24)
    (c : ℕ → K) (hc : NonzeroWeights n c) (M : Poly K) (hM : M ≠ 0)
    (hvars : (M.vars : Set ℕ) ⊆ {2}) {k : ℕ} (hk : 0 < k) :
    6 ≤ weight (lateBase n c ^ k * M) := by
  have hn18 : 18 ≤ n := by omega
  have hnz (a : ℕ) (ha : 1 ≤ a ∧ a ≤ n) : c a ≠ 0 := hc a (Finset.mem_Icc.mpr ha)
  let f : PUnit.{1} → ℕ := fun _ => 2
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  have hvars' : (M.vars : Set ℕ) ⊆ Set.range f := by
    intro z hz
    have hz2 : z = 2 := hvars hz
    exact ⟨(), hz2.symm⟩
  obtain ⟨M₀, hM₀⟩ := exists_rename_eq_of_vars_subset_range M f hf hvars'
  have hM₀ne : M₀ ≠ 0 := by
    intro hz
    apply hM
    rw [← hM₀, hz, map_zero]
  have hrename : rename f M₀ = rename coreNineVariables (rename some M₀) := by
    rw [rename_rename]
    rfl
  have hB0 : (lateBaseMiddle n c).coeff 0 ≠ 0 := by
    rcases hn with rfl | rfl <;> simpa [lateBaseMiddle] using hnz 3 (by omega)
  have hB1 : (lateBaseMiddle n c).coeff 1 ≠ 0 := by
    rcases hn with rfl | rfl <;> simpa [lateBaseMiddle] using hnz 6 (by omega)
  have h := bivariateQuadratic_power_mul_six
    (lateBaseBottom c) (lateBaseMiddle n c) (lateBaseTop c)
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 1 (by omega))
    (by simpa [lateBaseBottom, coreNineBottom] using hnz 2 (by omega)) hB0 hB1
    (by simpa [lateBaseTop] using hnz 9 (by omega))
    (by simpa [lateBaseTop] using hnz 18 (by omega)) M₀ hM₀ne hk
  rw [lateBase, ← hM₀, hrename, ← map_pow, ← map_mul,
    weight_rename_of_injective coreNineVariables coreNineVariables_injective]
  exact h

end WeightedPilz
