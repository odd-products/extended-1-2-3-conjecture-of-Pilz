import Pilz.SmallCaseCriterion
import Pilz.UnitIntervalClasses
import Pilz.FourMultipliers

/-! The regular finite blocks of the small-case proof. All polynomial
inputs are supplied by the core distance, four-term multiplier theorem,
and dispersed capacity; the remaining hypotheses are finite arithmetic
row checks. -/

noncomputable section

namespace Pilz

/-- The common table criterion for lengths eleven through sixty-six and
at most four synchronized multiplier terms. -/
theorem conjectureAt_small_regular (n κ r T U M : ℕ)
    (hn : 11 ≤ n) (hsmall : n ≤ 66)
    (hr : (freshPrimes n).card = r) (hrpos : 0 < r)
    (hκ : κ ≤ distance (core n)) (hκpos : 2 ≤ κ)
    (hbound : ∀ m : ℕ, m < n → (Even n → Even m) → m ≤ T)
    (hreduce : ∀ m u : ℕ, 0 < u → r * u < m → 2 * u ≤ m → m ≤ T →
      u < κ ∧ (r * u + κ ≤ m → u ≤ U))
    (hU : U ≤ 4)
    (hMthree : min U 3 * Nat.sqrt n ≤ M)
    (hMfour : U = 4 → 3 * Nat.sqrt n + Nat.sqrt (n / 2) ≤ M)
    (hNM : 2 * M ≤ n) : ConjectureAt n := by
  classical
  have hnpos : 0 < n := by omega
  have hfresh : (freshPrimes n).Nonempty := Finset.card_pos.mp (by omega)
  let S := intervalFreshData n hnpos hfresh
  have hF : S.F = interval n := intervalFreshData_F n hnpos hfresh
  refine conjectureAt_of_core_capacity n κ r T U M S hF hr hκ hκpos
    hbound hreduce ?_ ?_ hNM
  · intro nf hu ε
    change classWeight (core n * nf.D) ε ≤ M
    by_cases hthree : weight nf.D ≤ 3
    · have hcap := classWeight_mul_le (core n) nf.D (Nat.sqrt n)
        (fun η => (classWeight_le_sigma (core n) η).trans (sigma_core_le_sqrt n)) ε
      calc
        classWeight (core n * nf.D) ε ≤ Nat.sqrt n * weight nf.D := hcap
        _ = weight nf.D * Nat.sqrt n := Nat.mul_comm _ _
        _ ≤ min U 3 * Nat.sqrt n := Nat.mul_le_mul_right _ (le_min hu hthree)
        _ ≤ M := hMthree
    · have huEq : weight nf.D = 4 := by omega
      have hUEq : U = 4 := by omega
      have hclasses := normalForm_interval_at_least_two_classes n hnpos hfresh nf hsmall
        (by omega : 4 ≤ weight nf.D)
      have hcap := classWeight_core_mul_dispersed_two n nf.D hclasses ε
      have hcap' : classWeight (core n * nf.D) ε ≤
          3 * Nat.sqrt n + Nat.sqrt (n / 2) := by simpa [huEq] using hcap
      exact hcap'.trans (hMfour hUEq)
  · intro D hD hu
    exact four_multipliers_ge_eleven n D hn hD (hu.trans hU)

/-- For lengths twenty-six through twenty-nine, three synchronized terms
already occupy at least two classes. This improves the capacity to
`2*sqrt(n)+sqrt(n/2)` whenever the numerical row has `U=3`. -/
theorem conjectureAt_small_regular_26_29 (n κ r T U M : ℕ)
    (hlo : 26 ≤ n) (hhi : n ≤ 29)
    (hr : (freshPrimes n).card = r) (hrpos : 0 < r)
    (hκ : κ ≤ distance (core n)) (hκpos : 2 ≤ κ)
    (hbound : ∀ m : ℕ, m < n → (Even n → Even m) → m ≤ T)
    (hreduce : ∀ m u : ℕ, 0 < u → r * u < m → 2 * u ≤ m → m ≤ T →
      u < κ ∧ (r * u + κ ≤ m → u ≤ U))
    (hU : U ≤ 3)
    (hMtwo : min U 2 * Nat.sqrt n ≤ M)
    (hMthree : U = 3 → 2 * Nat.sqrt n + Nat.sqrt (n / 2) ≤ M)
    (hNM : 2 * M ≤ n) : ConjectureAt n := by
  classical
  have hnpos : 0 < n := by omega
  have hfresh : (freshPrimes n).Nonempty := Finset.card_pos.mp (by omega)
  let S := intervalFreshData n hnpos hfresh
  have hF : S.F = interval n := intervalFreshData_F n hnpos hfresh
  refine conjectureAt_of_core_capacity n κ r T U M S hF hr hκ hκpos
    hbound hreduce ?_ ?_ hNM
  · intro nf hu ε
    change classWeight (core n * nf.D) ε ≤ M
    by_cases htwo : weight nf.D ≤ 2
    · have hcap := classWeight_mul_le (core n) nf.D (Nat.sqrt n)
        (fun η => (classWeight_le_sigma (core n) η).trans (sigma_core_le_sqrt n)) ε
      calc
        classWeight (core n * nf.D) ε ≤ Nat.sqrt n * weight nf.D := hcap
        _ = weight nf.D * Nat.sqrt n := Nat.mul_comm _ _
        _ ≤ min U 2 * Nat.sqrt n := Nat.mul_le_mul_right _ (le_min hu htwo)
        _ ≤ M := hMtwo
    · have huEq : weight nf.D = 3 := by omega
      have hUEq : U = 3 := by omega
      have hclasses := normalForm_interval_at_least_two_classes_26_29 n hnpos hfresh nf
        hlo hhi (by omega : 3 ≤ weight nf.D)
      have hcap := classWeight_core_mul_dispersed_two n nf.D hclasses ε
      have hcap' : classWeight (core n * nf.D) ε ≤
          2 * Nat.sqrt n + Nat.sqrt (n / 2) := by simpa [huEq] using hcap
      exact hcap'.trans (hMthree hUEq)
  · intro D hD hu
    exact four_multipliers_ge_eleven n D (by omega) hD (by omega)

end Pilz
