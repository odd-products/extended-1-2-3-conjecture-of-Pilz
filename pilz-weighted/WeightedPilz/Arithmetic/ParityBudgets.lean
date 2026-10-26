import WeightedPilz.Arithmetic.MiddleBudgets
import Mathlib.Data.Nat.Squarefree

/-! Exact finite arithmetic for the characteristic-two argument. Squarefree
sets below have their ordinary mathematical meaning, proved from the bounded
divisor definition before any computation is used. -/

set_option Elab.async false

namespace WeightedPilz.Arithmetic

open scoped BigOperators

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def SquarefreeByDivisors (a : ℕ) : Prop :=
  0 < a ∧ ∀ k ∈ Finset.Icc 2 a, ¬ k * k ∣ a

instance (a : ℕ) : Decidable (SquarefreeByDivisors a) :=
  inferInstanceAs (Decidable (0 < a ∧ ∀ k ∈ Finset.Icc 2 a, ¬ k * k ∣ a))

theorem squarefreeByDivisors_iff (a : ℕ) : SquarefreeByDivisors a ↔ Squarefree a := by
  constructor
  · rintro ⟨hapos, hdiv⟩
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hpp
    have hpdiv : p ∣ a := dvd_trans (dvd_mul_right p p) hpp
    exact hdiv p (Finset.mem_Icc.mpr ⟨hp.two_le, Nat.le_of_dvd hapos hpdiv⟩) hpp
  · intro hsq
    refine ⟨Nat.pos_of_ne_zero hsq.ne_zero, ?_⟩
    intro k hk hdiv
    have hkone : k = 1 := Nat.isUnit_iff.mp (hsq k hdiv)
    have hk2 := (Finset.mem_Icc.mp hk).1
    omega

def squarefreeNumbers (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter SquarefreeByDivisors

def singletonParityNumbers (n : ℕ) : Finset ℕ :=
  (Finset.Icc (n / 4 + 1) n).filter SquarefreeByDivisors

theorem mem_squarefreeNumbers (n a : ℕ) :
    a ∈ squarefreeNumbers n ↔ 1 ≤ a ∧ a ≤ n ∧ Squarefree a := by
  simp [squarefreeNumbers, squarefreeByDivisors_iff, and_assoc]

theorem mem_singletonParityNumbers (n a : ℕ) :
    a ∈ singletonParityNumbers n ↔ n / 4 < a ∧ a ≤ n ∧ Squarefree a := by
  simp only [singletonParityNumbers, Finset.mem_filter, Finset.mem_Icc,
    squarefreeByDivisors_iff, Nat.add_one_le_iff, and_assoc]

private theorem singletonParity_formula_checked :
    ∀ n ∈ Finset.Icc 1 66,
      (singletonParityNumbers n).card + 2 * (n / 4) + n / 9 + n / 25 + n / 49 =
        n + n / 16 + 2 * (n / 36) := by weighted_decide

/-- The exact inclusion-exclusion formula, with negative terms transposed. -/
theorem singletonParity_formula {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 66) :
    (singletonParityNumbers n).card + 2 * (n / 4) + n / 9 + n / 25 + n / 49 =
      n + n / 16 + 2 * (n / 36) :=
  singletonParity_formula_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)

private theorem singletonParity_budget_checked :
    ∀ n ∈ Finset.Icc 25 66, n ≤ 3 * (singletonParityNumbers n).card := by weighted_decide

theorem singletonParity_budget {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66) :
    n ≤ 3 * (singletonParityNumbers n).card :=
  singletonParity_budget_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)

theorem singletonParity_initial_counts :
    (singletonParityNumbers 25).card = 11 ∧ (singletonParityNumbers 26).card = 12 := by weighted_decide

/-- All possible four-term exceptions, with the defining two strict inequalities. -/
theorem binary_four_term_exceptions :
    (Finset.Icc 25 66).filter (fun n =>
      binaryKappa n + 4 * freshCount n < n ∧
      n < 2 * (3 * Nat.sqrt n + Nat.sqrt (n / 2))) =
      {27, 28, 34, 35, 36, 38, 39, 40, 49, 50, 51} := by weighted_decide

private theorem binary_width_budgets_checked :
    ∀ n ∈ Finset.Icc 25 66,
      n ≤ freshCount n * binaryKappa n ∧
      ((n - 1 - binaryKappa n) / freshCount n ≤ 4 ∨ n = 58) ∧
      (n - 1 - binaryKappa n) / freshCount n ≤ 5 := by weighted_decide

theorem binary_width_budgets {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66) :
    n ≤ freshCount n * binaryKappa n ∧
    ((n - 1 - binaryKappa n) / freshCount n ≤ 4 ∨ n = 58) ∧
    (n - 1 - binaryKappa n) / freshCount n ≤ 5 :=
  binary_width_budgets_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)

theorem binary_five_term_data : (freshCount 58, binaryKappa 58) = (6, 27) := by weighted_decide

private theorem binary_capacity_checked :
    ∀ n ∈ Finset.Icc 25 66,
      4 * Nat.sqrt n ≤ n ∧
      (26 ≤ n → 4 * Nat.sqrt n + 2 * Nat.sqrt (n / 2) ≤ n) ∧
      (n ∈ ({27, 28, 34, 35, 36, 38, 39, 40, 49, 50, 51} : Finset ℕ) →
        2 * (3 * Nat.sqrt n + Nat.sqrt (n / 2)) ≤ n + 4 * freshCount n) := by weighted_decide

theorem binary_capacity {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66) :
    4 * Nat.sqrt n ≤ n ∧
    (26 ≤ n → 4 * Nat.sqrt n + 2 * Nat.sqrt (n / 2) ≤ n) ∧
    (n ∈ ({27, 28, 34, 35, 36, 38, 39, 40, 49, 50, 51} : Finset ℕ) →
      2 * (3 * Nat.sqrt n + Nat.sqrt (n / 2)) ≤ n + 4 * freshCount n) :=
  binary_capacity_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)

/-- Squarefree counts used when the parity displacement has an odd prime factor. -/
theorem parity_pair_squarefree_counts :
    (squarefreeNumbers 27).card = 17 ∧
    (squarefreeNumbers 28).card = 17 ∧
    (squarefreeNumbers 36).card = 23 := by weighted_decide

private theorem parity_pair_odd_prime_counts_checked :
    ∀ p ∈ Finset.Icc 3 36, Nat.Prime p →
      ((squarefreeNumbers 27).filter (p ∣ ·)).card ≤ 4 ∧
      ((squarefreeNumbers 28).filter (p ∣ ·)).card ≤ 4 ∧
      ((squarefreeNumbers 36).filter (p ∣ ·)).card ≤ 6 := by weighted_decide

theorem parity_pair_odd_prime_counts {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    ((squarefreeNumbers 27).filter (p ∣ ·)).card ≤ 4 ∧
    ((squarefreeNumbers 28).filter (p ∣ ·)).card ≤ 4 ∧
    ((squarefreeNumbers 36).filter (p ∣ ·)).card ≤ 6 := by
  by_cases hp36 : p ≤ 36
  · exact parity_pair_odd_prime_counts_checked p (Finset.mem_Icc.mpr ⟨hp3, hp36⟩) hp
  · have he : ∀ n ≤ 36, ((squarefreeNumbers n).filter (p ∣ ·)) = ∅ := by
      intro n hn
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨ha, hpa⟩ := Finset.mem_filter.mp ha
      obtain ⟨ha1, han, _⟩ := (mem_squarefreeNumbers n a).mp ha
      have hpa' := Nat.le_of_dvd (by omega : 0 < a) hpa
      omega
    rw [he 27 (by weighted_decide), he 28 (by weighted_decide), he 36 (by weighted_decide)]
    decide

def parityTripleCost (k : ℕ) : ℕ := [0, 3, 2, 3, 4, 6, 6].getD k 0

def parityPairCost (k l : ℕ) : ℕ :=
  if k = 0 then parityTripleCost l + l
  else if l = 0 then parityTripleCost k + k
  else (parityTripleCost k - l) + (parityTripleCost l - k)

def oddSquarefreeNumbers (n : ℕ) : Finset ℕ :=
  (squarefreeNumbers n).filter (fun s => s % 2 = 1)

/-- Sum of the pair bounds over each odd squarefree part, for displacement two. -/
def parityTwoBudget (n : ℕ) : ℕ :=
  ∑ s ∈ oddSquarefreeNumbers n,
    parityPairCost (Nat.sqrt (n / (2 * s))) (Nat.sqrt (n / s))

theorem parity_two_budgets :
    parityTwoBudget 27 = 38 ∧ parityTwoBudget 28 = 36 ∧ parityTwoBudget 36 = 51 := by
  unfold parityTwoBudget
  weighted_decide

end WeightedPilz.Arithmetic



