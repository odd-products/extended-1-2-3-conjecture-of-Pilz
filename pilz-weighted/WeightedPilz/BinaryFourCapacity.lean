import WeightedPilz.BinaryComparisonAll
import WeightedPilz.ParityPattern
import WeightedPilz.ParityIntegerBounds
import Mathlib.Tactic.NormNum.NatSqrt

/-! The exceptional four-term inputs satisfy a comparison bound twice as
large as their actual two-level residue capacity. -/
noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K] [CharP K 2]

theorem binary_four_exception_capacity_of_smooth (n : ℕ) (c : ℕ → K) (H : Poly K)
    (hc : NonzeroWeights n c) (hH : H ≠ 0) (hu : weight H = 4)
    (hcore : 27 ≤ n → n ≤ 48 → 6 ≤ distance (smoothInterval (Pilz.primesUpTo 5) n c))
    (hclasses : 2 ≤ (residueIndices 2 H).card)
    (hex : n ∈ ({27,28,34,35,36,38,39,40,49,50,51} : Finset ℕ)) :
    ∃ M : ℕ, (∀α, residueWeight 2 (intervalCore n c * H) α ≤ M) ∧
      2 * M ≤ n + 4 * Arithmetic.freshCount n ∧
      2 * M ≤ weight (interval n c * H) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let M := if ∃β, residueWeight 2 H β = 3 then
      3 * Nat.sqrt n + Nat.sqrt (n / 2) else 2 * Nat.sqrt n + 2 * Nat.sqrt (n / 2)
  have hMle : M ≤ 3 * Nat.sqrt n + Nat.sqrt (n / 2) := by
    have ht := Nat.sqrt_le_sqrt (Nat.div_le_self n 2)
    dsimp [M]
    split_ifs <;> omega
  have hcap : ∀α, residueWeight 2 (intervalCore n c * H) α ≤ M := by
    intro α
    by_cases hthree : ∃β, residueWeight 2 H β = 3
    · simp only [M, if_pos hthree]
      simpa only [hu, Nat.reduceSub] using intervalCore_parity_mixed_capacity n c hc H hclasses α
    · simp only [M, if_neg hthree]
      exact intervalCore_parity_four_capacity n c hc H hu hclasses hthree α
  have hn25 : 25 ≤ n := by simp only [Finset.mem_insert, Finset.mem_singleton] at hex; omega
  have hn66 : n ≤ 66 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hex; omega
  have hgate := (Arithmetic.binary_capacity hn25 hn66).2.2 hex
  refine ⟨M, hcap, (Nat.mul_le_mul_left 2 hMle).trans hgate, ?_⟩
  have hother (L : ℕ) (hL : 2 * (3 * Nat.sqrt n + Nat.sqrt (n / 2)) ≤ L)
      (hcomp : L ≤ weight (interval n c * H)) : 2 * M ≤ weight (interval n c * H) :=
    (Nat.mul_le_mul_left 2 hMle).trans (hL.trans hcomp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · by_cases hthree : ∃β, residueWeight 2 H β = 3
    · have h := interval_four_term_three_class_bound 27 (by omega) c hc H hu hthree
      norm_num [M, hthree] at h ⊢
      exact h
    · have h := binary_comparison_27_28_all 27 c H hc (by omega) (by omega) hH hu (hcore (by omega) (by omega))
      norm_num [M, hthree]
      exact h
  · by_cases hthree : ∃β, residueWeight 2 H β = 3
    · have h := interval_four_term_three_class_bound 28 (by omega) c hc H hu hthree
      norm_num [M, hthree] at h ⊢
      exact h
    · have h := binary_comparison_27_28_all 28 c H hc (by omega) (by omega) hH hu (hcore (by omega) (by omega))
      norm_num [M, hthree]
      exact h
  · exact hother 40 (by norm_num)
      (binary_comparison_34_35_all 34 c H hc (by omega) (by omega) hH hu (hcore (by omega) (by omega)))
  · exact hother 40 (by norm_num)
      (binary_comparison_34_35_all 35 c H hc (by omega) (by omega) hH hu (hcore (by omega) (by omega)))
  · by_cases hthree : ∃β, residueWeight 2 H β = 3
    · have h := interval_four_term_three_class_bound 36 (by omega) c hc H hu hthree
      norm_num [M, hthree] at h ⊢
      exact h
    · have h := binary_comparison_36_all c H hc hH hu (hcore (by omega) (by omega))
      norm_num [M, hthree]
      exact h
  · exact hother 44 (by norm_num) (binary_comparison_38_all c H hc hH hu (hcore (by omega) (by omega)))
  · exact hother 46 (by norm_num)
      (binary_comparison_39_40_all 39 c H hc (by omega) (by omega) hH hu (hcore (by omega) (by omega)))
  · exact hother 46 (by norm_num)
      (binary_comparison_39_40_all 40 c H hc (by omega) (by omega) hH hu (hcore (by omega) (by omega)))
  · exact hother 56 (by norm_num) (binary_comparison_49_51_all 49 c H hc (by omega) (by omega) hH hu)
  · exact hother 56 (by norm_num) (binary_comparison_49_51_all 50 c H hc (by omega) (by omega) hH hu)
  · exact hother 56 (by norm_num) (binary_comparison_49_51_all 51 c H hc (by omega) (by omega) hH hu)

end WeightedPilz
