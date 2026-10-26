import WeightedPilz.Arithmetic.FastPrimeCounts

/-! Exact endpoint budgets in equation (large-endpoint-budgets).
These are computations of the defining finite sets, not assumptions about a table.
-/

set_option Elab.async false

namespace WeightedPilz.Arithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem endpointBudgets_67_82 :
    ∀ n ∈ Finset.Icc 67 82,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_83_98 :
    ∀ n ∈ Finset.Icc 83 98,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_99_114 :
    ∀ n ∈ Finset.Icc 99 114,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_115_130 :
    ∀ n ∈ Finset.Icc 115 130,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_131_146 :
    ∀ n ∈ Finset.Icc 131 146,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_147_162 :
    ∀ n ∈ Finset.Icc 147 162,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_163_178 :
    ∀ n ∈ Finset.Icc 163 178,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_179_194 :
    ∀ n ∈ Finset.Icc 179 194,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_195_210 :
    ∀ n ∈ Finset.Icc 195 210,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_211_226 :
    ∀ n ∈ Finset.Icc 211 226,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

private theorem endpointBudgets_227_228 :
    ∀ n ∈ Finset.Icc 227 228,
      n ≤ endpoint n + squareCost n + freshCount n ∧
      n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by weighted_decide

/-- Both endpoint inequalities, including the endpoints 67 and 228. -/
theorem endpointBudgets {n : ℕ} (hn : 67 ≤ n) (hn' : n ≤ 228) :
    n ≤ endpoint n + squareCost n + freshCount n ∧
    n ≤ endpoint n + squareCost n + linearCoreCount n + 1 := by
  have hc : (67 ≤ n ∧ n ≤ 82) ∨
      (83 ≤ n ∧ n ≤ 98) ∨
      (99 ≤ n ∧ n ≤ 114) ∨
      (115 ≤ n ∧ n ≤ 130) ∨
      (131 ≤ n ∧ n ≤ 146) ∨
      (147 ≤ n ∧ n ≤ 162) ∨
      (163 ≤ n ∧ n ≤ 178) ∨
      (179 ≤ n ∧ n ≤ 194) ∨
      (195 ≤ n ∧ n ≤ 210) ∨
      (211 ≤ n ∧ n ≤ 226) ∨
      (227 ≤ n ∧ n ≤ 228) := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h
  · exact endpointBudgets_67_82 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_83_98 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_99_114 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_115_130 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_131_146 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_147_162 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_163_178 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_179_194 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_195_210 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_211_226 n (Finset.mem_Icc.mpr h)
  · exact endpointBudgets_227_228 n (Finset.mem_Icc.mpr h)

private theorem dimension_budget_of_block {a b n r d : ℕ}
    (ha : a ≤ n) (hb : n ≤ b)
    (hr : r = primeCount a - primeCount (b / 2))
    (hd : d = 1 + primeCount (a / 2))
    (hbudget : b ≤ d + r * (r + 1) / 2) :
    n ≤ 1 + primeCount (n / 2) + squareCost n := by
  have hrn : r ≤ freshCount n := by
    rw [hr]
    exact freshCount_block_lower ha hb
  have hdn : d ≤ 1 + primeCount (n / 2) := by
    rw [hd]
    exact Nat.add_le_add_left (primeCount_mono (Nat.div_le_div_right ha)) 1
  have hR : r * (r + 1) / 2 ≤ squareCost n :=
    Nat.div_le_div_right (Nat.mul_le_mul hrn (Nat.add_le_add_right hrn 1))
  omega

/-- The thirteen exact blocks in the second endpoint table. -/
theorem dimensionBudget {n : ℕ} (hn : 229 ≤ n) (hn' : n ≤ 1799) :
    n ≤ 1 + primeCount (n / 2) + squareCost n := by
  have hc :
      (229 ≤ n ∧ n ≤ 241) ∨ (242 ≤ n ∧ n ≤ 262) ∨
      (263 ≤ n ∧ n ≤ 286) ∨ (287 ≤ n ∧ n ≤ 325) ∨
      (326 ≤ n ∧ n ≤ 361) ∨ (362 ≤ n ∧ n ≤ 397) ∨
      (398 ≤ n ∧ n ≤ 457) ∨ (458 ≤ n ∧ n ≤ 541) ∨
      (542 ≤ n ∧ n ≤ 654) ∨ (655 ≤ n ∧ n ≤ 837) ∨
      (838 ≤ n ∧ n ≤ 1093) ∨ (1094 ≤ n ∧ n ≤ 1480) ∨
      (1481 ≤ n ∧ n ≤ 1799) := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact dimension_budget_of_block (r := 20) (d := 31) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 21) (d := 31) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 22) (d := 33) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 24) (d := 35) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 25) (d := 39) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 27) (d := 43) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 29) (d := 47) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 31) (d := 51) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 34) (d := 59) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 39) (d := 67) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 45) (d := 82) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 52) (d := 102) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)
  · exact dimension_budget_of_block (r := 80) (d := 132) h.1 h.2 (by fast_prime_decide) (by fast_prime_decide) (by fast_prime_decide)

end WeightedPilz.Arithmetic




