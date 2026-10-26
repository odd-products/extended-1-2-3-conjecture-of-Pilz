import WeightedPilz.Arithmetic.FastPrimeCounts

/-! The two printed endpoint tables, with their exact entries and coverage. -/

namespace WeightedPilz.Arithmetic

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

structure EndpointTableRow where
  a : ℕ
  b : ℕ
  r : ℕ
  kappa : ℕ
  h : ℕ
  leftBudget : ℕ
  rightBudget : ℕ
  deriving DecidableEq, Repr

/-- The fourteen rows printed before `eq:large-endpoint-budgets`. -/
def endpointTable : List EndpointTableRow :=
  [⟨67, 72, 8, 28, 7, 72, 72⟩,
   ⟨73, 81, 9, 30, 7, 84, 83⟩,
   ⟨82, 85, 9, 37, 9, 91, 92⟩,
   ⟨86, 93, 9, 40, 10, 94, 96⟩,
   ⟨94, 101, 9, 47, 11, 101, 104⟩,
   ⟨102, 115, 10, 50, 11, 115, 117⟩,
   ⟨116, 120, 13, 58, 12, 162, 162⟩,
   ⟨121, 133, 12, 53, 12, 143, 144⟩,
   ⟨134, 145, 12, 62, 14, 152, 155⟩,
   ⟨146, 161, 12, 71, 16, 161, 166⟩,
   ⟨162, 168, 14, 80, 17, 199, 203⟩,
   ⟨169, 193, 15, 72, 17, 207, 210⟩,
   ⟨194, 223, 15, 88, 19, 223, 228⟩,
   ⟨224, 228, 18, 109, 23, 298, 304⟩]

def EndpointTableRow.Correct (v : EndpointTableRow) : Prop :=
  v.r = primeCount v.a - primeCount (v.b / 2) ∧
  v.kappa = endpoint v.a ∧
  v.h = primeCount (v.a / 2) - primeCount (Nat.sqrt v.b) ∧
  v.leftBudget = v.kappa + v.r * (v.r + 1) / 2 + v.r ∧
  v.rightBudget = v.kappa + v.r * (v.r + 1) / 2 + v.h + 1 ∧
  v.b ≤ v.leftBudget ∧ v.b ≤ v.rightBudget

/-- Every displayed entry is calculated from the actual prime sets. -/
theorem endpointTable_correct : ∀ v ∈ endpointTable, v.Correct := by
  simp only [EndpointTableRow.Correct]
  weighted_decide

theorem endpointTable_covers {n : ℕ} (hn : 67 ≤ n) (hn' : n ≤ 228) :
    ∃ v ∈ endpointTable, v.a ≤ n ∧ n ≤ v.b := by
  have h : ∀ n ∈ Finset.Icc 67 228,
      ∃ v ∈ endpointTable, v.a ≤ n ∧ n ≤ v.b := by decide +kernel
  exact h n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)

/-- The three quantities used by a printed row remain lower bounds throughout it. -/
theorem endpointTable_lower_bounds : ∀ v ∈ endpointTable,
    ∀ n ∈ Finset.Icc v.a v.b,
      v.r ≤ freshCount n ∧ v.kappa ≤ endpoint n ∧ v.h ≤ linearCoreCount n := by
  weighted_decide

structure DimensionTableRow where
  a : ℕ
  b : ℕ
  r : ℕ
  d : ℕ
  square : ℕ
  budget : ℕ
  deriving DecidableEq, Repr

/-- The thirteen printed dimension-budget rows through 1799. -/
def dimensionTable : List DimensionTableRow :=
  [⟨229, 241, 20, 31, 210, 241⟩,
   ⟨242, 262, 21, 31, 231, 262⟩,
   ⟨263, 286, 22, 33, 253, 286⟩,
   ⟨287, 325, 24, 35, 300, 335⟩,
   ⟨326, 361, 25, 39, 325, 364⟩,
   ⟨362, 397, 27, 43, 378, 421⟩,
   ⟨398, 457, 29, 47, 435, 482⟩,
   ⟨458, 541, 31, 51, 496, 547⟩,
   ⟨542, 654, 34, 59, 595, 654⟩,
   ⟨655, 837, 39, 67, 780, 847⟩,
   ⟨838, 1093, 45, 82, 1035, 1117⟩,
   ⟨1094, 1480, 52, 102, 1378, 1480⟩,
   ⟨1481, 1799, 80, 132, 3240, 3372⟩]

def DimensionTableRow.Correct (v : DimensionTableRow) : Prop :=
  v.r = primeCount v.a - primeCount (v.b / 2) ∧
  v.d = 1 + primeCount (v.a / 2) ∧
  v.square = v.r * (v.r + 1) / 2 ∧
  v.budget = v.d + v.square ∧ v.b ≤ v.budget

theorem dimensionTable_correct : ∀ v ∈ dimensionTable, v.Correct := by
  simp only [DimensionTableRow.Correct]
  fast_prime_decide

theorem dimensionTable_covers {n : ℕ} (hn : 229 ≤ n) (hn' : n ≤ 1799) :
    ∃ v ∈ dimensionTable, v.a ≤ n ∧ n ≤ v.b := by
  have h : ∀ n ∈ Finset.Icc 229 1799,
      ∃ v ∈ dimensionTable, v.a ≤ n ∧ n ≤ v.b := by decide +kernel
  exact h n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)

theorem dimensionTable_lower_bounds {v : DimensionTableRow} (hv : v ∈ dimensionTable)
    {n : ℕ} (ha : v.a ≤ n) (hb : n ≤ v.b) :
    v.r ≤ freshCount n ∧ v.d ≤ 1 + primeCount (n / 2) ∧ v.square ≤ squareCost n := by
  obtain ⟨hr, hd, hR, _, _⟩ := dimensionTable_correct v hv
  have hrn : v.r ≤ freshCount n := by rw [hr]; exact freshCount_block_lower ha hb
  refine ⟨hrn, ?_, ?_⟩
  · rw [hd]
    exact Nat.add_le_add_left (primeCount_mono (Nat.div_le_div_right ha)) 1
  · rw [hR, squareCost]
    exact Nat.div_le_div_right (Nat.mul_le_mul hrn (Nat.add_le_add_right hrn 1))

end WeightedPilz.Arithmetic
