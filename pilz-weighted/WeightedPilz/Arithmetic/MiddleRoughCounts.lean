import WeightedPilz.Arithmetic.Counts
import Pilz.Sieve
import Mathlib.Data.Finset.Max

/-! Exact rough counts for the six-input and characteristic-two comparison
tables in the frozen middle interval proof. Negative contributions are moved
to the left in natural-number bounds; signed table entries use integers. -/

namespace WeightedPilz.Arithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def roughCount (q n : ℕ) : ℕ :=
  Pilz.roughCount ((Finset.range (q + 1)).filter Nat.Prime) n

private theorem sixInput_rough_budgets_checked :
    ∀ n ∈ Finset.Icc 25 66,
      n ≤ 2 * roughCount 2 n ∧
      n + roughCount 3 (n / 3) ≤ 3 * roughCount 3 n + roughCount 3 (n / 2) ∧
      n ≤ 4 * roughCount 5 n ∧
      n + roughCount 7 (n / 2) + 3 * roughCount 7 (n / 7) ≤
        5 * roughCount 7 n + 2 * roughCount 7 (n / 3) + 2 * roughCount 7 (n / 5) := by
  decide +kernel

theorem sixInput_rough_budgets {n : ℕ} (hn : 25 ≤ n) (hn' : n ≤ 66) :
    n ≤ 2 * roughCount 2 n ∧
    n + roughCount 3 (n / 3) ≤ 3 * roughCount 3 n + roughCount 3 (n / 2) ∧
    n ≤ 4 * roughCount 5 n ∧
    n + roughCount 7 (n / 2) + 3 * roughCount 7 (n / 7) ≤
      5 * roughCount 7 n + 2 * roughCount 7 (n / 3) + 2 * roughCount 7 (n / 5) :=
  sixInput_rough_budgets_checked n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)

/-- The complete list of seven-rough positive integers through 66. -/
theorem seven_rough_list :
    Pilz.roughNumbers {2, 3, 5, 7} 66 =
      {1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by decide +kernel

/-- Exact endpoint data in each of the six monotonicity blocks. -/
def SevenRoughRow (a b A B C D E : ℕ) : Prop :=
  (roughCount 7 a, roughCount 7 (b / 2), roughCount 7 (a / 3),
    roughCount 7 (a / 5), roughCount 7 (b / 7)) = (A, B, C, D, E) ∧
  b + B + 3 * E = 5 * A + 2 * C + 2 * D

instance (a b A B C D E : ℕ) : Decidable (SevenRoughRow a b A B C D E) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem sevenRough_25_28 : SevenRoughRow 25 28 6 3 1 1 1 := by decide +kernel
theorem sevenRough_29_33 : SevenRoughRow 29 33 7 3 1 1 1 := by decide +kernel
theorem sevenRough_34_38 : SevenRoughRow 34 38 8 5 2 1 1 := by decide +kernel
theorem sevenRough_39_45 : SevenRoughRow 39 45 9 5 3 1 1 := by decide +kernel
theorem sevenRough_46_54 : SevenRoughRow 46 54 11 6 3 1 1 := by decide +kernel
theorem sevenRough_55_66 : SevenRoughRow 55 66 13 8 4 2 1 := by decide +kernel

def roughProfile2 (n u : ℕ) : ℤ :=
  u * (roughCount 2 n : ℤ) + (2 - (u : ℤ)) * roughCount 2 (n / 2)

def roughProfile3 (n u : ℕ) : ℤ :=
  u * (roughCount 3 n : ℤ) + (4 - (u : ℤ)) * roughCount 3 (n / 2) -
    roughCount 3 (n / 3)

def roughProfile5 (n u : ℕ) : ℤ :=
  u * (roughCount 5 n : ℤ) + (4 - (u : ℤ)) * roughCount 5 (n / 2) +
    2 * roughCount 5 (n / 3) - 2 * roughCount 5 (n / 5)

def roughProfile5plus (n u : ℕ) : ℤ :=
  roughProfile5 n u + if 27 ≤ n ∧ n ≤ 48 then 2 else 0

def roughProfile7 (n u : ℕ) : ℤ :=
  u * (roughCount 7 n : ℤ) + (4 - (u : ℤ)) * roughCount 7 (n / 2) +
    2 * roughCount 7 (n / 3) + 2 * roughCount 7 (n / 5) - 3 * roughCount 7 (n / 7)

def quantitativeCut (n u q : ℕ) : ℤ :=
  2 * (n : ℤ) - 2 * ((u : ℤ) - 1) * (n / q : ℕ)

def ComparisonRow (a b u q cut h2 h3 h5 : ℕ) : Prop :=
  ((Finset.Icc a b).image (fun n => quantitativeCut n u q)).min = (cut : ℤ) ∧
  ((Finset.Icc a b).image (fun n => roughProfile2 n u)).min = (h2 : ℤ) ∧
  ((Finset.Icc a b).image (fun n => roughProfile3 n u)).min = (h3 : ℤ) ∧
  ((Finset.Icc a b).image (fun n => roughProfile5plus n u)).min = (h5 : ℤ)

instance (a b u q cut h2 h3 h5 : ℕ) : Decidable (ComparisonRow a b u q cut h2 h3 h5) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The first row needs only q = 2 and q = 3 below its cut threshold five. -/
theorem comparison_25 :
    quantitativeCut 25 3 5 = 30 ∧ roughProfile2 25 3 = 33 ∧ roughProfile3 25 3 = 28 := by
  decide +kernel

theorem comparison_27_28 : ComparisonRow 27 28 4 7 32 42 33 32 := by decide +kernel
theorem comparison_34_35 : ComparisonRow 34 35 4 7 40 50 40 40 := by decide +kernel
theorem comparison_36 : ComparisonRow 36 36 4 7 42 54 44 40 := by decide +kernel
theorem comparison_38 : ComparisonRow 38 38 4 7 46 56 48 44 := by decide +kernel
theorem comparison_39_40 : ComparisonRow 39 40 4 7 48 60 47 46 := by decide +kernel
theorem comparison_49_51 : ComparisonRow 49 51 4 7 56 74 62 60 := by decide +kernel
theorem comparison_58 : ComparisonRow 58 58 5 11 76 100 78 73 := by decide +kernel
theorem comparison_58_seven : roughProfile7 58 5 = 69 := by decide +kernel

end WeightedPilz.Arithmetic
