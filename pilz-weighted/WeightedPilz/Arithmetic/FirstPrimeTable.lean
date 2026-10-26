import WeightedPilz.Arithmetic.FastPrimeCounts

/-! Exact literal rows and coverage of the manuscript's first prime-budget table. -/

set_option Elab.async false

namespace WeightedPilz.Arithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- All four printed columns, interpreted using the actual prime-count function. -/
def FirstPrimeRow (a b r₀ B₀ : ℕ) : Prop :=
  r₀ = primeCount a - primeCount (b / 2) ∧
  B₀ + 48 = 10 * r₀ + 4 * primeCount (a / 2) +
    2 * primeCount (a / 3) + 2 * primeCount (a / 5) ∧
  Nat.sqrt b ≤ r₀ ∧ b ≤ B₀

macro "first_prime_row_decide" : tactic => `(tactic|
  (unfold FirstPrimeRow
   refine ⟨?_, ?_, Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (by decide)), by decide⟩
   all_goals fast_prime_decide))

/-- The thirteen rows exactly as printed, in their printed order. -/
def firstPrimeTable : List (ℕ × ℕ × ℕ × ℕ) :=
  [(101, 117, 10, 150),
   (118, 141, 11, 172),
   (142, 165, 12, 200),
   (166, 195, 13, 228),
   (196, 225, 15, 262),
   (226, 273, 16, 302),
   (274, 345, 19, 354),
   (346, 421, 22, 430),
   (422, 524, 27, 524),
   (525, 636, 33, 636),
   (637, 765, 40, 772),
   (766, 913, 48, 916),
   (914, 1023, 59, 1102)]

@[simp] theorem firstPrimeTable_length : firstPrimeTable.length = 13 := by decide

theorem firstPrimeRow_101_117 : FirstPrimeRow 101 117 10 150 := by
  first_prime_row_decide

theorem firstPrimeRow_118_141 : FirstPrimeRow 118 141 11 172 := by
  first_prime_row_decide

theorem firstPrimeRow_142_165 : FirstPrimeRow 142 165 12 200 := by
  first_prime_row_decide

theorem firstPrimeRow_166_195 : FirstPrimeRow 166 195 13 228 := by
  first_prime_row_decide

theorem firstPrimeRow_196_225 : FirstPrimeRow 196 225 15 262 := by
  first_prime_row_decide

theorem firstPrimeRow_226_273 : FirstPrimeRow 226 273 16 302 := by
  first_prime_row_decide

theorem firstPrimeRow_274_345 : FirstPrimeRow 274 345 19 354 := by
  first_prime_row_decide

theorem firstPrimeRow_346_421 : FirstPrimeRow 346 421 22 430 := by
  first_prime_row_decide

theorem firstPrimeRow_422_524 : FirstPrimeRow 422 524 27 524 := by
  first_prime_row_decide

theorem firstPrimeRow_525_636 : FirstPrimeRow 525 636 33 636 := by
  first_prime_row_decide

theorem firstPrimeRow_637_765 : FirstPrimeRow 637 765 40 772 := by
  first_prime_row_decide

theorem firstPrimeRow_766_913 : FirstPrimeRow 766 913 48 916 := by
  first_prime_row_decide

theorem firstPrimeRow_914_1023 : FirstPrimeRow 914 1023 59 1102 := by
  first_prime_row_decide

/-- Every literal row has its exact counts and both endpoint bounds. -/
theorem firstPrimeTable_rows {a b r₀ B₀ : ℕ}
    (h : (a, b, r₀, B₀) ∈ firstPrimeTable) : FirstPrimeRow a b r₀ B₀ := by
  simp only [firstPrimeTable, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · cases h0
    exact firstPrimeRow_101_117
  · cases h1
    exact firstPrimeRow_118_141
  · cases h2
    exact firstPrimeRow_142_165
  · cases h3
    exact firstPrimeRow_166_195
  · cases h4
    exact firstPrimeRow_196_225
  · cases h5
    exact firstPrimeRow_226_273
  · cases h6
    exact firstPrimeRow_274_345
  · cases h7
    exact firstPrimeRow_346_421
  · cases h8
    exact firstPrimeRow_422_524
  · cases h9
    exact firstPrimeRow_525_636
  · cases h10
    exact firstPrimeRow_637_765
  · cases h11
    exact firstPrimeRow_766_913
  · cases h12
    exact firstPrimeRow_914_1023

/-- The rows cover every integer of the stated interval, including both ends. -/
theorem firstPrimeTable_coverage {n : ℕ} (hn : 101 ≤ n) (hn' : n ≤ 1023) :
    ∃ a b r₀ B₀, (a, b, r₀, B₀) ∈ firstPrimeTable ∧ a ≤ n ∧ n ≤ b := by
  have hc :
      (101 ≤ n ∧ n ≤ 117) ∨
      (118 ≤ n ∧ n ≤ 141) ∨
      (142 ≤ n ∧ n ≤ 165) ∨
      (166 ≤ n ∧ n ≤ 195) ∨
      (196 ≤ n ∧ n ≤ 225) ∨
      (226 ≤ n ∧ n ≤ 273) ∨
      (274 ≤ n ∧ n ≤ 345) ∨
      (346 ≤ n ∧ n ≤ 421) ∨
      (422 ≤ n ∧ n ≤ 524) ∨
      (525 ≤ n ∧ n ≤ 636) ∨
      (637 ≤ n ∧ n ≤ 765) ∨
      (766 ≤ n ∧ n ≤ 913) ∨
      (914 ≤ n ∧ n ≤ 1023) := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · exact ⟨101, 117, 10, 150, by simp [firstPrimeTable], h0⟩
  · exact ⟨118, 141, 11, 172, by simp [firstPrimeTable], h1⟩
  · exact ⟨142, 165, 12, 200, by simp [firstPrimeTable], h2⟩
  · exact ⟨166, 195, 13, 228, by simp [firstPrimeTable], h3⟩
  · exact ⟨196, 225, 15, 262, by simp [firstPrimeTable], h4⟩
  · exact ⟨226, 273, 16, 302, by simp [firstPrimeTable], h5⟩
  · exact ⟨274, 345, 19, 354, by simp [firstPrimeTable], h6⟩
  · exact ⟨346, 421, 22, 430, by simp [firstPrimeTable], h7⟩
  · exact ⟨422, 524, 27, 524, by simp [firstPrimeTable], h8⟩
  · exact ⟨525, 636, 33, 636, by simp [firstPrimeTable], h9⟩
  · exact ⟨637, 765, 40, 772, by simp [firstPrimeTable], h10⟩
  · exact ⟨766, 913, 48, 916, by simp [firstPrimeTable], h11⟩
  · exact ⟨914, 1023, 59, 1102, by simp [firstPrimeTable], h12⟩

/-- Monotonicity transports the exact printed rows to all intervening integers. -/
theorem firstPrimeTable_bounds {n : ℕ} (hn : 101 ≤ n) (hn' : n ≤ 1023) :
    Nat.sqrt n ≤ freshCount n ∧
      n + 48 ≤ 10 * freshCount n + 4 * primeCount (n / 2) +
        2 * primeCount (n / 3) + 2 * primeCount (n / 5) := by
  obtain ⟨a, b, r₀, B₀, hmem, han, hnb⟩ := firstPrimeTable_coverage hn hn'
  obtain ⟨hr, hB, hs, hb⟩ := firstPrimeTable_rows hmem
  have hrn := freshCount_block_lower han hnb
  rw [← hr] at hrn
  refine ⟨(Nat.sqrt_le_sqrt hnb).trans (hs.trans hrn), ?_⟩
  have h₂ := primeCount_mono (Nat.div_le_div_right (c := 2) han)
  have h₃ := primeCount_mono (Nat.div_le_div_right (c := 3) han)
  have h₅ := primeCount_mono (Nat.div_le_div_right (c := 5) han)
  omega

end WeightedPilz.Arithmetic

