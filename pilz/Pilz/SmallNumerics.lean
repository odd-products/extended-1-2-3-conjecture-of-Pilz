import Pilz.SmallCoreParameters
import Pilz.Fresh
import Mathlib.Algebra.Group.Nat.Even

/-! Kernel-checked numerical rows for the final finite small-case assembly.
Square roots are certified by the defining square inequalities; no square
root is evaluated by a decision procedure. -/

namespace Pilz

open scoped BigOperators

structure SmallRow where
  r : ℕ
  κ : ℕ
  T : ℕ
  U : ℕ
  M : ℕ
  s : ℕ
  t : ℕ
  deriving DecidableEq, Repr

private def smallPair (n : ℕ) : ℕ × ℕ :=
  match n with
  | 11 => (2, 7) | 12 => (2, 6) | 13 => (3, 6) | 14 => (2, 8)
  | 15 => (2, 9) | 16 => (2, 9) | 17 => (3, 9) | 18 => (3, 11)
  | 19 => (4, 11) | 20 => (4, 12) | 21 => (4, 13) | 22 => (3, 15)
  | 23 => (4, 15) | 24 => (4, 14) | 25 => (4, 13) | 26 => (3, 15)
  | 27 => (3, 14) | 28 => (3, 15) | 29 => (4, 15) | 30 => (4, 16)
  | 31 => (5, 16) | 32 => (5, 15) | 33 => (5, 16) | 34 => (4, 18)
  | 35 => (4, 19) | 36 => (4, 20) | 37 => (5, 20) | 38 => (4, 22)
  | 39 => (4, 23) | 40 => (4, 22) | 41 => (5, 22) | 42 => (5, 23)
  | 43 => (6, 23) | 44 => (6, 24) | 45 => (6, 23) | 46 => (5, 25)
  | 47 => (6, 25) | 48 => (6, 25) | 49 => (6, 21) | 50 => (6, 21)
  | 51 => (6, 22) | 52 => (6, 23) | 53 => (7, 23) | 54 => (7, 23)
  | 55 => (7, 24) | 56 => (7, 24) | 57 => (7, 25) | 58 => (6, 27)
  | 59 => (7, 27) | 60 => (7, 27) | 61 => (8, 27) | 62 => (7, 29)
  | 63 => (7, 29) | 64 => (7, 29) | 65 => (7, 30) | 66 => (7, 31)
  | _ => (0, 0)

/-- A finite candidate for the square root, whose valid range is certified
below using square inequalities. -/
private def smallRoot (n : ℕ) : ℕ :=
  if n < 1 then 0 else if n < 4 then 1 else if n < 9 then 2 else
  if n < 16 then 3 else if n < 25 then 4 else if n < 36 then 5 else
  if n < 49 then 6 else if n < 64 then 7 else if n < 81 then 8 else 0

def SmallRegularIndex (n : ℕ) : Prop :=
  (11 ≤ n ∧ n ≤ 25) ∨ (30 ≤ n ∧ n ≤ 39) ∨
    (41 ≤ n ∧ n ≤ 48) ∨ (53 ≤ n ∧ n ≤ 66)

def SmallRefinedIndex (n : ℕ) : Prop := n = 26 ∨ n = 28 ∨ n = 29

def SmallExceptionalIndex (n : ℕ) : Prop := n = 27 ∨ n = 40 ∨ (49 ≤ n ∧ n ≤ 52)

instance (n : ℕ) : Decidable (SmallRegularIndex n) := by
  unfold SmallRegularIndex
  infer_instance

instance (n : ℕ) : Decidable (SmallRefinedIndex n) := by
  unfold SmallRefinedIndex
  infer_instance

instance (n : ℕ) : Decidable (SmallExceptionalIndex n) := by
  unfold SmallExceptionalIndex
  infer_instance

/-- The finite row, with the improved capacity 13 in the three refined
rows 26,28,29. All fields are ordinary computable natural numbers. -/
def smallRow (n : ℕ) : SmallRow :=
  let r := (smallPair n).1
  let κ := (smallPair n).2
  let T := n - 1 - (if n % 2 = 0 then 1 else 0)
  let U := (T - κ) / r
  let s := smallRoot n
  let t := smallRoot (n / 2)
  let M := if SmallRefinedIndex n then 2 * s + t else
    if U ≤ 3 then U * s else 3 * s + t
  ⟨r, κ, T, U, M, s, t⟩

private def computedCoreKappa (n : ℕ) : ℕ :=
  if n ≤ 26 then
    match n with
    | 11 => 7 | 12 => 6 | 13 => 6 | 14 => 8
    | 15 => 9 | 16 => 9 | 17 => 9 | 18 => 11
    | 19 => 11 | 20 => 12 | 21 => 13 | 22 => 15
    | 23 => 15 | 24 => 14 | 25 => 13 | 26 => 15
    | _ => 0
  else coreBKappa n + ∑ p ∈ (primesUpTo (n / 2)).filter (fun p => smallRoot n < p), n / p

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem fresh_certificate : ∀ n : Fin 67, 11 ≤ n.val →
    (freshPrimes n.val).card = (smallRow n.val).r := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem kappa_certificate : ∀ n : Fin 67, 11 ≤ n.val →
    (smallRow n.val).κ = computedCoreKappa n.val := by decide

private theorem square_certificate : ∀ n : Fin 67, 11 ≤ n.val →
    (smallRow n.val).s * (smallRow n.val).s ≤ n.val ∧
      n.val < ((smallRow n.val).s + 1) * ((smallRow n.val).s + 1) ∧
      (smallRow n.val).t * (smallRow n.val).t ≤ n.val / 2 ∧
      n.val / 2 < ((smallRow n.val).t + 1) * ((smallRow n.val).t + 1) := by decide

private theorem arithmetic_certificate : ∀ n : Fin 67, 11 ≤ n.val →
    0 < (smallRow n.val).r ∧ 2 ≤ (smallRow n.val).κ ∧ (smallRow n.val).U ≤ 4 ∧
      (smallRow n.val).T ≤ (smallRow n.val).r * (smallRow n.val).κ := by decide

theorem smallRow_fresh_card (n : ℕ) (hn : 11 ≤ n) (hhi : n ≤ 66) :
    (freshPrimes n).card = (smallRow n).r := fresh_certificate ⟨n, by omega⟩ hn

theorem smallRow_sqrt (n : ℕ) (hn : 11 ≤ n) (hhi : n ≤ 66) :
    Nat.sqrt n = (smallRow n).s := by
  have hs := square_certificate ⟨n, by omega⟩ hn
  exact (Nat.eq_sqrt.mpr ⟨hs.1, hs.2.1⟩).symm

theorem smallRow_half_sqrt (n : ℕ) (hn : 11 ≤ n) (hhi : n ≤ 66) :
    Nat.sqrt (n / 2) = (smallRow n).t := by
  have hs := square_certificate ⟨n, by omega⟩ hn
  exact (Nat.eq_sqrt.mpr ⟨hs.2.2.1, hs.2.2.2⟩).symm

theorem smallRow_coreKappa (n : ℕ) (hn : 11 ≤ n) (hhi : n ≤ 66) :
    (smallRow n).κ = coreKappa n := by
  have hκ := kappa_certificate ⟨n, by omega⟩ hn
  have hs := smallRow_sqrt n hn hhi
  change Nat.sqrt n = smallRoot n at hs
  have heq : coreKappa n = computedCoreKappa n := by
    unfold coreKappa computedCoreKappa linearCorePrimes
    rw [hs]
    rfl
  exact hκ.trans heq.symm

theorem smallRow_r_pos (n : ℕ) (hn : 11 ≤ n) (hhi : n ≤ 66) :
    0 < (smallRow n).r := (arithmetic_certificate ⟨n, by omega⟩ hn).1

theorem smallRow_kappa_pos (n : ℕ) (hn : 11 ≤ n) (hhi : n ≤ 66) :
    2 ≤ (smallRow n).κ := (arithmetic_certificate ⟨n, by omega⟩ hn).2.1

theorem smallRow_U_le_four (n : ℕ) (hn : 11 ≤ n) (hhi : n ≤ 66) :
    (smallRow n).U ≤ 4 := (arithmetic_certificate ⟨n, by omega⟩ hn).2.2.1

theorem smallRow_bound (n : ℕ) (_hn : 11 ≤ n) (_hhi : n ≤ 66)
    (m : ℕ) (hm : m < n) (hpar : Even n → Even m) : m ≤ (smallRow n).T := by
  change m ≤ n - 1 - (if n % 2 = 0 then 1 else 0)
  by_cases heven : Even n
  · have hnmod : n % 2 = 0 := Nat.even_iff.mp heven
    have hmmod : m % 2 = 0 := Nat.even_iff.mp (hpar heven)
    rw [if_pos hnmod]
    omega
  · have hnmod : n % 2 ≠ 0 := fun h => heven (Nat.even_iff.mpr h)
    rw [if_neg hnmod]
    omega

theorem smallRow_reduce (n : ℕ) (hn : 11 ≤ n) (hhi : n ≤ 66)
    (m u : ℕ) (_hu : 0 < u) (hru : (smallRow n).r * u < m)
    (_hhalf : 2 * u ≤ m) (hm : m ≤ (smallRow n).T) :
    u < (smallRow n).κ ∧ ((smallRow n).r * u + (smallRow n).κ ≤ m → u ≤ (smallRow n).U) := by
  have hnum : (smallRow n).T ≤ (smallRow n).r * (smallRow n).κ :=
    (arithmetic_certificate ⟨n, by omega⟩ hn).2.2.2
  have hrpos := smallRow_r_pos n hn hhi
  constructor
  · by_contra hnot
    have hmul := Nat.mul_le_mul_left (smallRow n).r (Nat.le_of_not_gt hnot)
    omega
  · intro hbudget
    have hmul : (smallRow n).r * u ≤ (smallRow n).T - (smallRow n).κ := by omega
    change u ≤ ((smallRow n).T - (smallRow n).κ) / (smallRow n).r
    apply (Nat.le_div_iff_mul_le hrpos).mpr
    simpa only [Nat.mul_comm] using hmul

private theorem regular_certificate : ∀ n : Fin 67, SmallRegularIndex n.val →
    min (smallRow n.val).U 3 * (smallRow n.val).s ≤ (smallRow n.val).M ∧
      ((smallRow n.val).U = 4 → 3 * (smallRow n.val).s + (smallRow n.val).t ≤ (smallRow n.val).M) ∧
      2 * (smallRow n.val).M ≤ n.val := by decide

private theorem refined_certificate : ∀ n : Fin 67, SmallRefinedIndex n.val →
    (smallRow n.val).U ≤ 3 ∧ min (smallRow n.val).U 2 * (smallRow n.val).s ≤ (smallRow n.val).M ∧
      ((smallRow n.val).U = 3 → 2 * (smallRow n.val).s + (smallRow n.val).t ≤ (smallRow n.val).M) ∧
      2 * (smallRow n.val).M ≤ n.val := by decide

theorem smallRow_regular (n : ℕ) (hreg : SmallRegularIndex n) :
    min (smallRow n).U 3 * Nat.sqrt n ≤ (smallRow n).M ∧
      ((smallRow n).U = 4 → 3 * Nat.sqrt n + Nat.sqrt (n / 2) ≤ (smallRow n).M) ∧
      2 * (smallRow n).M ≤ n := by
  have hlo : 11 ≤ n := by unfold SmallRegularIndex at hreg; omega
  have hhi : n ≤ 66 := by unfold SmallRegularIndex at hreg; omega
  rw [smallRow_sqrt n hlo hhi, smallRow_half_sqrt n hlo hhi]
  exact regular_certificate ⟨n, by omega⟩ hreg

theorem smallRow_refined (n : ℕ) (href : SmallRefinedIndex n) :
    (smallRow n).U ≤ 3 ∧ min (smallRow n).U 2 * Nat.sqrt n ≤ (smallRow n).M ∧
      ((smallRow n).U = 3 → 2 * Nat.sqrt n + Nat.sqrt (n / 2) ≤ (smallRow n).M) ∧
      2 * (smallRow n).M ≤ n := by
  have hlo : 11 ≤ n := by unfold SmallRefinedIndex at href; omega
  have hhi : n ≤ 66 := by unfold SmallRefinedIndex at href; omega
  rw [smallRow_sqrt n hlo hhi, smallRow_half_sqrt n hlo hhi]
  exact refined_certificate ⟨n, by omega⟩ href

def smallMThree (n : ℕ) : ℕ :=
  if 26 ≤ n ∧ n ≤ 29 then 2 * (smallRow n).s + (smallRow n).t else 3 * (smallRow n).s

def smallMFour (n : ℕ) : ℕ := 3 * (smallRow n).s + (smallRow n).t

def smallProductBound (n : ℕ) : ℕ := if n = 27 then 36 else if n = 40 then 44 else 56

private theorem exception_certificate : ∀ n : Fin 67, SmallExceptionalIndex n.val →
    (smallRow n.val).U = 4 ∧
      (3 * (smallRow n.val).s ≤ smallMThree n.val ∨
        (26 ≤ n.val ∧ n.val ≤ 29 ∧ 2 * (smallRow n.val).s + (smallRow n.val).t ≤ smallMThree n.val)) ∧
      3 * (smallRow n.val).s + (smallRow n.val).t ≤ smallMFour n.val ∧
      2 * smallMThree n.val ≤ n.val ∧
      (smallRow n.val).T + 2 * smallMFour n.val < 2 * n.val + 4 * (smallRow n.val).r ∧
      smallMFour n.val ≤ n.val ∧ n.val ≤ smallProductBound n.val ∧
      2 * smallMFour n.val ≤ smallProductBound n.val := by decide

theorem smallRow_exception (n : ℕ) (hex : SmallExceptionalIndex n) :
    (smallRow n).U = 4 ∧
      (3 * Nat.sqrt n ≤ smallMThree n ∨
        (26 ≤ n ∧ n ≤ 29 ∧ 2 * Nat.sqrt n + Nat.sqrt (n / 2) ≤ smallMThree n)) ∧
      3 * Nat.sqrt n + Nat.sqrt (n / 2) ≤ smallMFour n ∧
      2 * smallMThree n ≤ n ∧
      (smallRow n).T + 2 * smallMFour n < 2 * n + 4 * (smallRow n).r ∧
      smallMFour n ≤ n ∧ n ≤ smallProductBound n ∧ 2 * smallMFour n ≤ smallProductBound n := by
  have hlo : 11 ≤ n := by unfold SmallExceptionalIndex at hex; omega
  have hhi : n ≤ 66 := by unfold SmallExceptionalIndex at hex; omega
  rw [smallRow_sqrt n hlo hhi, smallRow_half_sqrt n hlo hhi]
  exact exception_certificate ⟨n, by omega⟩ hex

theorem smallRow_index_cases (n : ℕ) (hn : 11 ≤ n) (hhi : n ≤ 66) :
    SmallRegularIndex n ∨ SmallRefinedIndex n ∨ SmallExceptionalIndex n := by
  unfold SmallRegularIndex SmallRefinedIndex SmallExceptionalIndex
  omega

theorem smallRow_refined_range (n : ℕ) (href : SmallRefinedIndex n) : 26 ≤ n ∧ n ≤ 29 := by
  unfold SmallRefinedIndex at href
  omega

theorem smallRow_exception_cases (n : ℕ) (hex : SmallExceptionalIndex n) :
    n = 27 ∨ n = 40 ∨ (49 ≤ n ∧ n ≤ 52) := hex

end Pilz
