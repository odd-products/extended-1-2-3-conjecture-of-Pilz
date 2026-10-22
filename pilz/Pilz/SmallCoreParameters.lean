import Pilz.ComponentProfile
import Mathlib.Data.Nat.Sqrt

/-! The exact numerical parameters used by the paper's finite core tables. -/

namespace Pilz

open scoped BigOperators

def linearCorePrimes (n : ℕ) : Finset ℕ :=
  (primesUpTo (n / 2)).filter (fun p => Nat.sqrt n < p)

def coreBKappa (n : ℕ) : ℕ :=
  if n < 30 then 7 else if n < 32 then 8 else if n < 36 then 7 else
  if n < 40 then 8 else if n < 45 then 7 else if n < 49 then 6 else 8

def coreKappa (n : ℕ) : ℕ :=
  if n ≤ 26 then
    match n with
    | 11 => 7 | 12 => 6 | 13 => 6 | 14 => 8
    | 15 => 9 | 16 => 9 | 17 => 9 | 18 => 11
    | 19 => 11 | 20 => 12 | 21 => 13 | 22 => 15
    | 23 => 15 | 24 => 14 | 25 => 13 | 26 => 15
    | _ => 0
  else coreBKappa n + ∑ p ∈ linearCorePrimes n, n / p

end Pilz
