import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace Pilz

/-- The paper's pi(n), including all primes at most n. -/
def primeCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Nat.Prime).card

/-- The paper's r(n): primes in (n/2, n]. -/
def freshCount (n : ℕ) : ℕ := primeCount n - primeCount (n / 2)

/-- The natural-number form of beta(n) >= n, with 48 moved to the left. -/
def PrimeBudget (n : ℕ) : Prop :=
  n + 48 ≤ 10 * freshCount n + 4 * primeCount (n / 2) +
    2 * primeCount (n / 3) + 2 * primeCount (n / 5)

instance (n : ℕ) : Decidable (PrimeBudget n) := inferInstanceAs (Decidable (_ ≤ _))

theorem primeCount_mono {a b : ℕ} (h : a ≤ b) : primeCount a ≤ primeCount b := by
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩


end Pilz
