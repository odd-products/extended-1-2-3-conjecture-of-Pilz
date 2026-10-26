import Pilz.PrimeCounts
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold

/-!
The natural-number parameters in the frozen weighted manuscript.
All division is integer division and all square roots are exact integer roots.
The old development supplies only the definitions of prime counts and their
elementary monotonicity proof; no polynomial theorem is used here.
-/

namespace WeightedPilz.Arithmetic

open scoped BigOperators

abbrev primeCount := Pilz.primeCount
abbrev freshCount := Pilz.freshCount

/-- A structurally finite evaluation of the integer square root. -/
def kernelSqrt (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup (fun k => if k * k ≤ n then k else 0)

/-- The computational certificate uses exactly `Nat.sqrt`, via this proved equality. -/
theorem kernelSqrt_eq (n : ℕ) : kernelSqrt n = Nat.sqrt n := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro k hk
    split
    · exact Nat.le_sqrt.mpr ‹k * k ≤ n›
    · exact Nat.zero_le _
  · have h := Finset.le_sup (f := fun k => if k * k ≤ n then k else 0)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sqrt_le_self n)))
    simpa only [if_pos (Nat.sqrt_le n)] using h

/-- A proved constant-depth evaluator on the square-root range used by the tables. -/
def smallSqrt (n : ℕ) : ℕ :=
  if n < 1 then 0 else if n < 4 then 1 else if n < 9 then 2 else
  if n < 16 then 3 else if n < 25 then 4 else if n < 36 then 5 else
  if n < 49 then 6 else if n < 64 then 7 else if n < 81 then 8 else
  if n < 100 then 9 else if n < 121 then 10 else if n < 144 then 11 else
  if n < 169 then 12 else if n < 196 then 13 else if n < 225 then 14 else
  if n < 256 then 15 else Nat.sqrt n

theorem smallSqrt_eq (n : ℕ) : smallSqrt n = Nat.sqrt n := by
  unfold smallSqrt
  by_cases h0 : n < 1
  · rw [if_pos h0]
    exact Nat.eq_sqrt.mpr (by omega)
  · rw [if_neg h0]
    by_cases h1 : n < 4
    · rw [if_pos h1]
      exact Nat.eq_sqrt.mpr (by omega)
    · rw [if_neg h1]
      by_cases h2 : n < 9
      · rw [if_pos h2]
        exact Nat.eq_sqrt.mpr (by omega)
      · rw [if_neg h2]
        by_cases h3 : n < 16
        · rw [if_pos h3]
          exact Nat.eq_sqrt.mpr (by omega)
        · rw [if_neg h3]
          by_cases h4 : n < 25
          · rw [if_pos h4]
            exact Nat.eq_sqrt.mpr (by omega)
          · rw [if_neg h4]
            by_cases h5 : n < 36
            · rw [if_pos h5]
              exact Nat.eq_sqrt.mpr (by omega)
            · rw [if_neg h5]
              by_cases h6 : n < 49
              · rw [if_pos h6]
                exact Nat.eq_sqrt.mpr (by omega)
              · rw [if_neg h6]
                by_cases h7 : n < 64
                · rw [if_pos h7]
                  exact Nat.eq_sqrt.mpr (by omega)
                · rw [if_neg h7]
                  by_cases h8 : n < 81
                  · rw [if_pos h8]
                    exact Nat.eq_sqrt.mpr (by omega)
                  · rw [if_neg h8]
                    by_cases h9 : n < 100
                    · rw [if_pos h9]
                      exact Nat.eq_sqrt.mpr (by omega)
                    · rw [if_neg h9]
                      by_cases h10 : n < 121
                      · rw [if_pos h10]
                        exact Nat.eq_sqrt.mpr (by omega)
                      · rw [if_neg h10]
                        by_cases h11 : n < 144
                        · rw [if_pos h11]
                          exact Nat.eq_sqrt.mpr (by omega)
                        · rw [if_neg h11]
                          by_cases h12 : n < 169
                          · rw [if_pos h12]
                            exact Nat.eq_sqrt.mpr (by omega)
                          · rw [if_neg h12]
                            by_cases h13 : n < 196
                            · rw [if_pos h13]
                              exact Nat.eq_sqrt.mpr (by omega)
                            · rw [if_neg h13]
                              by_cases h14 : n < 225
                              · rw [if_pos h14]
                                exact Nat.eq_sqrt.mpr (by omega)
                              · rw [if_neg h14]
                                by_cases h15 : n < 256
                                · rw [if_pos h15]
                                  exact Nat.eq_sqrt.mpr (by omega)
                                · rw [if_neg h15]

/-- Bounded trial division used only to accelerate finite certificates. -/
def smallPrime (B p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ d : Fin B, 2 ≤ d.val → d.val * d.val ≤ p → ¬ d.val ∣ p

instance (B p : ℕ) : Decidable (smallPrime B p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem smallPrime_iff {B p : ℕ} (hpB : p < B * B) : smallPrime B p ↔ Nat.Prime p := by
  rw [Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun d hd2 hds => ?_⟩
    have hs : Nat.sqrt p < B := Nat.sqrt_lt.mpr hpB
    exact hd ⟨d, by omega⟩ hd2 (Nat.le_sqrt.mp hds)
  · rintro ⟨hp, hd⟩
    exact ⟨hp, fun d hd2 hds => hd d.val hd2 (Nat.le_sqrt.mpr hds)⟩

def kernelPrime (p : ℕ) : Prop :=
  if p < 256 then smallPrime 16 p else
  if p < 1849 then smallPrime 43 p else Nat.Prime p

instance (p : ℕ) : Decidable (kernelPrime p) := by
  unfold kernelPrime
  infer_instance

theorem kernelPrime_iff (p : ℕ) : kernelPrime p ↔ Nat.Prime p := by
  unfold kernelPrime
  split
  · exact smallPrime_iff (by omega)
  · split
    · exact smallPrime_iff (by omega)
    · rfl

theorem primePredicate_eq : Nat.Prime = kernelPrime :=
  funext (fun p => propext (kernelPrime_iff p).symm)

/-- Cost of aggregate fresh degree two outside characteristic two. -/
def squareCost (n : ℕ) : ℕ := freshCount n * (freshCount n + 1) / 2

/-- Primes occurring linearly in the core, strictly above the integer root. -/
def linearCorePrimes (n : ℕ) : Finset ℕ :=
  ((Finset.range (n / 2 + 1)).filter Nat.Prime).filter (Nat.sqrt n < ·)

/-- Sum of the lengths of the linear prime coefficient intervals. -/
def linearCoreCost (n : ℕ) : ℕ := ∑ q ∈ linearCorePrimes n, n / q

/-- Both the middle-interval `d₀` and the large-interval `κ`. -/
def endpoint (n : ℕ) : ℕ := 1 + primeCount (Nat.sqrt n) + linearCoreCost n

/-- Number of linear prime coefficient intervals. -/
def linearCoreCount (n : ℕ) : ℕ := primeCount (n / 2) - primeCount (Nat.sqrt n)

/-- The characteristic-two smooth-core bound in equation (fin-binary-smooth). -/
def binarySmoothBound (n : ℕ) : ℕ :=
  if n ≤ 26 then 7 else if n ≤ 48 then 6 else 8

/-- Characteristic-two `κ` of equation (fin-kappa). -/
def binaryKappa (n : ℕ) : ℕ := binarySmoothBound n + linearCoreCost n

/-- The number of linear terms allowed after reserving the constant and square rows. -/
def affineLinearBudget (n t : ℕ) : ℕ :=
  (n - 1 - endpoint n - squareCost n * t) / freshCount n

/-- The unique-product threshold in the seven-block table. -/
def uniqueThreshold (n : ℕ) : ℕ :=
  n + (n - 2 * freshCount n) * affineLinearBudget n 1 - squareCost n

/-- Kernel calculation after rewriting the proved finite square-root evaluator. -/
macro "weighted_decide" : tactic => `(tactic|
  (try dsimp only [uniqueThreshold, affineLinearBudget, binaryKappa, endpoint,
      linearCoreCost, linearCorePrimes, linearCoreCount, squareCost,
      freshCount, Pilz.freshCount, primeCount, Pilz.primeCount]
   try simp only [primePredicate_eq, ← smallSqrt_eq]
   all_goals decide +kernel))

theorem primeCount_mono {a b : ℕ} (h : a ≤ b) : primeCount a ≤ primeCount b :=
  Pilz.primeCount_mono h

theorem freshCount_le (n : ℕ) : freshCount n ≤ primeCount n := Nat.sub_le _ _

theorem primeCount_half_le (n : ℕ) : primeCount (n / 2) ≤ primeCount n :=
  primeCount_mono (Nat.div_le_self _ _)

theorem freshCount_add_half (n : ℕ) :
    freshCount n + primeCount (n / 2) = primeCount n :=
  Nat.sub_add_cancel (primeCount_half_le n)

theorem freshCount_block_lower {a n b : ℕ} (ha : a ≤ n) (hb : n ≤ b) :
    primeCount a - primeCount (b / 2) ≤ freshCount n := by
  have h₁ := primeCount_mono ha
  have h₂ : primeCount (n / 2) ≤ primeCount (b / 2) :=
    primeCount_mono (Nat.div_le_div_right hb)
  change primeCount a - primeCount (b / 2) ≤ primeCount n - primeCount (n / 2)
  omega

theorem squareCost_mono_of_fresh {a n : ℕ} (h : freshCount a ≤ freshCount n) :
    squareCost a ≤ squareCost n :=
  Nat.div_le_div_right (Nat.mul_le_mul h (Nat.add_le_add_right h 1))

end WeightedPilz.Arithmetic

