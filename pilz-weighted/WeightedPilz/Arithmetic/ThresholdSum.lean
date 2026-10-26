import Pilz.ComponentCounts
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel

/-! The finite threshold-sum identity `arith:eq:threshold-sum`.
The cost may decrease: its differences live in an additive group. The result
holds for every finite set of excluded divisors, hence in particular for the
primes at most any chosen support prime. -/

namespace WeightedPilz.Arithmetic
open scoped BigOperators

private theorem telescope_cost {A : Type*} [AddCommGroup A] (f : ℕ → A) :
    ∀ k : ℕ, 1 ≤ k → f 1 + (∑ j ∈ Finset.Icc 2 k, (f j - f (j - 1))) = f k := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst k
      simp
    have hk1 : 1 ≤ k := by omega
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1)]
    simp only [Nat.add_sub_cancel]
    rw [← add_assoc, ih hk1]
    abel

/-- General additive form of `arith:eq:threshold-sum`, valid also at `n = 0`. -/
theorem rough_threshold_sum {A : Type*} [AddCommGroup A]
    (T : Finset ℕ) (n : ℕ) (f : ℕ → A) :
    (∑ b ∈ Pilz.roughNumbers T n, f (n / b)) =
      Pilz.roughCount T n • f 1 +
        ∑ j ∈ Finset.Icc 2 n, Pilz.roughCount T (n / j) • (f j - f (j - 1)) := by
  classical
  have hrow (b : ℕ) (hb : b ∈ Pilz.roughNumbers T n) :
      f (n / b) = f 1 + ∑ j ∈ Finset.Icc 2 n,
        if j ≤ n / b then f j - f (j - 1) else 0 := by
    obtain ⟨hbpos, hbn, _⟩ := (Pilz.mem_roughNumbers T n b).mp hb
    have hk : 1 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by simpa using hbn)
    have hkn : n / b ≤ n := Nat.div_le_self n b
    have hfilter : (Finset.Icc 2 n).filter (fun j => j ≤ n / b) =
        Finset.Icc 2 (n / b) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter, hfilter]
    exact (telescope_cost f (n / b) hk).symm
  calc
    (∑ b ∈ Pilz.roughNumbers T n, f (n / b)) =
        ∑ b ∈ Pilz.roughNumbers T n, (f 1 + ∑ j ∈ Finset.Icc 2 n,
          if j ≤ n / b then f j - f (j - 1) else 0) :=
      Finset.sum_congr rfl hrow
    _ = Pilz.roughCount T n • f 1 + ∑ j ∈ Finset.Icc 2 n,
        ∑ b ∈ Pilz.roughNumbers T n,
          if j ≤ n / b then f j - f (j - 1) else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_comm]
      rfl
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter, Finset.sum_const,
        Pilz.card_roughNumbers_index_ge T n j (by have := (Finset.mem_Icc.mp hj).1; omega)]

/-- The manuscript's displayed signed counting formula. -/
theorem threshold_sum (T : Finset ℕ) (n : ℕ) (f : ℕ → ℤ) :
    (∑ b ∈ Pilz.roughNumbers T n, f (n / b)) =
      f 1 * (Pilz.roughCount T n : ℤ) + ∑ j ∈ Finset.Icc 2 n,
        (f j - f (j - 1)) * (Pilz.roughCount T (n / j) : ℤ) := by
  simpa only [nsmul_eq_mul, mul_comm] using rough_threshold_sum T n f

/-- Taking `T` to be all primes through `q` gives the exact stated rough-part sum. -/
theorem threshold_sum_primes (q n : ℕ) (f : ℕ → ℤ) :
    (∑ b ∈ Pilz.roughNumbers ((Finset.range (q + 1)).filter Nat.Prime) n, f (n / b)) =
      f 1 * (Pilz.roughCount ((Finset.range (q + 1)).filter Nat.Prime) n : ℤ) +
      ∑ j ∈ Finset.Icc 2 n, (f j - f (j - 1)) *
        (Pilz.roughCount ((Finset.range (q + 1)).filter Nat.Prime) (n / j) : ℤ) :=
  threshold_sum _ n f

end WeightedPilz.Arithmetic
