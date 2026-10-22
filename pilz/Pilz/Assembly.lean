import Pilz.OddProduct
import Pilz.LargeConclusion
import Pilz.SmallConclusion

/-!
# Pilz's conjecture

The two branches are the paper's finite small-case proof and its
fresh-prime elimination / directed-cut / localized-expansion proof.
All arithmetic and algebraic inputs are constructed in the imported files.
-/

namespace Pilz

/-- The polynomial statement of Theorem A, for every interval length. -/
theorem conjecture (n : ℕ) : ConjectureAt n := by
  by_cases hn : n ≤ 66
  · exact conjectureAt_le_sixty_six n hn
  · exact conjectureAt_large n (by omega)

/-- The equivalent exact minimum-distance statement. -/
theorem distance_interval (n : ℕ) : distance (interval n) = n := by
  apply Nat.le_antisymm
  · have h := distance_le_termWeight (interval n)
    change distance (interval n) ≤ weight (interval n) at h
    simpa only [weight_interval] using h
  · exact (le_distance_iff (interval n) n).mpr (conjecture n)

/-- The original finite-set Pilz conjecture. Members of `A` are positive,
and representations in `oddProduct` are ordered pairs. The `n=0` case is
included harmlessly in addition to the manuscript's positive lengths. -/
theorem pilz_conjecture (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (oddProduct A (Finset.Icc 1 n)).card :=
  oddProduct_interval_lower_bound (conjecture n) A hA hne

end Pilz
