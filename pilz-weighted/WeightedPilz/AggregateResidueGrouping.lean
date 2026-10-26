import WeightedPilz.FreshResidueSectors
import WeightedPilz.Frobenius

/-! Group a scalar aggregate expansion by exponent residues. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

namespace FreshData

omit [DecidableEq σ] in
theorem powersInFresh_pow_expChar (S : FreshData σ K) (p : ℕ) [ExpChar K p]
    (P : MvPolynomial σ K) : S.PowersInFresh p (P ^ p) := by
  classical
  intro z hz d hd
  have hs := support_pow_expChar p 1 P
  simp only [pow_one] at hs
  rw [hs] at hd
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
  simp only [scaleExponent_apply]
  exact dvd_mul_right p (b z)

def aggregateResidueRow (S : FreshData σ K) (p : ℕ) (s : Finset ℕ)
    (B : ℕ → MvPolynomial σ K) (j : ℕ) : MvPolynomial σ K :=
  ∑ n ∈ s.filter (fun n => n % p = j), S.freshSum ^ (p * (n / p)) * B n

theorem aggregateResidueRow_powersInFresh (S : FreshData σ K)
    (p : ℕ) [ExpChar K p] (s : Finset ℕ) (B : ℕ → MvPolynomial σ K)
    (hB : ∀ n ∈ s, S.BaseOnly (B n)) (j : ℕ) :
    S.PowersInFresh p (S.aggregateResidueRow p s B j) := by
  apply PowersInFresh.sum
  intro n hn
  have hpow : S.PowersInFresh p (S.freshSum ^ (p * (n / p))) := by
    rw [Nat.mul_comm p (n / p), pow_mul]
    exact S.powersInFresh_pow_expChar p _
  apply hpow.mul
  intro z hz d hd
  rw [hB n (Finset.mem_filter.mp hn).1 z hz d hd]
  exact dvd_zero p

/-- Grouping changes only aggregate exponents. In positive characteristic,
all fresh exponents of each resulting coefficient polynomial are divisible
by `p`, including over an imperfect coefficient field. -/
theorem aggregate_residue_grouping (S : FreshData σ K) (p : ℕ) (hp : 0 < p)
    (s : Finset ℕ) (B : ℕ → MvPolynomial σ K) :
    (∑ n ∈ s, B n * S.freshSum ^ n) =
      ∑ j ∈ Finset.range p, S.freshSum ^ j * S.aggregateResidueRow p s B j := by
  classical
  symm
  calc
    (∑ j ∈ Finset.range p, S.freshSum ^ j * S.aggregateResidueRow p s B j) =
        ∑ j ∈ Finset.range p, ∑ n ∈ s.filter (fun n => n % p = j), S.freshSum ^ n * B n := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [aggregateResidueRow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnj := (Finset.mem_filter.mp hn).2
      rw [← mul_assoc, ← pow_add, ← hnj, Nat.mod_add_div]
    _ = ∑ n ∈ s, S.freshSum ^ n * B n :=
      Finset.sum_fiberwise_of_maps_to (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hp)) _
    _ = ∑ n ∈ s, B n * S.freshSum ^ n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact mul_comm _ _

theorem exists_aggregate_residue_grouping (S : FreshData σ K)
    (p : ℕ) [ExpChar K p] (s : Finset ℕ) (B : ℕ → MvPolynomial σ K)
    (hB : ∀ n ∈ s, S.BaseOnly (B n)) :
    ∃ A : ℕ → MvPolynomial σ K,
      (∀ j < p, S.PowersInFresh p (A j)) ∧
      (∑ n ∈ s, B n * S.freshSum ^ n) = ∑ j ∈ Finset.range p, S.freshSum ^ j * A j := by
  refine ⟨S.aggregateResidueRow p s B, ?_, ?_⟩
  · intro j hj
    exact S.aggregateResidueRow_powersInFresh p s B hB j
  · exact S.aggregate_residue_grouping p (expChar_pos K p) s B

end FreshData

end WeightedPilz
