import WeightedPilz.Arithmetic.UniqueProducts
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated

/-! Small finite certificates for the four square times binomial bounds.
The witnesses are unique products in the core, and every coordinate-zero
slice contains enough witnesses. Every computation is checked by `decide`.
-/

namespace WeightedPilz.Arithmetic

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def smallSquareWitnesses : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 33, 35, 39, 49, 55, 77, 117, 121, 125, 128,
   143, 169, 175, 256, 273, 294, 325, 338, 375, 440, 462, 525, 572,
   576, 625, 676}

def fortySquareWitnesses : Finset ℕ :=
  {1, 119, 125, 143, 169, 289, 361, 363, 625, 748, 1152, 1520, 1521}

private theorem mem_uniqueProducts_of_divisors_card {n m : ℕ}
    (h : (representationDivisors n m).card = 1) : m ∈ uniqueProducts n := by
  have hr : (representations n m).card = 1 := (representations_card_eq n m).trans h
  exact Finset.mem_filter.mpr
    ⟨representations_nonempty_iff.mp (Finset.card_pos.mp (by omega)), hr⟩

private theorem small_unique_26 : ∀ m ∈ smallSquareWitnesses,
    (representationDivisors 26 m).card = 1 := by decide +kernel

private theorem small_unique_27 : ∀ m ∈ smallSquareWitnesses,
    (representationDivisors 27 m).card = 1 := by decide +kernel

private theorem small_unique_28 : ∀ m ∈ smallSquareWitnesses,
    (representationDivisors 28 m).card = 1 := by decide +kernel

private theorem forty_unique : ∀ m ∈ fortySquareWitnesses,
    (representationDivisors 40 m).card = 1 := by decide +kernel

theorem smallSquareWitnesses_subset (n : ℕ) (hn : n = 26 ∨ n = 27 ∨ n = 28) :
    smallSquareWitnesses ⊆ uniqueProducts n := by
  intro m hm
  apply mem_uniqueProducts_of_divisors_card
  rcases hn with rfl | rfl | rfl
  · exact small_unique_26 m hm
  · exact small_unique_27 m hm
  · exact small_unique_28 m hm

theorem fortySquareWitnesses_subset : fortySquareWitnesses ⊆ uniqueProducts 40 := by
  intro m hm
  exact mem_uniqueProducts_of_divisors_card (forty_unique m hm)

private theorem zero_slice_bound (S V : Finset ℕ) (N : ℕ)
    (hs : ∀ m ∈ S, m.factorization.support ⊆ V)
    (hc : ∀ j ∈ V, N ≤ (S.filter (fun m => m.factorization j = 0)).card)
    (hN : N ≤ S.card) (j : ℕ) :
    N ≤ (S.filter (fun m => m.factorization j = 0)).card := by
  by_cases hj : j ∈ V
  · exact hc j hj
  · have heq : S.filter (fun m => m.factorization j = 0) = S := by
      apply Finset.filter_eq_self.mpr
      intro m hm
      apply Finsupp.notMem_support_iff.mp
      exact fun h => hj (hs m hm h)
    rwa [heq]

private theorem support_subset_of_divisor_certificate (S V : Finset ℕ) (D : ℕ)
    (hV : ∀ p ∈ V, p.Prime)
    (hc : ∀ m ∈ S, m ∣ (V.prod id) ^ D) :
    ∀ m ∈ S, m.factorization.support ⊆ V := by
  intro m hm j hj
  change j ∈ m.primeFactors at hj
  have hp := Nat.prime_of_mem_primeFactors hj
  have hdvd := hp.dvd_of_dvd_pow ((Nat.dvd_of_mem_primeFactors hj).trans (hc m hm))
  obtain ⟨p, hpV, hjp⟩ := (hp.prime.dvd_finset_prod_iff id).mp hdvd
  have heq : j = p := ((hV p hpV).eq_one_or_self_of_dvd j hjp).resolve_left hp.ne_one
  exact heq.symm ▸ hpV

theorem smallSquareWitnesses_zero_slice (j : ℕ) :
    22 ≤ (smallSquareWitnesses.filter (fun m => m.factorization j = 0)).card := by
  apply zero_slice_bound smallSquareWitnesses {2, 3, 5, 7, 11, 13} 22
  · apply support_subset_of_divisor_certificate _ _ 8
    · decide +kernel
    · decide +kernel
  · simp only [Nat.factorization_eq_zero_iff]
    decide +kernel
  · decide +kernel

theorem fortySquareWitnesses_zero_slice (j : ℕ) :
    10 ≤ (fortySquareWitnesses.filter (fun m => m.factorization j = 0)).card := by
  apply zero_slice_bound fortySquareWitnesses {2, 3, 5, 7, 11, 13, 17, 19} 10
  · apply support_subset_of_divisor_certificate _ _ 8
    · decide +kernel
    · decide +kernel
  · simp only [Nat.factorization_eq_zero_iff]
    decide +kernel
  · decide +kernel

end WeightedPilz.Arithmetic
