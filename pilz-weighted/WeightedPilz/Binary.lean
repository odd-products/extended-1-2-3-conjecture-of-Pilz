import WeightedPilz.Convolution
import Pilz.OddProduct
import Mathlib.Algebra.Field.ZMod

/-!
# The original symmetric-difference formulation

This file reuses only the audited parity encoding in `Pilz.OddProduct`, whose
imports do not contain the unweighted interval theorem. The lower bound below
is stated with the weighted field theorem at the given index as a hypothesis.
That hypothesis is discharged unconditionally in `WeightedPilz.FieldTheorem`,
whose `weighted_symmetric_difference` is the full Extended 1-2-3 Conjecture.
-/

noncomputable section

namespace WeightedPilz

open scoped BigOperators

@[simp] theorem binary_interval_eq (n : ℕ) :
    interval n (fun _ : ℕ => (1 : ZMod 2)) = Pilz.interval n := rfl

/-- The old unweighted polynomial interface is the constant-weight specialization. -/
theorem binary_intervalBound_iff (n : ℕ) :
    IntervalBound n (fun _ : ℕ => (1 : ZMod 2)) ↔ Pilz.ConjectureAt n := Iff.rfl

/-- The finite set `{a,2a,...,na}`. -/
def dilatedInterval (n a : ℕ) : Finset ℕ := (Finset.Icc 1 n).image (a * ·)

/-- The iterated symmetric difference: membership means appearing in an odd
number of the sets `{a,2a,...,na}` indexed by `a ∈ A`. -/
def intervalSymmetricDifference (n : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (A.biUnion (dilatedInterval n)).filter fun m =>
    Odd ((A.filter fun a => m ∈ dilatedInterval n a).card)

theorem mem_intervalSymmetricDifference (n : ℕ) (A : Finset ℕ) (m : ℕ) :
    m ∈ intervalSymmetricDifference n A ↔
      Odd ((A.filter fun a => m ∈ dilatedInterval n a).card) := by
  classical
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).2
  · intro hm
    apply Finset.mem_filter.mpr
    refine ⟨?_, hm⟩
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hm.pos
    exact Finset.mem_biUnion.mpr ⟨a, (Finset.mem_filter.mp ha).1,
      (Finset.mem_filter.mp ha).2⟩

/-- Positive interval progressions have one representation for each participating input. -/
theorem representationCount_interval (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (m : ℕ) :
    Pilz.representationCount A (Finset.Icc 1 n) m =
      (A.filter fun a => m ∈ dilatedInterval n a).card := by
  classical
  unfold Pilz.representationCount
  apply Finset.card_bij (fun ab _ => ab.1)
  · intro ab hab
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨ha, Finset.mem_image.mpr ⟨ab.2, hb, he⟩⟩
  · intro ab hab cd hcd hac
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hab
    obtain ⟨_, hce⟩ := Finset.mem_filter.mp hcd
    apply Prod.ext hac
    apply Nat.eq_of_mul_eq_mul_left (hA ab.1 (Finset.mem_product.mp hp).1)
    rw [he, hac, hce]
  · intro a ha
    obtain ⟨ha, hm⟩ := Finset.mem_filter.mp ha
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hm
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩

theorem intervalSymmetricDifference_eq_oddProduct (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) :
    intervalSymmetricDifference n A = Pilz.oddProduct A (Finset.Icc 1 n) := by
  ext m
  rw [mem_intervalSymmetricDifference, Pilz.mem_oddProduct_iff,
    representationCount_interval n A hA m]

@[simp] theorem intervalSymmetricDifference_singleton (n a : ℕ) :
    intervalSymmetricDifference n {a} = dilatedInterval n a := by
  classical
  ext m
  rw [mem_intervalSymmetricDifference]
  simp only [Finset.filter_singleton]
  by_cases hm : m ∈ dilatedInterval n a <;> simp [hm]

/-- A singleton input attains equality in the original finite-set statement. -/
theorem symmetric_difference_singleton_sharpness (n a : ℕ) (ha : 0 < a) :
    (intervalSymmetricDifference n {a}).card = n := by
  rw [intervalSymmetricDifference_singleton, dilatedInterval]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left ha h)]
  simp

/-- The weighted field bound over `F₂`, specialized to unit weights, gives
the original symmetric-difference inequality. -/
theorem symmetric_difference_bound_of_intervalBound {n : ℕ}
    (h : IntervalBound n (fun _ : ℕ => (1 : ZMod 2)))
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (intervalSymmetricDifference n A).card := by
  rw [intervalSymmetricDifference_eq_oddProduct n A hA]
  exact Pilz.oddProduct_interval_lower_bound ((binary_intervalBound_iff n).mp h) A hA hne

end WeightedPilz
