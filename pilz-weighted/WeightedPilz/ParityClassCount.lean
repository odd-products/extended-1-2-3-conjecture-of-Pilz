import WeightedPilz.ParityCore
import WeightedPilz.ParityCombinatorics

/-! Unpaired occupied parity classes under a translation with a nonzero bit. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace WeightedPilz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem parity_unpaired_card_lower {σ : Type*} [DecidableEq σ]
    (A : Finset (σ →₀ ℕ)) (ν : σ →₀ ℕ)
    (hA : ∀ α ∈ A, residueExponent 2 α = α) (p : σ) (hν : ν p % 2 = 1) :
    A.card ≤ (A.filter (fun α => residueExponent 2 (α + ν) ∉ A)).card +
      2 * (A.filter (fun α => α p = 1)).card := by
  classical
  apply unpaired_card_lower_of_involutive_on A (fun α => residueExponent 2 (α + ν))
  · intro α hα
    ext i
    have hi := congrArg (fun e : σ →₀ ℕ => e i) (hA α hα)
    simp only [residueExponent_apply, Finsupp.add_apply] at hi ⊢
    omega
  · intro α hα
    have hi := congrArg (fun e : σ →₀ ℕ => e p) (hA α hα)
    simp only [residueExponent_apply, Finsupp.add_apply] at hi ⊢
    omega

theorem squarefree_factorization_bit_iff {s p : ℕ} (hs : Squarefree s) (hp : p.Prime) :
    s.factorization p = 1 ↔ p ∣ s := by
  rw [hp.dvd_iff_one_le_factorization hs.ne_zero]
  have h := hs.natFactorization_le_one p
  omega

theorem squarefree_parity_bit_card (n p : ℕ) (hp : p.Prime) :
    (((Arithmetic.squarefreeNumbers n).image Nat.factorization).filter
      (fun α => α p = 1)).card =
        ((Arithmetic.squarefreeNumbers n).filter (fun s => p ∣ s)).card := by
  classical
  have heq : (((Arithmetic.squarefreeNumbers n).image Nat.factorization).filter
      (fun α => α p = 1)) =
        (((Arithmetic.squarefreeNumbers n).filter (fun s => p ∣ s)).image Nat.factorization) := by
    ext α
    constructor
    · intro h
      obtain ⟨hmem, hbit⟩ := Finset.mem_filter.mp h
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hmem
      have hsq := (Arithmetic.mem_squarefreeNumbers n s).mp hs
      exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr
        ⟨hs, (squarefree_factorization_bit_iff hsq.2.2 hp).mp hbit⟩, rfl⟩
    · intro h
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hs, hpdiv⟩ := Finset.mem_filter.mp hs
      have hsq := (Arithmetic.mem_squarefreeNumbers n s).mp hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨s, hs, rfl⟩,
        (squarefree_factorization_bit_iff hsq.2.2 hp).mpr hpdiv⟩
  rw [heq]
  apply Finset.card_image_of_injOn
  intro s hs t ht hst
  have hsq := (Arithmetic.mem_squarefreeNumbers n s).mp (Finset.mem_filter.mp hs).1
  have htq := (Arithmetic.mem_squarefreeNumbers n t).mp (Finset.mem_filter.mp ht).1
  exact Nat.factorization_inj hsq.2.2.ne_zero htq.2.2.ne_zero hst

theorem squarefree_parity_unpaired_count (n p : ℕ) (hp : p.Prime)
    (ν : ℕ →₀ ℕ) (hν : ν p % 2 = 1) :
    (Arithmetic.squarefreeNumbers n).card ≤
      (((Arithmetic.squarefreeNumbers n).image Nat.factorization).filter
        (fun α => residueExponent 2 (α + ν) ∉
          (Arithmetic.squarefreeNumbers n).image Nat.factorization)).card +
        2 * ((Arithmetic.squarefreeNumbers n).filter (fun s => p ∣ s)).card := by
  classical
  have h := parity_unpaired_card_lower
    ((Arithmetic.squarefreeNumbers n).image Nat.factorization) ν (by
      intro α hα
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hα
      exact residue_factorization_squarefree ((Arithmetic.mem_squarefreeNumbers n s).mp hs).2.2)
    p hν
  rw [squarefree_parity_bit_card n p hp] at h
  have hinj : Set.InjOn Nat.factorization (Arithmetic.squarefreeNumbers n : Set ℕ) := by
    intro s hs t ht hst
    exact Nat.factorization_inj
      ((Arithmetic.mem_squarefreeNumbers n s).mp hs).2.2.ne_zero
      ((Arithmetic.mem_squarefreeNumbers n t).mp ht).2.2.ne_zero hst
  rwa [Finset.card_image_of_injOn hinj] at h

/-- Integer-labelled occupied classes whose translate is unoccupied. -/
def unpairedSquarefree (n : ℕ) (ν : ℕ →₀ ℕ) : Finset ℕ :=
  (Arithmetic.squarefreeNumbers n).filter (fun s =>
    residueExponent 2 (s.factorization + ν) ∉
      (Arithmetic.squarefreeNumbers n).image Nat.factorization)

theorem unpairedSquarefree_count (n p : ℕ) (hp : p.Prime)
    (ν : ℕ →₀ ℕ) (hν : ν p % 2 = 1) :
    (Arithmetic.squarefreeNumbers n).card ≤ (unpairedSquarefree n ν).card +
      2 * ((Arithmetic.squarefreeNumbers n).filter (fun s => p ∣ s)).card := by
  classical
  have h := squarefree_parity_unpaired_count n p hp ν hν
  have hcard :
      (((Arithmetic.squarefreeNumbers n).image Nat.factorization).filter
        (fun α => residueExponent 2 (α + ν) ∉
          (Arithmetic.squarefreeNumbers n).image Nat.factorization)).card =
        (unpairedSquarefree n ν).card := by
    rw [Finset.filter_image]
    apply Finset.card_image_of_injOn
    intro s hs t ht hst
    have hsq := (Arithmetic.mem_squarefreeNumbers n s).mp (Finset.mem_filter.mp hs).1
    have htq := (Arithmetic.mem_squarefreeNumbers n t).mp (Finset.mem_filter.mp ht).1
    exact Nat.factorization_inj hsq.2.2.ne_zero htq.2.2.ne_zero hst
  rwa [hcard] at h

theorem unpairedSquarefree_odd_prime_bounds (ν : ℕ →₀ ℕ) (p : ℕ)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hν : ν p % 2 = 1) :
    9 ≤ (unpairedSquarefree 27 ν).card ∧
    9 ≤ (unpairedSquarefree 28 ν).card ∧
    11 ≤ (unpairedSquarefree 36 ν).card := by
  have h27 := unpairedSquarefree_count 27 p hp ν hν
  have h28 := unpairedSquarefree_count 28 p hp ν hν
  have h36 := unpairedSquarefree_count 36 p hp ν hν
  obtain ⟨hc27, hc28, hc36⟩ := Arithmetic.parity_pair_squarefree_counts
  obtain ⟨hp27, hp28, hp36⟩ := Arithmetic.parity_pair_odd_prime_counts hp hp3
  omega

theorem unpairedSquarefree_eq_of_nonprime (n : ℕ) (ν : ℕ →₀ ℕ) (p : ℕ)
    (hp : ¬ p.Prime) (hν : ν p % 2 = 1) :
    unpairedSquarefree n ν = Arithmetic.squarefreeNumbers n := by
  classical
  apply Finset.filter_eq_self.mpr
  intro s hs hmem
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
  have hi := congrArg (fun α : ℕ →₀ ℕ => α p) heq
  simp only [residueExponent_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_prime _ hp, zero_add, hν] at hi
  omega

end WeightedPilz
