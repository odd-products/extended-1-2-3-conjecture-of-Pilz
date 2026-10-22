import Density.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Tauto

noncomputable section

namespace PilzDensity

def lowerSlice (A : Finset ℕ) (p : ℕ) : Finset ℕ :=
  A.filter (fun a => ¬ p ∣ a)

def upperSlice (A : Finset ℕ) (p : ℕ) : Finset ℕ :=
  A.filter (fun a => p ∣ a)

theorem slice_union (A : Finset ℕ) (p : ℕ) :
    lowerSlice A p ∪ upperSlice A p = A := by
  ext a
  simp only [lowerSlice, upperSlice, Finset.mem_union, Finset.mem_filter]
  tauto

theorem slice_disjoint (A : Finset ℕ) (p : ℕ) :
    Disjoint (lowerSlice A p) (upperSlice A p) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  exact (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

theorem lowerSlice_subset (A : Finset ℕ) (p : ℕ) : lowerSlice A p ⊆ A :=
  Finset.filter_subset _ _

theorem upperSlice_subset (A : Finset ℕ) (p : ℕ) : upperSlice A p ⊆ A :=
  Finset.filter_subset _ _

theorem lowerSlice_nonempty (A : Finset ℕ) (p : ℕ) (hp : Nat.Prime p)
    (hgcd : A.gcd id = 1) : (lowerSlice A p).Nonempty := by
  by_contra h
  have hall : ∀ a ∈ A, p ∣ a := by
    intro a ha
    by_contra hpa
    exact h ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩⟩
  have hdvd : p ∣ A.gcd id := Finset.dvd_gcd_iff.mpr hall
  rw [hgcd] at hdvd
  exact hp.not_dvd_one hdvd

theorem upperSlice_nonempty (A : Finset ℕ) (p : ℕ)
    (h : ∃ a ∈ A, p ∣ a) : (upperSlice A p).Nonempty := by
  obtain ⟨a, ha, hp⟩ := h
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, hp⟩⟩

theorem lowerSlice_card_lt (A : Finset ℕ) (p : ℕ)
    (h : (upperSlice A p).Nonempty) : (lowerSlice A p).card < A.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨lowerSlice_subset A p, ?_⟩
  intro heq
  obtain ⟨a, ha⟩ := h
  have hb : a ∈ lowerSlice A p := heq.symm ▸ upperSlice_subset A p ha
  exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2

theorem upperSlice_card_lt (A : Finset ℕ) (p : ℕ)
    (h : (lowerSlice A p).Nonempty) : (upperSlice A p).card < A.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨upperSlice_subset A p, ?_⟩
  intro heq
  obtain ⟨a, ha⟩ := h
  have hb : a ∈ upperSlice A p := heq.symm ▸ lowerSlice_subset A p ha
  exact (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

theorem exists_prime_divisor_of_one_lt_card (A : Finset ℕ)
    (hcard : 1 < A.card) : ∃ p, Nat.Prime p ∧ ∃ a ∈ A, p ∣ a := by
  have hnot : ¬ A ⊆ {1} := by
    intro h
    have := Finset.card_le_card h
    simpa using (not_le_of_gt hcard) (by simpa using this)
  obtain ⟨a, ha, hane⟩ := Finset.not_subset.mp hnot
  have hne : a ≠ 1 := by simpa using hane
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne
  exact ⟨p, hp, a, ha, hdvd⟩

theorem powers_two_of_no_odd_prime (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a)
    (hodd : ¬ ∃ p, Nat.Prime p ∧ 3 ≤ p ∧ ∃ a ∈ A, p ∣ a) :
    ∀ a ∈ A, ∃ k : ℕ, a = 2 ^ k := by
  intro a ha
  refine ⟨a.primeFactorsList.length, ?_⟩
  apply Nat.eq_prime_pow_of_unique_prime_dvd (ne_of_gt (hA a ha))
  intro p hp hpa
  have hge := hp.two_le
  by_contra hne
  have hthree : 3 ≤ p := by omega
  exact hodd ⟨p, hp, hthree, a, ha, hpa⟩

end PilzDensity
