import WeightedPilz.Arithmetic.Counts

/-! Set/cardinality interfaces for the linear prime components. -/

namespace WeightedPilz.Arithmetic

theorem mem_linearCorePrimes (n q : ℕ) :
    q ∈ linearCorePrimes n ↔ Nat.Prime q ∧ Nat.sqrt n < q ∧ q ≤ n / 2 := by
  simp only [linearCorePrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hqn, hp⟩, hr⟩
    exact ⟨hp, hr, by omega⟩
  · rintro ⟨hp, hr, hqn⟩
    exact ⟨⟨by omega, hp⟩, hr⟩

theorem sqrt_le_half {n : ℕ} (hn : 4 ≤ n) : Nat.sqrt n ≤ n / 2 := by
  have hs : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  exact (Nat.mul_le_mul_left (Nat.sqrt n) hs).trans (Nat.sqrt_le n)

/-- The difference of prime counts is exactly the size of the displayed set. -/
theorem linearCoreCount_eq_card {n : ℕ} (hn : 4 ≤ n) :
    linearCoreCount n = (linearCorePrimes n).card := by
  have hroot := sqrt_le_half hn
  have hsub :
      (Finset.range (Nat.sqrt n + 1)).filter Nat.Prime ⊆
        (Finset.range (n / 2 + 1)).filter Nat.Prime := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
    exact ⟨by omega, hq.2⟩
  have heq : linearCorePrimes n =
      ((Finset.range (n / 2 + 1)).filter Nat.Prime) \
        ((Finset.range (Nat.sqrt n + 1)).filter Nat.Prime) := by
    ext q
    simp only [linearCorePrimes, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hqn, hp⟩, hr⟩
      exact ⟨⟨hqn, hp⟩, fun h => by omega⟩
    · rintro ⟨⟨hqn, hp⟩, hnot⟩
      refine ⟨⟨hqn, hp⟩, ?_⟩
      by_contra h
      exact hnot ⟨by omega, hp⟩
  rw [heq, Finset.card_sdiff_of_subset hsub]
  rfl

theorem linearCoreQuotient_lower {n q : ℕ} (hq : q ∈ linearCorePrimes n) :
    2 ≤ n / q := by
  obtain ⟨hp, _, hqn⟩ := (mem_linearCorePrimes n q).mp hq
  apply (Nat.le_div_iff_mul_le hp.pos).mpr
  have h := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hqn
  simpa only [Nat.mul_comm] using h

end WeightedPilz.Arithmetic
