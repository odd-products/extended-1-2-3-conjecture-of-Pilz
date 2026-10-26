import WeightedPilz.LargeBase
import WeightedPilz.IntervalFresh

noncomputable section
namespace WeightedPilz
variable {K : Type*} [Field K]

theorem FreshPrimeBounded.baseOnly {n : ℕ} {D : Poly K} (hD : FreshPrimeBounded n D) :
    ∀ p ∈ intervalFreshPrimes n, ∀ d ∈ D.support, d p = 0 := by
  intro p hp d hd
  by_contra hne
  have hbound := (hD p ⟨d, hd, Nat.pos_of_ne_zero hne⟩).2
  have hfresh := (Pilz.mem_freshPrimes_iff n p).mp hp
  omega

/-- Equation `eq:large-base`, with the actual weighted interval core. -/
theorem large_base (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n) (hD : D ≠ 0)
    (hbound : FreshPrimeBounded n D) :
    n ≤ weight (intervalCore n c * D) + Pilz.freshCount n * weight D := by
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < (Pilz.freshPrimes n).card
    rw [Pilz.card_freshPrimes]
    have h := Arithmetic.fresh_count_eight n hn
    omega
  have h := interval_mul_base_lower n c D hc hn hD hbound
  rwa [weight_interval_mul_base_freshCount n c (by omega) hc hr D hbound.baseOnly] at h

/-- The interval core uses exactly base prime coordinates; nonzero coefficients
are used only to identify its support. -/
theorem intervalCore_freshPrimeBounded (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) : FreshPrimeBounded n (intervalCore n c) := by
  intro p hp
  obtain ⟨d, hd, hdp⟩ := hp
  have hd0 := hd
  rw [intervalCore_support n c hc] at hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  have hpFac : p ∈ a.primeFactors := Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hdp)
  have hpp := (Nat.mem_primeFactors.mp hpFac).1
  have hpn : p ≤ n := (Nat.le_of_mem_primeFactors hpFac).trans
    (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).2
  refine ⟨hpp, ?_⟩
  by_contra hnot
  have hfresh : p ∈ intervalFreshPrimes n :=
    (Pilz.mem_freshPrimes_iff n p).mpr ⟨hpp, hpn, by omega⟩
  have hz := intervalCore_fresh_exponent_zero c hc hfresh hd0
  omega

/-- Outside-variable slicing extends the large-base budget to every nonzero
polynomial, simultaneously controlling its own weight and its core product. -/
theorem large_base_unrestricted (n : ℕ) (c : ℕ → K) (D : Poly K)
    (hc : NonzeroWeights n c) (hn : 67 ≤ n) (hD : D ≠ 0) :
    n ≤ weight (intervalCore n c * D) + Pilz.freshCount n * weight D := by
  classical
  let S : Set ℕ := (Pilz.primesUpTo (n / 2) : Set ℕ)
  have hC : ((intervalCore n c).vars : Set ℕ) ⊆ S := by
    intro p hp
    exact (Pilz.mem_primesUpTo (n / 2) p).mpr
      (intervalCore_freshPrimeBounded n c hc p
        ((variableOccurs_iff_mem_vars _ p).mpr hp))
  obtain ⟨E, hE, hEvars, hEweight, hEproduct⟩ :=
    exists_base_multiplier_with_weight S (intervalCore n c) D hC hD
  have hEbound : FreshPrimeBounded n E := by
    intro p hp
    exact (Pilz.mem_primesUpTo (n / 2) p).mp
      (hEvars ((variableOccurs_iff_mem_vars E p).mp hp))
  have hbase := large_base n c E hc hn hE hEbound
  exact hbase.trans (Nat.add_le_add hEproduct
    (Nat.mul_le_mul_left (Pilz.freshCount n) hEweight))

end WeightedPilz
