import WeightedPilz.Initial
import WeightedPilz.InitialCoreBinomial
import WeightedPilz.CoreOverlap
import WeightedPilz.PowerGapPositive
import WeightedPilz.ShortFreshTest

/-! The short fresh-row assembly for the last four composite initial intervals.
The core-distance input is separated from its coordinate-slice proof. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

def initialLateCoreLowerBound (n : ℕ) : ℕ :=
  if n = 18 then 11 else if n = 21 then 12 else 15

/-- The four late initial cases follow from their core bounds, uniformly in
the characteristic and without restrictions on the multiplier variables. -/
theorem intervalBound_initial_late_of_core (n : ℕ)
    (hn : n = 18 ∨ n = 21 ∨ n = 22 ∨ n = 24)
    (c : ℕ → K) (hc : NonzeroWeights n c)
    (hcore : initialLateCoreLowerBound n ≤ distance (intervalCore n c)) :
    IntervalBound n c := by
  let κ := initialLateCoreLowerBound n
  let r := Pilz.freshCount n
  have hnum : 2 ≤ r ∧ n ≤ r * (κ + 1) ∧ n - 1 - κ ≤ 2 * r ∧
      2 ≤ n - r ∧ n ≤ κ + 1 + r * (r + 1) / 2 ∧ n < 25 ∧
      n - 2 * r + 8 ≤ 2 * (n - r) := by
    rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel
  have hnpos : 0 < n := by omega
  have hr : (intervalFreshPrimes n).Nonempty := by
    apply Finset.card_pos.mp
    rw [Pilz.card_freshPrimes]
    exact lt_of_lt_of_le (by decide : 0 < 2) hnum.1
  let S := intervalFreshData n c hnpos hc hr
  have hvars : S.vars.card = r := Pilz.card_freshPrimes n
  have hsum : weight S.C + S.vars.card = n := by
    rw [hvars]
    exact weight_intervalCore_add_freshCount n c hc
  have hwcore : weight S.C = n - r := by omega
  obtain ⟨p, hp⟩ := ExpChar.exists K
  letI : ExpChar K p := hp
  have hdist := S.short_fresh_test p κ
    (by rw [hvars]; exact hnum.1) hcore
    (by rw [hsum, hvars]; exact hnum.2.1)
    (by rw [hsum, hvars]; exact hnum.2.2.1)
    (by
      intro j hj hnd _
      have hgap := power_gap p S.C (by rw [hwcore]; exact hnum.2.2.2.1) hj hnd
      have hfresh := S.fresh_nondistinguished_degree_cost p hj hnd
      rw [hvars] at hfresh
      rw [hsum]
      have hκ : κ ≤ distance S.C := hcore
      omega)
    (by
      intro e B hB
      rw [hsum, hvars]
      exact intervalCore_initial_distinguished_binomial_budget p e n
        (by omega) c hc B hB)
    (by
      intro e f M L hef hM hL _
      have hbound := intervalCore_unequal_distinguished_sum_bound n 4 p e f c hc
        hnum.2.2.2.2.2.1 M L hef hM hL
      change 2 * weight S.C ≤
        weight (M * S.C ^ p ^ e + L * S.C ^ p ^ f) + 2 * 4 at hbound
      rw [hsum, hvars]
      rw [hwcore] at hbound
      omega)
  rw [hsum] at hdist
  apply (le_distance_iff (interval n c) n).mp
  rw [distance_interval_eq_freshData n c hnpos hc hr]
  exact hdist

/-- The remaining direct sharp-completion case. -/
theorem intervalBound_twenty_of_core (c : ℕ → K) (hc : NonzeroWeights 20 c)
    (hcore : 12 ≤ distance (intervalCore 20 c)) : IntervalBound 20 c := by
  apply intervalBound_of_core_distance 20 c (by decide) hc (by decide +kernel)
  have hcard : (intervalFreshPrimes 20).card = 4 := by decide +kernel
  rw [hcard]
  omega

theorem intervalBound_nineteen_of_core (c : ℕ → K) (hc : NonzeroWeights 19 c)
    (hcore : 11 ≤ distance (intervalCore 18 c)) : IntervalBound 19 c := by
  have hc18 : NonzeroWeights 18 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
      (Finset.mem_Icc.mp ha).2.trans (by decide)⟩)
  apply intervalBound_prime_successor 18 c (by decide) hc
  exact intervalBound_initial_late_of_core 18 (Or.inl rfl) c hc18
    (by simpa [initialLateCoreLowerBound] using hcore)

theorem intervalBound_twentyThree_of_core (c : ℕ → K) (hc : NonzeroWeights 23 c)
    (hcore : 15 ≤ distance (intervalCore 22 c)) : IntervalBound 23 c := by
  have hc22 : NonzeroWeights 22 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
      (Finset.mem_Icc.mp ha).2.trans (by decide)⟩)
  apply intervalBound_prime_successor 22 c (by decide) hc
  exact intervalBound_initial_late_of_core 22 (by omega) c hc22
    (by simpa [initialLateCoreLowerBound] using hcore)

end WeightedPilz
