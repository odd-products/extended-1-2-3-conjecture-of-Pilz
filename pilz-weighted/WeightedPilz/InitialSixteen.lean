import WeightedPilz.InitialFifteen
import WeightedPilz.InitialSixteenMixed
import WeightedPilz.ShortFreshFive

/-! The exceptional sixteenth interval and its prime successor. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem two_ne_zero_of_expChar_ne_two (p : ℕ) [hpK : ExpChar K p] (hp2 : p ≠ 2) :
    (2 : K) ≠ 0 := by
  cases hpK with
  | zero => exact two_ne_zero
  | prime hp =>
    intro hz
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact hp.ne_one h
    · exact hp2 h

theorem intervalBound_sixteen (c : ℕ → K) (hc : NonzeroWeights 16 c) : IntervalBound 16 c := by
  have hr : (intervalFreshPrimes 16).Nonempty := by decide
  let S := intervalFreshData 16 c (by decide) hc hr
  have hvars : S.vars.card = 2 := by change (intervalFreshPrimes 16).card = 2; decide
  have hcore : S.C = intervalCore 16 c := rfl
  have hw : weight S.C = 14 := by rw [hcore, weight_intervalCore 16 c hc]; decide
  have hd : 10 ≤ distance S.C := by rw [hcore]; exact intervalCore_sixteen_distance_ten c hc
  have h := S.short_fresh_test_five (ringExpChar K) 10 hvars hd (by omega) (by omega)
    (by
      intro j hj hnd hcost
      have hpow := intervalCore_sixteen_nondistinguished_power_sixteen c hc (ringExpChar K) hj hnd
      rw [hw, hvars, hcore]
      omega)
    (by
      intro e H hH
      have hbin := intervalCore_initial_distinguished_binomial_budget
        (ringExpChar K) e 16 (by omega) c hc H hH
      have hfc : Pilz.freshCount 16 = 2 := by decide
      rw [hfc] at hbin
      rw [hw, hvars, hcore]
      exact hbin)
    (by
      intro e f M L hef hM hL hne
      have htwo := intervalCore_unequal_distinguished_sum_bound 16 4 (ringExpChar K) e f c hc
        (by decide) M L hef hM hL
      have hweight : weight (intervalCore 16 c) = 14 := by rw [← hcore]; exact hw
      rw [hweight] at htwo
      rw [hw, hvars, hcore]
      omega)
    (by
      intro hp2 e f M L hM hL hne
      have hmixed := intervalCore_sixteen_mixed_distinguished (ringExpChar K) e f c hc
        (two_ne_zero_of_expChar_ne_two (ringExpChar K) hp2) M L hM hL
      rw [hw, hvars, hcore]
      exact hmixed)
  rw [hw, hvars] at h
  have heq := distance_interval_eq_freshData 16 c (by decide) hc hr
  change distance (interval 16 c) = distance S.F at heq
  rw [← heq] at h
  exact (le_distance_iff _ 16).mp h

theorem intervalBound_seventeen (c : ℕ → K) (hc : NonzeroWeights 17 c) : IntervalBound 17 c := by
  have hc16 : NonzeroWeights 16 c := by
    intro a ha
    exact hc a (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by
      have := (Finset.mem_Icc.mp ha).2
      omega⟩)
  exact intervalBound_prime_successor 16 c (by decide) hc (intervalBound_sixteen c hc16)

end WeightedPilz
