import WeightedPilz.CoreNinePowers
import WeightedPilz.DilationOverlap
import WeightedPilz.IntegerResidues
import WeightedPilz.ShortFreshTest
import WeightedPilz.Initial

/-! The weighted ninth interval, including arbitrary fields. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

theorem intervalCore_nine_residue_capacity (c : ℕ → K) (hc : NonzeroWeights 9 c)
    {q : ℕ} (hq : 2 ≤ q) : residueSigma q (intervalCore 9 c) ≤ 3 := by
  have hp : 16 ≤ 4 ^ q := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 4) hq
  have h9 : 9 < 4 ^ q := lt_of_lt_of_le (by decide : 9 < 16) hp
  have h := residueSigma_intervalCore_pow_le 9 q 1 3 c hc (by omega) (by simpa using h9)
  simpa only [pow_one] using h

theorem intervalCore_nine_unequal_distinguished_sum (p e f : ℕ) [ExpChar K p]
    (c : ℕ → K) (hc : NonzeroWeights 9 c) (M L : Poly K)
    (hef : p ^ e ≠ p ^ f) (hM : weight M = 1) (hL : weight L = 1) :
    8 ≤ weight (M * intervalCore 9 c ^ p ^ e + L * intervalCore 9 c ^ p ^ f) := by
  obtain ⟨a, u, hu, rfl⟩ := exists_monomial_of_weight_one M hM
  obtain ⟨b, v, hv, rfl⟩ := exists_monomial_of_weight_one L hL
  have hweight : weight (intervalCore 9 c) = 7 := by
    rw [weight_intervalCore 9 c hc]
    decide
  have hp : 2 ≤ p := by
    have hp0 := expChar_pos K p
    by_contra hnot
    have hp1 : p = 1 := by omega
    simp [hp1] at hef
  have aux (i j : ℕ) (hij : i ≤ j) (hneq : p ^ i ≠ p ^ j)
      (a b : ℕ →₀ ℕ) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) :
      8 ≤ weight (monomial a u * intervalCore 9 c ^ p ^ i +
        monomial b v * intervalCore 9 c ^ p ^ j) := by
    have hlt : i < j := by
      have hne : i ≠ j := fun h => hneq (congrArg (fun k => p ^ k) h)
      omega
    have hratio : 2 ≤ p ^ (j - i) := by
      have h := Nat.pow_le_pow_right (by omega : 1 ≤ p) (show 1 ≤ j - i by omega)
      simp only [pow_one] at h
      exact hp.trans h
    have hσ := intervalCore_nine_residue_capacity c hc hratio
    have h := distinguished_monomial_sum_overlap p i j hij (intervalCore 9 c) a b u v hu hv
    rw [hweight] at h
    omega
  rcases le_total e f with h | h
  · exact aux e f h hef a b u v hu hv
  · simpa only [add_comm] using aux f e h hef.symm b a v u hv hu

theorem intervalBound_nine (c : ℕ → K) (hc : NonzeroWeights 9 c) : IntervalBound 9 c := by
  have hr : (intervalFreshPrimes 9).Nonempty := by decide
  let S := intervalFreshData 9 c (by decide) hc hr
  have hvars : S.vars.card = 2 := by change (intervalFreshPrimes 9).card = 2; decide
  have hcore : S.C = intervalCore 9 c := rfl
  have hw : weight S.C = 7 := by rw [hcore, weight_intervalCore 9 c hc]; decide
  have hd : 4 ≤ distance S.C := by rw [hcore]; exact intervalCore_nine_distance_four c hc
  have h := S.short_fresh_test (ringExpChar K) 4 (by omega) hd (by omega) (by omega)
    (by
      intro j hj hnd hcost
      have hrow := S.fresh_nondistinguished_degree_cost (ringExpChar K) hj hnd
      rw [hvars] at hrow
      have hpow := intervalCore_nine_power_six c hc hj
      rw [hw, hvars, hcore]
      omega)
    (by
      intro e H hH
      have hbin := intervalCore_nine_distinguished_binomial_six (ringExpChar K) e c hc H hH
      rw [hw, hvars, hcore]
      omega)
    (by
      intro e f M L hef hM hL hne
      have htwo := intervalCore_nine_unequal_distinguished_sum (ringExpChar K) e f c hc M L hef hM hL
      rw [hw, hvars, hcore]
      omega)
  rw [hw, hvars] at h
  have heq := distance_interval_eq_freshData 9 c (by decide) hc hr
  change distance (interval 9 c) = distance S.F at heq
  rw [← heq] at h
  exact (le_distance_iff _ 9).mp h

theorem intervalBound_le_nine (n : ℕ) (hn : n ≤ 9) (c : ℕ → K)
    (hc : NonzeroWeights n c) : IntervalBound n c := by
  by_cases h8 : n ≤ 8
  · exact intervalBound_le_eight n h8 c hc
  · have hn9 : n = 9 := by omega
    subst n
    exact intervalBound_nine c hc

end WeightedPilz
