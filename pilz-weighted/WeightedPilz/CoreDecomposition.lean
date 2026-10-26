import WeightedPilz.Components
import WeightedPilz.ComponentBounds
import WeightedPilz.IntervalFresh
import WeightedPilz.Arithmetic.PrimeComponents
import WeightedPilz.RepeatedEndpoints

/-! Exact decomposition of the weighted core at the integer square root. -/

noncomputable section
namespace WeightedPilz

open MvPolynomial
open scoped BigOperators
open Pilz (primesUpTo mem_primesUpTo roughNumbers mem_roughNumbers)
variable {K : Type*} [Field K]

theorem div_le_sqrt_of_sqrt_lt {n p : ℕ} (hp : Nat.sqrt n < p) :
    n / p ≤ Nat.sqrt n := by
  have hp0 : 0 < p := by omega
  by_contra hnot
  have hmul : (Nat.sqrt n + 1) * p ≤ n :=
    (Nat.le_div_iff_mul_le hp0).mp (by omega)
  have hsq := Nat.lt_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at hsq
  have hpp : Nat.sqrt n + 1 ≤ p := by omega
  have hbound := Nat.mul_le_mul_left (Nat.sqrt n + 1) hpp
  omega

theorem sqrt_le_half {n : ℕ} (hn : 4 ≤ n) : Nat.sqrt n ≤ n / 2 :=
  Arithmetic.sqrt_le_half hn

/-- The numerical subtraction in the tables counts exactly the linear rows. -/
theorem card_linearCorePrimes (n : ℕ) (hn : 4 ≤ n) :
    (Arithmetic.linearCorePrimes n).card = Arithmetic.linearCoreCount n :=
  (Arithmetic.linearCoreCount_eq_card hn).symm

theorem roughNumbers_sqrt (n : ℕ) (hn : 0 < n) :
    roughNumbers (primesUpTo (Nat.sqrt n)) n =
      insert 1 ((primesUpTo n).filter (Nat.sqrt n < ·)) := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨hbpos, hbn, hbrough⟩ := (mem_roughNumbers _ n b).mp hb
    by_cases hb1 : b = 1
    · simp [hb1]
    · have hprime : Nat.Prime b := by
        apply Nat.prime_def_le_sqrt.mpr
        refine ⟨by omega, ?_⟩
        intro m hm2 hms hmdvd
        have hp := Nat.minFac_prime (show m ≠ 1 by omega)
        have hpm : Nat.minFac m ≤ m := Nat.minFac_le_of_dvd hm2 (dvd_refl m)
        have hpn : Nat.minFac m ≤ Nat.sqrt n :=
          hpm.trans (hms.trans (Nat.sqrt_le_sqrt hbn))
        exact hbrough (Nat.minFac m) ((mem_primesUpTo _ _).mpr ⟨hp, hpn⟩)
          ((Nat.minFac_dvd m).trans hmdvd)
      have hroot : Nat.sqrt n < b := by
        by_contra h
        exact hbrough b ((mem_primesUpTo _ _).mpr ⟨hprime, by omega⟩) (dvd_refl b)
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨(mem_primesUpTo n b).mpr ⟨hprime, hbn⟩, hroot⟩)
  · intro hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact (mem_roughNumbers _ n 1).mpr
        ⟨le_rfl, hn, fun p hp => (Pilz.primesUpTo_prime _ p hp).not_dvd_one⟩
    · obtain ⟨hbp, hroot⟩ := Finset.mem_filter.mp hb
      obtain ⟨hprime, hbn⟩ := (mem_primesUpTo n b).mp hbp
      apply (mem_roughNumbers _ n b).mpr
      refine ⟨hprime.pos, hbn, ?_⟩
      intro p hp hdiv
      obtain ⟨hpp, hps⟩ := (mem_primesUpTo _ p).mp hp
      have heq := (Nat.prime_dvd_prime_iff_eq hpp hprime).mp hdiv
      omega

theorem interval_eq_smooth_add_prime_rows (n : ℕ) (c : ℕ → K) (hn : 0 < n) :
    interval n c = smoothInterval (primesUpTo (Nat.sqrt n)) n c +
      ∑ p ∈ (primesUpTo n).filter (Nat.sqrt n < ·),
        interval (n / p) (fun a => c (p * a)) * X p := by
  classical
  have hone : 1 ∉ (primesUpTo n).filter (Nat.sqrt n < ·) := by
    intro h
    exact Nat.not_prime_one ((mem_primesUpTo n 1).mp (Finset.mem_filter.mp h).1).1
  rw [interval_eq_rough_components _ n c (Pilz.primesUpTo_prime (Nat.sqrt n)),
    roughNumbers_sqrt n hn, Finset.sum_insert hone]
  simp only [Nat.div_one, monomialOf_one, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpmem, hroot⟩ := Finset.mem_filter.mp hp
  have hprime := ((mem_primesUpTo n p).mp hpmem).1
  rw [smoothInterval_primesUpTo_eq_interval (div_le_sqrt_of_sqrt_lt hroot),
    monomialOf_prime hprime, mul_comm]

theorem intervalCore_eq_smooth_add_linear (n : ℕ) (c : ℕ → K) (hn : 4 ≤ n) :
    intervalCore n c = smoothInterval (primesUpTo (Nat.sqrt n)) n c +
      ∑ p ∈ Arithmetic.linearCorePrimes n,
        interval (n / p) (fun a => c (p * a)) * X p := by
  classical
  have hs : Nat.sqrt n ≤ n / 2 := sqrt_le_half hn
  have hsplit : (primesUpTo n).filter (Nat.sqrt n < ·) =
      Arithmetic.linearCorePrimes n ∪ intervalFreshPrimes n := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpn, hroot⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpp, hpn⟩ := (mem_primesUpTo n p).mp hpn
      by_cases hh : p ≤ n / 2
      · exact Finset.mem_union_left _ ((Arithmetic.mem_linearCorePrimes n p).mpr
          ⟨hpp, hroot, hh⟩)
      · exact Finset.mem_union_right _ ((Pilz.mem_freshPrimes_iff n p).mpr
          ⟨hpp, hpn, by omega⟩)
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨hpp, hroot, hh⟩ := (Arithmetic.mem_linearCorePrimes n p).mp hp
        exact Finset.mem_filter.mpr ⟨(mem_primesUpTo n p).mpr
          ⟨hpp, hh.trans (Nat.div_le_self n 2)⟩, hroot⟩
      · obtain ⟨hpp, hpn, hh⟩ := (Pilz.mem_freshPrimes_iff n p).mp hp
        exact Finset.mem_filter.mpr ⟨(mem_primesUpTo n p).mpr
          ⟨hpp, hpn⟩, lt_of_le_of_lt hs hh⟩
  have hdis : Disjoint (Arithmetic.linearCorePrimes n) (intervalFreshPrimes n) := by
    apply Finset.disjoint_left.mpr
    intro p hp hf
    have hpbound : p ≤ n / 2 := by
      have hp' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hp')
    have hfbound := ((Pilz.mem_freshPrimes_iff n p).mp hf).2.2
    omega
  have hI := interval_eq_smooth_add_prime_rows n c (by omega)
  rw [hsplit, Finset.sum_union hdis] at hI
  have hsum : (∑ p ∈ intervalFreshPrimes n,
      interval (n / p) (fun a => c (p * a)) * X p) =
      ∑ p ∈ intervalFreshPrimes n, C (c p) * X p := by
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpp, hpn, hph⟩ := (Pilz.mem_freshPrimes_iff n p).mp hp
    have hlo : 1 ≤ n / p := (Nat.le_div_iff_mul_le hpp.pos).mpr (by simpa using hpn)
    have hhi : n / p < 2 := (Nat.div_lt_iff_lt_mul hpp.pos).mpr (by omega)
    have hdiv : n / p = 1 := by omega
    rw [hdiv]
    simp [interval, polynomialOf]
  rw [hsum, interval_eq_core_add_weighted_fresh] at hI
  exact add_right_cancel (by simpa only [add_assoc] using hI)

theorem linearCore_coefficient_weights (n p : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hp : p ∈ Arithmetic.linearCorePrimes n) :
    NonzeroWeights (n / p) (fun a => c (p * a)) := by
  intro a ha
  have hprime : Nat.Prime p := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  apply hc
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.mul_pos hprime.pos (Finset.mem_Icc.mp ha).1, ?_⟩
  simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hprime.pos).mp (Finset.mem_Icc.mp ha).2

end WeightedPilz
