import Pilz.PrimePowerSplit
import Pilz.PrimePowerTailNumeric

/-! The prime-power error estimate, with the paper's constant `8/3`. -/

noncomputable section

namespace Pilz.Chebyshev

open Finset
open scoped BigOperators

def thetaPower (n a : ℕ) : ℝ :=
  ∑ p ∈ (primeSet n).filter (fun p => p ^ a ≤ n), Real.log (p : ℝ)

theorem thetaPower_le_theta_root {n a : ℕ} (ha : 0 < a) :
    thetaPower n a ≤ theta ((n : ℝ) ^ ((a : ℝ)⁻¹)) := by
  unfold theta
  rw [thetaNat_eq_sum_primes]
  unfold thetaPower
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hpow⟩ := mem_filter.mp hp
    obtain ⟨hprime, _⟩ := mem_primeSet.mp hp
    apply mem_primeSet.mpr
    refine ⟨hprime, Nat.le_floor ?_⟩
    apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p) (Nat.cast_nonneg n)
      (by exact_mod_cast ha)).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast hpow
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (mem_primeSet.mp hp).1.one_le)

theorem thetaPower_lt_root_log_four {n a : ℕ} (hn : 1 ≤ n) (ha : 0 < a) :
    thetaPower n a < (n : ℝ) ^ ((a : ℝ)⁻¹) * Real.log 4 := by
  have htheta := thetaPower_le_theta_root (n := n) ha
  have hpsi : theta ((n : ℝ) ^ ((a : ℝ)⁻¹)) ≤ psi ((n : ℝ) ^ ((a : ℝ)⁻¹)) :=
    thetaNat_le_psiNat _
  have hroot : 1 ≤ (n : ℝ) ^ ((a : ℝ)⁻¹) :=
    Real.one_le_rpow (by exact_mod_cast hn) (inv_nonneg.mpr (Nat.cast_nonneg a))
  exact htheta.trans_lt (hpsi.trans_lt (psi_lt_mul_log_four hroot))

theorem oddPowerPairs_eq_bounded {n : ℕ} (hK : 3 ≤ Nat.log 2 n) :
    oddPowerPairs n =
      ((primeSet n) ×ˢ Icc 0 ((Nat.log 2 n - 3) / 2)).filter
        (fun z => z.1 ^ (2 * z.2 + 3) ≤ n) := by
  ext z
  obtain ⟨p, a⟩ := z
  simp only [mem_oddPowerPairs, mem_filter, mem_product, mem_primeSet, mem_Icc]
  constructor
  · rintro ⟨hp, hpow⟩
    have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2)
      ((Nat.pow_le_pow_left hp.two_le (2 * a + 3)).trans hpow)
    have hpn := (le_self_pow₀ hp.one_le (by omega : 2 * a + 3 ≠ 0)).trans hpow
    exact ⟨⟨⟨hp, hpn⟩, by omega, by omega⟩, hpow⟩
  · rintro ⟨⟨⟨hp, _⟩, _⟩, hpow⟩
    exact ⟨hp, hpow⟩

theorem oddPower_sum_eq {n : ℕ} (hK : 3 ≤ Nat.log 2 n) :
    (∑ z ∈ oddPowerPairs n, Real.log (z.1 : ℝ)) =
      thetaPower n 3 + ∑ a ∈ Icc 1 ((Nat.log 2 n - 3) / 2), thetaPower n (2 * a + 3) := by
  rw [oddPowerPairs_eq_bounded hK]
  simp only [sum_filter, sum_product_right]
  have hs : Icc 0 ((Nat.log 2 n - 3) / 2) =
      insert 0 (Icc 1 ((Nat.log 2 n - 3) / 2)) := by
    ext a
    simp only [mem_Icc, mem_insert]
    omega
  rw [hs, sum_insert (by simp)]
  simp only [mul_zero, zero_add, thetaPower, sum_filter]

theorem oddPower_sum_le {n : ℕ} (hn : 1 ≤ n) (hK : 3 ≤ Nat.log 2 n) :
    (∑ z ∈ oddPowerPairs n, Real.log (z.1 : ℝ)) ≤
      thetaPower n 3 + (((Nat.log 2 n - 3) / 2 : ℕ) : ℝ) *
        ((n : ℝ) ^ (1 / 5 : ℝ) * Real.log 4) := by
  rw [oddPower_sum_eq hK]
  apply add_le_add_left
  calc
    _ ≤ ∑ _a ∈ Icc 1 ((Nat.log 2 n - 3) / 2),
        (n : ℝ) ^ (1 / 5 : ℝ) * Real.log 4 := by
      apply sum_le_sum
      intro a ha
      have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
      have hab := thetaPower_lt_root_log_four hn (by omega : 0 < 2 * a + 3)
      have hexp : ((2 * a + 3 : ℕ) : ℝ)⁻¹ ≤ (1 / 5 : ℝ) := by
        have h5 : (5 : ℝ) ≤ (2 * a + 3 : ℕ) := by exact_mod_cast (show 5 ≤ 2 * a + 3 by omega)
        simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 5) h5
      exact hab.le.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hexp)
        (Real.log_nonneg (by norm_num)))
    _ = _ := by simp

theorem odd_exponent_count_le_log {n : ℕ} (hn : 1 ≤ n) (hK : 3 ≤ Nat.log 2 n) :
    (((Nat.log 2 n - 3) / 2 : ℕ) : ℝ) ≤ Real.log n / (2 * Real.log 2) - 3 / 2 := by
  have hp := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n)
    (show (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) by exact_mod_cast hp)
  rw [Real.log_pow] at hlog
  have hc : 2 * ((Nat.log 2 n - 3) / 2) + 3 ≤ Nat.log 2 n := by omega
  have hcr : 2 * (((Nat.log 2 n - 3) / 2 : ℕ) : ℝ) + 3 ≤ (Nat.log 2 n : ℝ) := by
    exact_mod_cast hc
  have hb : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hprod := mul_le_mul_of_nonneg_right hcr hb.le
  have hfrac : (((Nat.log 2 n - 3) / 2 : ℕ) : ℝ) + 3 / 2 ≤
      Real.log n / (2 * Real.log 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log (2 : ℝ))).mpr
    nlinarith
  linarith

theorem psiNat_sub_thetaNat_lt {n : ℕ} (hn : 256 ≤ n) :
    psiNat n - thetaNat n < 8 / 3 * Real.sqrt n := by
  have hn1 : 1 ≤ n := by omega
  have hK : 3 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
  have hnreal : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
  have hpsi := psi_lt_mul_log_four hsqrt
  have heq : psi (Real.sqrt (n : ℝ)) = psiNat n.sqrt := by
    simp only [psi, Real.nat_floor_real_sqrt_eq_nat_sqrt]
  rw [heq] at hpsi
  have hcube := thetaPower_lt_root_log_four hn1 (by decide : 0 < 3)
  norm_num only [Nat.cast_ofNat, inv_eq_one_div] at hcube
  have hodd := oddPower_sum_le hn1 hK
  have hcount := odd_exponent_count_le_log hn1 hK
  have hmult := mul_le_mul_of_nonneg_right hcount
    (by positivity : 0 ≤ (n : ℝ) ^ (1 / 5 : ℝ) * Real.log 4)
  have hraw : psiNat n - thetaNat n < Real.log 4 *
      (Real.sqrt n + (n : ℝ) ^ (1 / 3 : ℝ) +
        (Real.log n / (2 * Real.log 2) - 3 / 2) * (n : ℝ) ^ (1 / 5 : ℝ)) := by
    rw [psiNat_sub_thetaNat]
    nlinarith
  have h3 : Real.sqrt (n : ℝ) * (n : ℝ) ^ (-1 / 6 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
    norm_num
  have h5 : Real.sqrt (n : ℝ) * (n : ℝ) ^ (-3 / 10 : ℝ) = (n : ℝ) ^ (1 / 5 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
    norm_num
  have hfactor := mul_lt_mul_of_pos_right (primePower_tail_factor hnreal)
    (Real.sqrt_pos.mpr hnpos)
  rw [show Real.log 4 * (1 + (n : ℝ) ^ (-1 / 6 : ℝ) +
      (Real.log n / (2 * Real.log 2) - 3 / 2) * (n : ℝ) ^ (-3 / 10 : ℝ)) *
      Real.sqrt n = Real.log 4 *
      (Real.sqrt n + (n : ℝ) ^ (1 / 3 : ℝ) +
        (Real.log n / (2 * Real.log 2) - 3 / 2) * (n : ℝ) ^ (1 / 5 : ℝ)) by
      calc
        _ = Real.log 4 * (Real.sqrt n +
            Real.sqrt n * (n : ℝ) ^ (-1 / 6 : ℝ) +
            (Real.log n / (2 * Real.log 2) - 3 / 2) *
              (Real.sqrt n * (n : ℝ) ^ (-3 / 10 : ℝ))) := by ring
        _ = _ := by rw [h3, h5]] at hfactor
  exact hraw.trans hfactor

theorem psi_sub_theta_nonneg (x : ℝ) : 0 ≤ psi x - theta x := by
  exact sub_nonneg.mpr (thetaNat_le_psiNat _)

theorem psi_sub_theta_lt {x : ℝ} (hx : 256 ≤ x) :
    psi x - theta x < 8 / 3 * Real.sqrt x := by
  have hxnonneg : 0 ≤ x := by linarith
  have hn : 256 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; exact hx)
  have h := psiNat_sub_thetaNat_lt hn
  have hs := Real.sqrt_le_sqrt (Nat.floor_le hxnonneg)
  have hmul := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 8 / 3)
  exact h.trans_le hmul

end Pilz.Chebyshev
