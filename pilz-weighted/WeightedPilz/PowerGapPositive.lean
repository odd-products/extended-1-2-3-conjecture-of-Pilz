import WeightedPilz.PowerGap
import WeightedPilz.Frobenius
import Mathlib.Data.Finsupp.Weight

/-! The positive-characteristic assertion of `lem:powergap`.
Induction on total degree removes common exponent residues and exponent
dilations. Coefficients are never replaced by presumed roots. -/

noncomputable section

namespace WeightedPilz

open MvPolynomial

variable {σ K : Type*} [Field K]

theorem distance_monomial_mul (α : σ →₀ ℕ) (P : MvPolynomial σ K) :
    distance (monomial α 1 * P) = distance P := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨H, hH, hmin⟩ := exists_weight_eq_distance P
    have h := distance_le_weight_mul (monomial α 1 * P) H hH
    rwa [mul_assoc, weight_monomial_mul, hmin] at h
  · apply (le_distance_iff _ _).mpr
    intro H hH
    simpa only [mul_assoc, weight_monomial_mul] using distance_le_weight_mul P H hH

private theorem dilate_pow' (q : ℕ) (P : MvPolynomial σ K) (n : ℕ) :
    dilate q (P ^ n) = (dilate q P) ^ n := by
  induction n with
  | zero =>
    change dilate q (monomial 0 1) = _
    rw [dilate_monomial]
    simp [scaleExponent]
  | succ n ih => rw [pow_succ, dilate_mul, ih, pow_succ]

private theorem sum_scaleExponent (q : ℕ) (d : σ →₀ ℕ) :
    (scaleExponent q d).sum (fun _ e => e) = q * d.sum (fun _ e => e) := by
  simp only [scaleExponent]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [succ_nsmul, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ih]
    rw [Nat.succ_mul]

private theorem totalDegree_pos_of_nonmonomial (P : MvPolynomial σ K)
    (hP : 2 ≤ weight P) : 0 < P.totalDegree := by
  classical
  by_contra hz
  have heq : P = C (coeff 0 P) := totalDegree_eq_zero_iff_eq_C.mp (by omega)
  have hw : weight P ≤ 1 := by
    rw [heq]
    change (monomial (0 : σ →₀ ℕ) (coeff 0 P)).support.card ≤ 1
    rw [support_monomial]
    split_ifs <;> simp
  omega

private theorem residueRoot_totalDegree_lt {p : ℕ} (hp : 2 ≤ p)
    (P : MvPolynomial σ K) (hP : 2 ≤ weight P) (α : σ →₀ ℕ) :
    (residueRoot p P α).totalDegree < P.totalDegree := by
  classical
  have hb : (residueRoot p P α).totalDegree ≤ P.totalDegree / p := by
    apply Finset.sup_le
    intro d hd
    have h := le_totalDegree (residueRoot_support_lift (by omega) P α d hd)
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), sum_scaleExponent] at h
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have hmul : p * d.sum (fun _ e => e) ≤ P.totalDegree := (Nat.le_add_left _ _).trans h
    simpa only [Nat.mul_comm] using hmul
  have hmul : p * (residueRoot p P α).totalDegree ≤ P.totalDegree := by
    have h := (Nat.le_div_iff_mul_le (by omega)).mp hb
    simpa [Nat.mul_comm] using h
  have htwo := (Nat.mul_le_mul_right (residueRoot p P α).totalDegree hp).trans hmul
  have hpos := totalDegree_pos_of_nonmonomial P hP
  omega

private theorem power_gap_charP_coprime_aux (p : ℕ) [CharP K p] (hp : p.Prime)
    (N : ℕ) : ∀ P : MvPolynomial σ K, P.totalDegree = N → 2 ≤ weight P →
    ∀ n : ℕ, 2 ≤ n → (n : K) ≠ 0 → distance P + 1 ≤ weight (P ^ n) := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro P hdeg hP n hn hnK
    by_cases hv : ∃ (i : σ) (d : σ →₀ ℕ), d ∈ P.support ∧
        ∃ e ∈ P.support, (d i : K) ≠ (e i : K)
    · obtain ⟨i, d, hd, e, he, hde⟩ := hv
      exact power_gap_of_residue_variation P i hd he hde hn hnK
    · push_neg at hv
      have hPn : P ≠ 0 := by
        intro hz
        simp [hz, weight] at hP
      obtain ⟨a, ha⟩ := support_nonempty.mpr hPn
      let α := residueExponent p a
      have hres : ∀ d ∈ P.support, residueExponent p d = α := by
        intro d hd
        ext i
        exact (CharP.cast_eq_iff_mod_eq K p).mp (hv i d hd a ha)
      let D := residueRoot p P α
      have hfactor : P = monomial α 1 * dilate p D := by
        rw [← residuePart_eq_self_of_support p P α hres]
        exact residuePart_eq_monomial_mul_dilate p P α
      have hw : weight D = weight P := by
        rw [hfactor, weight_monomial_mul, weight_dilate hp.pos]
      have hdist : distance P = distance D := by
        rw [hfactor, distance_monomial_mul, distance_dilate hp.pos]
      have hpow : weight (P ^ n) = weight (D ^ n) := by
        rw [hfactor, mul_pow, monomial_pow, one_pow, weight_monomial_mul,
          ← dilate_pow', weight_dilate hp.pos]
      have hlt : D.totalDegree < N := by
        rw [← hdeg]
        exact residueRoot_totalDegree_lt hp.two_le P hP α
      rw [hdist, hpow]
      exact ih D.totalDegree hlt D rfl (by omega) n hn hnK

/-- The power gap for exponents prime to the positive characteristic. -/
theorem power_gap_charP_coprime (p : ℕ) [CharP K p] (hp : p.Prime)
    (P : MvPolynomial σ K) (hP : 2 ≤ weight P) {n : ℕ} (hn : 2 ≤ n)
    (hnp : ¬ p ∣ n) : distance P + 1 ≤ weight (P ^ n) := by
  exact power_gap_charP_coprime_aux p hp P.totalDegree P rfl hP n hn
    (fun h => hnp ((CharP.cast_eq_zero_iff K p n).mp h))

/-- `lem:powergap` in every positive characteristic, including imperfect fields. -/
theorem power_gap_charP (p : ℕ) [CharP K p] (hp : p.Prime)
    (P : MvPolynomial σ K) (hP : 2 ≤ weight P) {n : ℕ} (hn : 0 < n)
    (hnpower : ∀ e : ℕ, n ≠ p ^ e) : distance P + 1 ≤ weight (P ^ n) := by
  letI : ExpChar K p := ExpChar.prime hp
  obtain ⟨e, h, hnp, hfactor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hn) p hp.ne_one
  have hpos : 0 < h := by
    by_contra hz
    have hh : h = 0 := by omega
    simp [hh] at hfactor
    omega
  have hh : 2 ≤ h := by
    by_contra hnot
    have hone : h = 1 := by omega
    have hbad : n = p ^ e := by simpa [hone] using hfactor
    exact hnpower e hbad
  have hgap := power_gap_charP_coprime p hp P hP hh hnp
  have hw : weight (P ^ n) = weight (P ^ h) := by
    rw [hfactor, Nat.mul_comm, pow_mul]
    exact weight_pow_expChar p e (P ^ h)
  rw [hw]
  exact hgap

/-- Unified power gap. The exponential characteristic is one in
characteristic zero and the characteristic prime otherwise. -/
theorem power_gap (p : ℕ) [hpK : ExpChar K p]
    (P : MvPolynomial σ K) (hP : 2 ≤ weight P) {n : ℕ} (hn : 0 < n)
    (hnpower : ∀ e : ℕ, n ≠ p ^ e) : distance P + 1 ≤ weight (P ^ n) := by
  cases hpK with
  | zero =>
    have hn1 : n ≠ 1 := by simpa using hnpower 0
    exact power_gap_charZero P hP (by omega)
  | prime hp => exact power_gap_charP p hp P hP hn hnpower

/-- Every positive power either preserves the original weight or costs at
least one more term than the minimum distance. -/
theorem min_weight_distance_add_one_le_weight_pow (p : ℕ) [ExpChar K p]
    (P : MvPolynomial σ K) (hP : 2 ≤ weight P) {n : ℕ} (hn : 0 < n) :
    min (weight P) (distance P + 1) ≤ weight (P ^ n) := by
  by_cases hnpower : ∃ e : ℕ, n = p ^ e
  · obtain ⟨e, rfl⟩ := hnpower
    rw [weight_pow_expChar]
    exact Nat.min_le_left _ _
  · have hgap := power_gap p P hP hn (by simpa using hnpower)
    exact (Nat.min_le_right _ _).trans hgap

end WeightedPilz
