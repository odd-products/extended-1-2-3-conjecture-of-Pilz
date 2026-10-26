import WeightedPilz.IntegerResidues
import WeightedPilz.ParityMajorization

/-! The two largest parity capacities of an interval core. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {K : Type*} [Field K]

private def parityRootLabel (d : ℕ →₀ ℕ) : ℕ :=
  Nat.floorRoot 2 (d.prod (· ^ ·))

private theorem parityRootLabel_eq {a : ℕ} (ha : 0 < a) :
    parityRootLabel a.factorization = Nat.floorRoot 2 a := by
  rw [parityRootLabel, Nat.factorization_prod_pow_eq_self ha.ne']

private theorem double_root_square_le {a : ℕ} (ha : 0 < a)
    (hres : residueExponent 2 a.factorization ≠ 0) :
    2 * Nat.floorRoot 2 a ^ 2 ≤ a := by
  obtain ⟨k, hk⟩ := (Nat.floorRoot_pow_dvd : Nat.floorRoot 2 a ^ 2 ∣ a)
  have hk0 : k ≠ 0 := by
    intro h
    have hz : a = 0 := by simpa [h] using hk
    omega
  have hk1 : k ≠ 1 := by
    intro h
    have heq : a = Nat.floorRoot 2 a ^ 2 := by simpa [h] using hk
    have hz : residueExponent 2 ((Nat.floorRoot 2 a ^ 2).factorization) = 0 := by
      ext p
      simp [residueExponent_apply, Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul]
    exact hres ((congrArg (fun b : ℕ => residueExponent 2 b.factorization) heq).trans hz)
  have hk2 : 2 ≤ k := by omega
  calc
    2 * Nat.floorRoot 2 a ^ 2 ≤ Nat.floorRoot 2 a ^ 2 * k := by nlinarith
    _ = a := hk.symm

/-- A nonzero exponent parity forces a nonsquare label, so its square part
is at most half the original integer. -/
theorem residueWeight_two_nonzero_le (N : ℕ) (P : Poly K) (hP : IntegerSupported N P)
    (α : ℕ →₀ ℕ) (hα : α ≠ 0) :
    residueWeight 2 P α ≤ Nat.sqrt (N / 2) := by
  classical
  let A := (residuePart 2 P α).support
  have hlabel : ∀d∈A, ∃a:ℕ, 0 < a ∧ a ≤ N ∧ a.factorization = d := by
    intro d hd
    exact hP d (support_residuePart_subset 2 P α hd)
  have hresidue : ∀d∈A, residueExponent 2 d = α := by
    intro d hd
    by_contra hne
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [coeff_residuePart, if_neg hne] at hcoeff
    exact hcoeff rfl
  have hmaps : ∀d∈A, parityRootLabel d ∈ Finset.Icc 1 (Nat.sqrt (N / 2)) := by
    intro d hd
    obtain ⟨a, ha, haN, rfl⟩ := hlabel d hd
    rw [parityRootLabel_eq ha]
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨by decide, ha.ne'⟩), ?_⟩
    apply Nat.le_sqrt.mpr
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    have hnz : residueExponent 2 a.factorization ≠ 0 := by
      rw [hresidue a.factorization hd]
      exact hα
    have hb := (double_root_square_le ha hnz).trans haN
    nlinarith
  have hinj : Set.InjOn parityRootLabel (A : Set (ℕ →₀ ℕ)) := by
    intro d hd e he hde
    obtain ⟨a, ha, _, had⟩ := hlabel d hd
    obtain ⟨b, hb, _, hbe⟩ := hlabel e he
    have hroots : Nat.floorRoot 2 a = Nat.floorRoot 2 b := by
      simpa only [← had, ← hbe, parityRootLabel_eq ha, parityRootLabel_eq hb] using hde
    have hquot := congrArg Nat.factorization hroots
    rw [Nat.factorization_floorRoot, Nat.factorization_floorRoot, had, hbe] at hquot
    ext i
    have hdiv : d i / 2 = e i / 2 := by
      simpa using congrArg (fun f : ℕ →₀ ℕ => f i) hquot
    have hmod : d i % 2 = e i % 2 :=
      congrArg (fun f : ℕ →₀ ℕ => f i) ((hresidue d hd).trans (hresidue e he).symm)
    omega
  have hcard : A.card ≤ (Finset.Icc 1 (Nat.sqrt (N / 2))).card := by
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro b hb
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
    exact hmaps d hd
  simpa only [Nat.card_Icc, Nat.add_sub_cancel, A] using hcard

theorem residueWeight_intervalCore_zero_le (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) : residueWeight 2 (intervalCore n c) 0 ≤ Nat.sqrt n := by
  apply residueWeight_le_of_integerSupported 2 n (Nat.sqrt n) (by decide)
    (intervalCore n c) (integerSupported_intervalCore n c hc)
  simpa only [Nat.succ_eq_add_one, pow_two] using Nat.lt_succ_sqrt n

theorem residueWeight_intervalCore_nonzero_le (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (α : ℕ →₀ ℕ) (hα : α ≠ 0) :
    residueWeight 2 (intervalCore n c) α ≤ Nat.sqrt (n / 2) :=
  residueWeight_two_nonzero_le n _ (integerSupported_intervalCore n c hc) α hα

/-- The actual weighted core satisfies the two-class majorization bound. -/
theorem intervalCore_parity_mixed_capacity (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (D : Poly K)
    (hclasses : 2 ≤ (residueIndices 2 D).card) (α : ℕ →₀ ℕ) :
    residueWeight 2 (intervalCore n c * D) α ≤
      (weight D - 1) * Nat.sqrt n + Nat.sqrt (n / 2) :=
  residueWeight_mul_mixed 2 _ D _ _ (Nat.sqrt_le_sqrt (Nat.div_le_self n 2))
    (residueWeight_intervalCore_zero_le n c hc)
    (residueWeight_intervalCore_nonzero_le n c hc) hclasses α

/-- Every four-term mixed pattern other than `(3,1)` has capacity `2s+2t`. -/
theorem intervalCore_parity_four_capacity (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (D : Poly K) (hD : weight D = 4)
    (hclasses : 2 ≤ (residueIndices 2 D).card)
    (hnot31 : ¬ ∃ β, residueWeight 2 D β = 3) (α : ℕ →₀ ℕ) :
    residueWeight 2 (intervalCore n c * D) α ≤ 2 * Nat.sqrt n + 2 * Nat.sqrt (n / 2) :=
  residueWeight_mul_four_not_three_one 2 _ D _ _
    (Nat.sqrt_le_sqrt (Nat.div_le_self n 2)) (residueWeight_intervalCore_zero_le n c hc)
    (residueWeight_intervalCore_nonzero_le n c hc) hD hclasses hnot31 α

end WeightedPilz
