import WeightedPilz.IntervalFresh
import WeightedPilz.ResidueCapacity
import Mathlib.Data.Nat.Factorization.Root

/-! Integer labels bound the size of each full exponent-residue class. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators Pointwise
variable {K : Type*} [Field K]

/-- Every supported exponent encodes a positive integer at most `N`. -/
def IntegerSupported (N : ℕ) (P : Poly K) : Prop :=
  ∀ d ∈ P.support, ∃ a : ℕ, 0 < a ∧ a ≤ N ∧ a.factorization = d

theorem integerSupported_intervalCore (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) : IntegerSupported n (intervalCore n c) := by
  intro d hd
  rw [intervalCore_support n c hc] at hd
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hd
  have hab := Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1
  exact ⟨a, hab.1, hab.2, heq⟩

theorem IntegerSupported.mul {M N : ℕ} {P Q : Poly K}
    (hP : IntegerSupported M P) (hQ : IntegerSupported N Q) :
    IntegerSupported (M * N) (P * Q) := by
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  obtain ⟨m, hm, hmM, hma⟩ := hP a ha
  obtain ⟨n, hn, hnN, hnb⟩ := hQ b hb
  refine ⟨m * n, Nat.mul_pos hm hn, Nat.mul_le_mul hmM hnN, ?_⟩
  rw [Nat.factorization_mul hm.ne' hn.ne', hma, hnb]

theorem IntegerSupported.pow {N : ℕ} {P : Poly K}
    (hP : IntegerSupported N P) (j : ℕ) : IntegerSupported (N ^ j) (P ^ j) := by
  induction j with
  | zero =>
      intro d hd
      have hd0 : d = 0 := by
        by_contra hne
        have hc := MvPolynomial.mem_support_iff.mp hd
        rw [pow_zero] at hc
        have hone : MvPolynomial.coeff d (1 : Poly K) = if 0 = d then 1 else 0 :=
          MvPolynomial.coeff_one d
        rw [hone, if_neg (Ne.symm hne)] at hc
        exact hc rfl
      exact ⟨1, by decide, by simp, by simpa using hd0.symm⟩
  | succ j ih => simpa only [pow_succ] using ih.mul hP

private def residueRootLabel (q : ℕ) (d : ℕ →₀ ℕ) : ℕ :=
  Nat.floorRoot q (d.prod (· ^ ·))

private theorem residueRootLabel_eq (q : ℕ) {a : ℕ} (ha : 0 < a) :
    residueRootLabel q a.factorization = Nat.floorRoot q a := by
  rw [residueRootLabel, Nat.factorization_prod_pow_eq_self ha.ne']

/-- Exact integer version of the residue-capacity estimate: a class of
integer labels at most `N` has at most `m` members when `N < (m+1)^q`.
The injection removes the common exponent remainder, not merely total degree. -/
theorem residueWeight_le_of_integerSupported (q N m : ℕ) (hq : 0 < q)
    (P : Poly K) (hP : IntegerSupported N P) (hNm : N < (m + 1) ^ q)
    (α : ℕ →₀ ℕ) : residueWeight q P α ≤ m := by
  let A := (residuePart q P α).support
  have hlabel : ∀ d ∈ A, ∃ a : ℕ, 0 < a ∧ a ≤ N ∧ a.factorization = d := by
    intro d hd
    exact hP d (support_residuePart_subset q P α hd)
  have hmaps : ∀ d ∈ A, residueRootLabel q d ∈ Finset.Icc 1 m := by
    intro d hd
    obtain ⟨a, ha, haN, rfl⟩ := hlabel d hd
    rw [residueRootLabel_eq q ha]
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨hq.ne', ha.ne'⟩), ?_⟩
    have hpow : Nat.floorRoot q a ^ q ≤ N :=
      (Nat.le_of_dvd ha Nat.floorRoot_pow_dvd).trans haN
    by_contra hnot
    have hle : m + 1 ≤ Nat.floorRoot q a := by omega
    have hmono := Nat.pow_le_pow_left hle q
    omega
  have hinj : Set.InjOn (residueRootLabel q) (A : Set (ℕ →₀ ℕ)) := by
    intro d hd e he hde
    obtain ⟨a, ha, _, had⟩ := hlabel d hd
    obtain ⟨b, hb, _, hbe⟩ := hlabel e he
    have hresd : residueExponent q d = α := by
      by_contra hne
      have hc := MvPolynomial.mem_support_iff.mp hd
      rw [coeff_residuePart, if_neg hne] at hc
      exact hc rfl
    have hrese : residueExponent q e = α := by
      by_contra hne
      have hc := MvPolynomial.mem_support_iff.mp he
      rw [coeff_residuePart, if_neg hne] at hc
      exact hc rfl
    have hroots : Nat.floorRoot q a = Nat.floorRoot q b := by
      simpa only [← had, ← hbe, residueRootLabel_eq q ha, residueRootLabel_eq q hb] using hde
    have hquot := congrArg Nat.factorization hroots
    rw [Nat.factorization_floorRoot, Nat.factorization_floorRoot, had, hbe] at hquot
    ext i
    have hdiv : d i / q = e i / q := by
      simpa using congrArg (fun f : ℕ →₀ ℕ => f i) hquot
    have hmod : d i % q = e i % q :=
      congrArg (fun f : ℕ →₀ ℕ => f i) (hresd.trans hrese.symm)
    have hdv := Nat.mod_add_div (d i) q
    have hev := Nat.mod_add_div (e i) q
    rw [hmod, hdiv] at hdv
    exact hdv.symm.trans hev
  have hcard : A.card ≤ (Finset.Icc 1 m).card := by
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro b hb
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
    exact hmaps d hd
  simpa only [Nat.card_Icc, Nat.add_sub_cancel, A] using hcard

theorem residueSigma_le_of_integerSupported (q N m : ℕ) (hq : 0 < q)
    (P : Poly K) (hP : IntegerSupported N P) (hNm : N < (m + 1) ^ q) :
    residueSigma q P ≤ m := by
  apply Finset.sup_le
  intro α _
  exact residueWeight_le_of_integerSupported q N m hq P hP hNm α

theorem residueSigma_intervalCore_pow_le (n q j m : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hq : 0 < q) (hNm : n ^ j < (m + 1) ^ q) :
    residueSigma q (intervalCore n c ^ j) ≤ m :=
  residueSigma_le_of_integerSupported q (n ^ j) m hq _
    ((integerSupported_intervalCore n c hc).pow j) hNm

end WeightedPilz
