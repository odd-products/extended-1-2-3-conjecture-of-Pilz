import WeightedPilz.IntervalFresh
import WeightedPilz.Dilation
import WeightedPilz.ResidueCapacity
import WeightedPilz.Arithmetic.ParityBudgets

/-! Squarefree labels for the exact weighted parity decomposition.
Exponent dilation retains coefficients, so no square roots of coefficients are needed. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma residue_factorization_squarefree {s : ℕ} (hs : Squarefree s) :
    residueExponent 2 s.factorization = s.factorization := by
  ext p
  apply Nat.mod_eq_of_lt
  have h := (Nat.squarefree_iff_factorization_le_one hs.ne_zero).mp hs p
  omega

lemma residue_factorization_mul_square {s b : ℕ} (hs : 0 < s) (hb : 0 < b) :
    residueExponent 2 (s * b ^ 2).factorization = residueExponent 2 s.factorization := by
  rw [Nat.factorization_mul hs.ne' (pow_ne_zero _ hb.ne'), Nat.factorization_pow]
  ext p
  simp [residueExponent_apply, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, Nat.add_mod]

lemma squarefree_residue_iff {s a : ℕ} (hs : Squarefree s) (ha : 0 < a) :
    residueExponent 2 a.factorization = s.factorization ↔
      ∃ b : ℕ, 0 < b ∧ a = s * b ^ 2 := by
  constructor
  · intro hres
    obtain ⟨t, b, ht, hb, hmul, htsq⟩ := Nat.sq_mul_squarefree_of_pos ha
    have hres' : residueExponent 2 a.factorization = t.factorization := by
      rw [← hmul, Nat.mul_comm]
      rw [residue_factorization_mul_square ht hb, residue_factorization_squarefree htsq]
    have hts : t = s := Nat.factorization_inj ht.ne' hs.ne_zero (hres'.symm.trans hres)
    refine ⟨b, hb, ?_⟩
    simpa [hts, Nat.mul_comm] using hmul.symm
  · rintro ⟨b, hb, rfl⟩
    rw [residue_factorization_mul_square (Nat.pos_of_ne_zero hs.ne_zero) hb,
      residue_factorization_squarefree hs]

lemma square_interval_bound {n s b : ℕ} (hs : 0 < s) :
    b ≤ Nat.sqrt (n / s) ↔ s * b ^ 2 ≤ n := by
  rw [Nat.le_sqrt, Nat.le_div_iff_mul_le hs]
  simp only [pow_two, Nat.mul_comm]

lemma interval_parity_indices (n : ℕ) :
    ((Finset.Icc 1 n).image (fun a => residueExponent 2 a.factorization)) =
      (Arithmetic.squarefreeNumbers n).image Nat.factorization := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨s, b, hs, hb, hmul, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Finset.mem_Icc.mp ha).1
    have hsa : s ≤ a := Nat.le_of_dvd (Finset.mem_Icc.mp ha).1
      ⟨b ^ 2, by simpa [Nat.mul_comm] using hmul.symm⟩
    refine Finset.mem_image.mpr ⟨s, (Arithmetic.mem_squarefreeNumbers n s).mpr
      ⟨hs, hsa.trans (Finset.mem_Icc.mp ha).2, hsq⟩, ?_⟩
    symm
    apply (squarefree_residue_iff hsq (Finset.mem_Icc.mp ha).1).mpr
    exact ⟨b, hb, by simpa [Nat.mul_comm] using hmul.symm⟩
  · intro hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hs1, hsn, hsq⟩ := (Arithmetic.mem_squarefreeNumbers n s).mp hs
    exact Finset.mem_image.mpr ⟨s, Finset.mem_Icc.mpr ⟨hs1, hsn⟩,
      residue_factorization_squarefree hsq⟩

variable {K : Type*} [Field K]

private lemma residuePart_sum' (q : ℕ) {ι : Type*} (A : Finset ι)
    (f : ι → Poly K) (α : ℕ →₀ ℕ) :
    residuePart q (∑i∈A, f i) α = ∑i∈A, residuePart q (f i) α := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [residuePart, Finsupp.filter_zero]
  | @insert i A hi ih => simp only [Finset.sum_insert hi, residuePart_add, ih]

private lemma dilate_sum' (q : ℕ) {ι : Type*} (A : Finset ι) (f : ι → Poly K) :
    dilate q (∑i∈A, f i) = ∑i∈A, dilate q (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih => simp only [Finset.sum_insert hi, dilate_add, ih]

/-- The squarefree class `s` inherits precisely the weights `c(s*b²)`. -/
theorem interval_parity_class (n s : ℕ) (c : ℕ → K) (hs : Squarefree s) :
    residuePart 2 (interval n c) s.factorization =
      monomialOf s * dilate 2 (interval (Nat.sqrt (n / s)) (fun b => c (s * b ^ 2))) := by
  classical
  have hspos := Nat.pos_of_ne_zero hs.ne_zero
  have hR : monomialOf s * dilate 2
      (interval (Nat.sqrt (n / s)) (fun b => c (s * b ^ 2))) =
      ∑b∈Finset.Icc 1 (Nat.sqrt (n / s)), monomial (s * b ^ 2).factorization (c (s * b ^ 2)) := by
    unfold interval polynomialOf
    rw [dilate_sum', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hbpos : 0 < b := (Finset.mem_Icc.mp hb).1
    rw [dilate_monomial, monomialOf, monomial_mul, one_mul,
      Nat.factorization_mul hs.ne_zero (pow_ne_zero _ hbpos.ne'), Nat.factorization_pow]
    rfl
  rw [hR, interval, polynomialOf, residuePart_sum']
  simp only [residuePart_monomial]
  trans ∑ a ∈ (Finset.Icc 1 n).filter
      (fun a => residueExponent 2 a.factorization = s.factorization),
        monomial a.factorization (c a)
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> rfl
  symm
  apply Finset.sum_bij (fun b _ => s * b ^ 2)
  · intro b hb
    have hbpos := (Finset.mem_Icc.mp hb).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hspos (pow_pos hbpos 2),
      (square_interval_bound hspos).mp (Finset.mem_Icc.mp hb).2⟩, ?_⟩
    exact (squarefree_residue_iff hs (Nat.mul_pos hspos (pow_pos hbpos 2))).mpr ⟨b, hbpos, rfl⟩
  · intro b hb b' hb' heq
    have hsq : b ^ 2 = b' ^ 2 := Nat.eq_of_mul_eq_mul_left hspos heq
    nlinarith
  · intro a ha
    obtain ⟨haI, hares⟩ := Finset.mem_filter.mp ha
    obtain ⟨b, hb, hab⟩ := (squarefree_residue_iff hs (Finset.mem_Icc.mp haI).1).mp hares
    refine ⟨b, Finset.mem_Icc.mpr ⟨hb, ?_⟩, hab.symm⟩
    apply (square_interval_bound hspos).mpr
    rw [← hab]
    exact (Finset.mem_Icc.mp haI).2
  · intro b hb
    rfl

theorem interval_parity_class_weights (n s : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hs : Squarefree s) :
    NonzeroWeights (Nat.sqrt (n / s)) (fun b => c (s * b ^ 2)) := by
  intro b hb
  exact hc _ (Finset.mem_Icc.mpr
    ⟨Nat.mul_pos (Nat.pos_of_ne_zero hs.ne_zero) (pow_pos (Finset.mem_Icc.mp hb).1 2),
      (square_interval_bound (Nat.pos_of_ne_zero hs.ne_zero)).mp (Finset.mem_Icc.mp hb).2⟩)

theorem interval_parity_class_weight (n s : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hs : Squarefree s) :
    residueWeight 2 (interval n c) s.factorization = Nat.sqrt (n / s) := by
  rw [residueWeight, interval_parity_class n s c hs, monomialOf,
    weight_monomial_mul, weight_dilate (by decide : 0 < 2),
    weight_interval _ _ (interval_parity_class_weights n s c hc hs)]

end WeightedPilz
