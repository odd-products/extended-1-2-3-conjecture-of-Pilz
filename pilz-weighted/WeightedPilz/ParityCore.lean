import WeightedPilz.ParityDecomposition

/-! Exact occupied parity classes and the weighted squarefree decomposition
of the interval core. All dilation maps leave coefficients unchanged. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K]

theorem residuePart_polynomialOf (q : ℕ) (A : Finset ℕ) (c : ℕ → K)
    (α : ℕ →₀ ℕ) :
    residuePart q (polynomialOf A c) α =
      polynomialOf (A.filter (fun a => residueExponent q a.factorization = α)) c := by
  classical
  ext d
  rw [coeff_residuePart]
  simp only [polynomialOf, coeff_sum, Finset.sum_filter, apply_ite, coeff_zero]
  by_cases hr : residueExponent q d = α
  · rw [if_pos hr]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases he : a.factorization = d
    · simp [coeff_monomial, he, hr]
    · simp [coeff_monomial, he]
  · rw [if_neg hr]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    by_cases he : a.factorization = d
    · simp [coeff_monomial, he, hr]
    · simp [coeff_monomial, he]

theorem residueIndices_interval_parity (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) :
    residueIndices 2 (interval n c) =
      (Arithmetic.squarefreeNumbers n).image Nat.factorization := by
  rw [← interval_parity_indices n]
  ext α
  constructor
  · intro h
    simp only [residueIndices, Finset.mem_image] at h
    obtain ⟨d, hd, hres⟩ := h
    rw [support_interval n c hc] at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr ⟨a, ha, hres⟩
  · intro h
    obtain ⟨a, ha, hres⟩ := Finset.mem_image.mp h
    simp only [residueIndices, Finset.mem_image]
    refine ⟨a.factorization, ?_, hres⟩
    rw [support_interval n c hc]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

theorem intervalCore_parity_indices (n : ℕ) :
    ((Finset.Icc 1 n \ intervalFreshPrimes n).image
      (fun a => residueExponent 2 a.factorization)) =
      (Arithmetic.squarefreeNumbers n \ intervalFreshPrimes n).image Nat.factorization := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨haI, hanot⟩ := Finset.mem_sdiff.mp ha
    have hapos : 0 < a := (Finset.mem_Icc.mp haI).1
    obtain ⟨s, b, hs, hb, hmul, hsq⟩ := Nat.sq_mul_squarefree_of_pos hapos
    have hdiv : s ∣ a := ⟨b ^ 2, by simpa [Nat.mul_comm] using hmul.symm⟩
    have hsn : s ≤ n := (Nat.le_of_dvd hapos hdiv).trans (Finset.mem_Icc.mp haI).2
    have hsnot : s ∉ intervalFreshPrimes n := by
      intro hsf
      have hsa := Pilz.eq_freshPrime_of_dvd hsf haI hdiv
      exact hanot (hsa.symm ▸ hsf)
    refine Finset.mem_image.mpr ⟨s, Finset.mem_sdiff.mpr
      ⟨(Arithmetic.mem_squarefreeNumbers n s).mpr ⟨hs, hsn, hsq⟩, hsnot⟩, ?_⟩
    symm
    exact (squarefree_residue_iff hsq hapos).mpr
      ⟨b, hb, by simpa [Nat.mul_comm] using hmul.symm⟩
  · intro hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hsI, hsnot⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hspos, hsn, hsq⟩ := (Arithmetic.mem_squarefreeNumbers n s).mp hsI
    exact Finset.mem_image.mpr ⟨s, Finset.mem_sdiff.mpr
      ⟨Finset.mem_Icc.mpr ⟨hspos, hsn⟩, hsnot⟩, residue_factorization_squarefree hsq⟩

theorem residueIndices_intervalCore_parity (n : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) :
    residueIndices 2 (intervalCore n c) =
      (Arithmetic.squarefreeNumbers n \ intervalFreshPrimes n).image Nat.factorization := by
  rw [← intervalCore_parity_indices n]
  ext α
  constructor
  · intro h
    simp only [residueIndices, Finset.mem_image] at h
    obtain ⟨d, hd, hres⟩ := h
    rw [intervalCore_support n c hc] at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr ⟨a, ha, hres⟩
  · intro h
    obtain ⟨a, ha, hres⟩ := Finset.mem_image.mp h
    simp only [residueIndices, Finset.mem_image]
    refine ⟨a.factorization, ?_, hres⟩
    rw [intervalCore_support n c hc]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

theorem intervalCore_parity_class_eq_interval (n s : ℕ) (c : ℕ → K)
    (hs : Squarefree s) (hsnot : s ∉ intervalFreshPrimes n) :
    residuePart 2 (intervalCore n c) s.factorization =
      residuePart 2 (interval n c) s.factorization := by
  rw [intervalCore, interval, residuePart_polynomialOf, residuePart_polynomialOf]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨ha, hres⟩
    refine ⟨⟨ha, ?_⟩, hres⟩
    intro haf
    have hp := ((Pilz.mem_freshPrimes_iff n a).mp haf).1
    rw [residue_factorization_squarefree hp.squarefree] at hres
    have has := Nat.factorization_inj hp.ne_zero hs.ne_zero hres
    exact hsnot (has ▸ haf)

theorem intervalCore_parity_class (n s : ℕ) (c : ℕ → K)
    (hs : Squarefree s) (hsnot : s ∉ intervalFreshPrimes n) :
    residuePart 2 (intervalCore n c) s.factorization =
      monomialOf s * dilate 2 (interval (Nat.sqrt (n / s)) (fun b => c (s * b ^ 2))) := by
  rw [intervalCore_parity_class_eq_interval n s c hs hsnot, interval_parity_class n s c hs]

theorem intervalCore_parity_root (n s : ℕ) (c : ℕ → K)
    (hs : Squarefree s) (hsnot : s ∉ intervalFreshPrimes n) :
    residueRoot 2 (intervalCore n c) s.factorization =
      interval (Nat.sqrt (n / s)) (fun b => c (s * b ^ 2)) := by
  have he := intervalCore_parity_class n s c hs hsnot
  rw [residuePart_eq_monomial_mul_dilate] at he
  change monomial s.factorization 1 * dilate 2 _ =
    monomial s.factorization 1 * dilate 2 _ at he
  apply dilate_injective (by decide : 0 < 2)
  exact mul_left_cancel₀ (by simp : (monomial s.factorization (1 : K) : Poly K) ≠ 0) he

theorem intervalCore_parity_class_weight (n s : ℕ) (c : ℕ → K)
    (hc : NonzeroWeights n c) (hs : Squarefree s) (hsnot : s ∉ intervalFreshPrimes n) :
    residueWeight 2 (intervalCore n c) s.factorization = Nat.sqrt (n / s) := by
  unfold residueWeight
  rw [intervalCore_parity_class_eq_interval n s c hs hsnot]
  exact interval_parity_class_weight n s c hc hs

end WeightedPilz
