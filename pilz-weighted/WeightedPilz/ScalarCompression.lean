import WeightedPilz.CompressionAdmissibility
import WeightedPilz.ScalarRepresentation

/-! Assembly of `thm:compression` over the original, arbitrary field. -/
noncomputable section
namespace WeightedPilz.Compression
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- Scalar support compression, including exact base-exponent preservation.
The finite expansion records dependence only on the aggregate fresh sum.
The core may be zero, and the field may be finite or imperfect. -/
theorem scalar_support_compression (V : Finset σ) (hV : V.Nonempty)
    (C₀ : MvPolynomial σ K) (hind : ∀ i ∈ V, i ∉ C₀.vars)
    (G : MvPolynomial σ K) (hG : G ≠ 0) (hdiv : (C₀ + ∑ i ∈ V, X i) ∣ G) :
    ∃ F : MvPolynomial σ K, F ≠ 0 ∧ (C₀ + ∑ i ∈ V, X i) ∣ F ∧
      weight F ≤ weight G ∧
      (∀ d ∈ F.support, ∃ e ∈ G.support, ∀ i ∉ V, d i = e i) ∧
      (∀ i ∉ V, widthOf i F ≤ widthOf i G) ∧
      ∃ (N : Finset ℕ) (A : ℕ → MvPolynomial σ K),
        (∀ n i, i ∈ V → i ∉ (A n).vars) ∧ F = ∑ n ∈ N, A n * (∑ i ∈ V, X i) ^ n := by
  classical
  obtain ⟨j, hj⟩ := hV
  let P := C₀ + ∑ i ∈ V, (X i : MvPolynomial σ K)
  obtain ⟨S, hS, hadm, hmax⟩ := exists_maximal_profile V (pivotWeight j) P G hG hdiv
  have hstable : StableSupport (K := K) V j S := by
    intro i hi Q hQ n
    obtain ⟨hij, hiV⟩ := Finset.mem_erase.mp hi
    have hadm' := pairShift_admissible_of_fresh V C₀ hind S i j hiV hj hij hadm
    have hfixed := pairBlocksFixed_of_maximal V G.support S P i j hiV hj hij hS hmax hadm'
    exact parameterCoeff_formalBalanced_support_subset S i j hij
      (pairStable_of_pairBlocksFixed S i j hij hfixed) Q hQ n
  obtain ⟨G₀, hG₀, hPG₀, hG₀S⟩ := hadm
  obtain ⟨D, α, hD, hDvars, hdivD, hweightD, hα, htranslated⟩ :=
    scalar_extraction V j hj C₀ hind S hstable G₀ hG₀ hPG₀ hG₀S
  let F := sumChange V j D
  have hF : F ≠ 0 := by
    intro hz
    apply hD
    exact (sumChange (K := K) V j).injective (by simpa only [map_zero] using hz)
  have hbase : ∀ d ∈ F.support, ∃ e ∈ G.support, ∀ i ∉ V, d i = e i := by
    intro d hd
    have hmem : α + d ∈ (monomial α 1 * F).support := by
      have hs : (monomial α 1 * F).support = F.support.map (addLeftEmbedding α) :=
        AddMonoidAlgebra.support_single_mul F 1 (by simp) α
      rw [hs]
      exact Finset.mem_map.mpr ⟨d, hd, rfl⟩
    obtain ⟨e, he, heq⟩ := hS.base_match (htranslated hmem)
    refine ⟨e, he, ?_⟩
    intro i hi
    simpa only [Finsupp.add_apply, hα i (Or.inl hi), zero_add] using heq i hi
  refine ⟨F, hF, hdivD, ?_, hbase, ?_, ?_⟩
  · exact hweightD.trans (le_of_eq hS.card_eq.symm)
  · intro i hi
    apply widthOf_mono_exponents i hF
    intro d hd
    obtain ⟨e, he, heq⟩ := hbase d hd
    exact ⟨e, he, heq i hi⟩
  · exact sumChange_scalar_representation V j hj D hDvars

/-- The multiplier formulation needed by minimum-cofactor-width descent. -/
theorem scalar_support_compression_multiplier (V : Finset σ) (hV : V.Nonempty)
    (C₀ : MvPolynomial σ K) (hind : ∀ i ∈ V, i ∉ C₀.vars)
    (H : MvPolynomial σ K) (hproduct : (C₀ + ∑ i ∈ V, X i) * H ≠ 0) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧
      weight ((C₀ + ∑ i ∈ V, X i) * J) ≤ weight ((C₀ + ∑ i ∈ V, X i) * H) ∧
      (∀ i ∉ V, widthOf i ((C₀ + ∑ k ∈ V, X k) * J) ≤
        widthOf i ((C₀ + ∑ k ∈ V, X k) * H)) ∧
      ∃ (N : Finset ℕ) (A : ℕ → MvPolynomial σ K),
        (∀ n i, i ∈ V → i ∉ (A n).vars) ∧
        (C₀ + ∑ i ∈ V, X i) * J = ∑ n ∈ N, A n * (∑ i ∈ V, X i) ^ n := by
  obtain ⟨F, hF, ⟨J, hJ⟩, hw, _, hwidth, hscalar⟩ :=
    scalar_support_compression V hV C₀ hind _ hproduct (dvd_mul_right _ H)
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hF
    rw [hJ, hz, mul_zero]
  · simpa only [← hJ] using hw
  · simpa only [← hJ] using hwidth
  · simpa only [← hJ] using hscalar

end WeightedPilz.Compression
