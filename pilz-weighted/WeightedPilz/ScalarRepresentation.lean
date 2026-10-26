import WeightedPilz.CompressionExtraction

/-! Expand the extracted polynomial as a scalar polynomial in the fresh sum. -/

noncomputable section
namespace WeightedPilz.Compression
open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- Explicit finite scalar representation of the output of compression.
Every coefficient is independent of every designated fresh coordinate. -/
theorem sumChange_scalar_representation (V : Finset σ) (j : σ) (hj : j ∈ V)
    (D : MvPolynomial σ K) (hD : ∀ i ∈ V.erase j, i ∉ D.vars) :
    ∃ (N : Finset ℕ) (A : ℕ → MvPolynomial σ K),
      (∀ n i, i ∈ V → i ∉ (A n).vars) ∧
      sumChange V j D = ∑ n ∈ N, A n * (∑ i ∈ V, X i) ^ n := by
  have hrow : ∀ n : ℕ, ∃ A : MvPolynomial σ K,
      coordinatePart j n D = monomial (Finsupp.single j n) 1 * A ∧
      (A.vars : Set σ) ⊆ {i | i ≠ j} := by
    intro n
    rw [coordinatePart_eq_outsideSlice]
    apply outsideSlice_division
    ext i
    by_cases hi : i = j <;> simp [outsideExponent_apply, hi, Finsupp.single_apply]
  choose A hfactor hbase using hrow
  have hA : ∀ n i, i ∈ V → i ∉ (A n).vars := by
    intro n i hi himem
    by_cases hij : i = j
    · exact hbase n himem hij
    · obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars i).mp himem
      have hprod : Finsupp.single j n + d ∈ (monomial (Finsupp.single j n) 1 * A n).support := by
        have hs : (monomial (Finsupp.single j n) 1 * A n).support =
            (A n).support.map (addLeftEmbedding (Finsupp.single j n)) :=
          AddMonoidAlgebra.support_single_mul (A n) 1 (by simp) (Finsupp.single j n)
        rw [hs]
        exact Finset.mem_map.mpr ⟨d, hd, rfl⟩
      rw [← hfactor n, support_coordinatePart] at hprod
      have hdD := (Finset.mem_filter.mp hprod).1
      have hzero := MvPolynomial.mem_support_notMem_vars_zero hdD
        (hD i (Finset.mem_erase.mpr ⟨hij, hi⟩))
      have hdi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hdi
      apply hdi'
      simpa [Finsupp.single_apply, hij] using hzero
  let N := D.support.image (fun d => d j)
  have hsum : (∑ n ∈ N, coordinatePart j n D) = D := by
    ext d
    rw [MvPolynomial.coeff_sum]
    simp only [coeff_coordinatePart]
    by_cases hd : d ∈ D.support
    · have hn : d j ∈ N := Finset.mem_image.mpr ⟨d, hd, rfl⟩
      simp [hn]
    · simp [MvPolynomial.notMem_support_iff.mp hd]
  refine ⟨N, A, hA, ?_⟩
  calc
    sumChange V j D = sumChange V j (∑ n ∈ N, coordinatePart j n D) := congrArg _ hsum.symm
    _ = ∑ n ∈ N, A n * (∑ i ∈ V, X i) ^ n := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [hfactor n, map_mul, sumChange_eq_self V j (A n) (hA n j hj)]
      rw [← X_pow_eq_monomial, map_pow, sumChange_X_self V j hj, mul_comm]

end WeightedPilz.Compression
