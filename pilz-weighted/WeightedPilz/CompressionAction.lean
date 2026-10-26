import WeightedPilz.CompressionBlocks

/-! Exact identification of the balanced polynomial action with the
characteristic-independent pair matrix in `SupportShift`. -/

noncomputable section

namespace WeightedPilz.Compression

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [DecidableEq σ] [Field K]

def aboveIndex {d : ℕ} (a : Fin (d + 1)) (k : Fin (d - a.val + 1)) : Fin (d + 1) :=
  ⟨a.val + k.val, by omega⟩

theorem sum_aboveIndex {M : Type*} [AddCommMonoid M] {d : ℕ}
    (a : Fin (d + 1)) (f : Fin (d + 1) → M) :
    (∑ k : Fin (d - a.val + 1), f (aboveIndex a k)) =
      ∑ k : Fin (d + 1), if a ≤ k then f k else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ ↦ aboveIndex a k)
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change a.val ≤ a.val + k.val
    omega
  · intro k _ l _ h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [aboveIndex] at this
    omega
  · intro k hk
    have hak : a.val ≤ k.val := (Finset.mem_filter.mp hk).2
    refine ⟨⟨k.val - a.val, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp [aboveIndex]
    omega
  · intro k _
    rfl

theorem formalBalanced_sum {ι : Type*} (T : Finset ι) (f : ι → MvPolynomial σ K)
    (i j : σ) :
    formalBalanced i j (∑ a ∈ T, f a) = ∑ a ∈ T, formalBalanced i j (f a) := by
  simp only [formalBalanced, map_sum]

/-- One monomial's full formal action in the finite homogeneous pair basis. -/
theorem formalBalanced_pairExponent (i j : σ) (hij : i ≠ j) (b : σ →₀ ℕ)
    (hbi : b i = 0) (hbj : b j = 0) (d : ℕ) (a : Fin (d + 1)) (c : K) :
    formalBalanced i j (monomial (pairExponent i j b d a) c) =
      ∑ k : Fin (d + 1), monomial (pairExponent i j b d k)
        (Polynomial.C (SupportShift.shiftMatrix (K := K) d a k) *
          ((Polynomial.C c * (1 - Polynomial.X) ^ a.val) *
            Polynomial.X ^ (k.val - a.val))) := by
  unfold formalBalanced
  rw [MvPolynomial.map_monomial]
  unfold pairExponent
  rw [balancedMap_monomial_pair i j hij _ b hbi hbj]
  rw [← Fin.sum_univ_eq_sum_range]
  have hterm (k : Fin (d - a.val + 1)) :
      monomial (b + Finsupp.single i (a.val + k.val) +
        Finsupp.single j (d - a.val - k.val))
        (Polynomial.C c * (1 - Polynomial.X) ^ a.val *
          (1 - (1 - Polynomial.X)) ^ k.val * ((d - a.val).choose k.val : Polynomial K)) =
      monomial (pairExponent i j b d (aboveIndex a k))
        (Polynomial.C (SupportShift.shiftMatrix (K := K) d a (aboveIndex a k)) *
          ((Polynomial.C c * (1 - Polynomial.X) ^ a.val) *
            Polynomial.X ^ ((aboveIndex a k).val - a.val))) := by
    have hak : a ≤ aboveIndex a k := by change a.val ≤ a.val + k.val; omega
    have hsub : d - a.val - k.val = d - (a.val + k.val) := by omega
    rw [SupportShift.shiftMatrix, if_pos hak]
    simp only [pairExponent, aboveIndex,
      Nat.add_sub_cancel_left, map_natCast, hsub, sub_sub_cancel]
    congr 1
    ring
  simp_rw [hterm]
  rw [sum_aboveIndex a (fun k ↦ monomial (pairExponent i j b d k)
    (Polynomial.C (SupportShift.shiftMatrix (K := K) d a k) *
      ((Polynomial.C c * (1 - Polynomial.X) ^ a.val) *
        Polynomial.X ^ (k.val - a.val))))]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hak
  · rfl
  · simp [SupportShift.shiftMatrix, hak]

/-- The action on a whole pair block is exactly `SupportShift.deform`. -/
theorem formalBalanced_pair_block (i j : σ) (hij : i ≠ j) (b : σ →₀ ℕ)
    (hbi : b i = 0) (hbj : b j = 0) (d : ℕ) (A : Finset (Fin (d + 1)))
    (c : Fin (d + 1) → K) :
    formalBalanced i j (∑ a ∈ A, monomial (pairExponent i j b d a) (c a)) =
      ∑ k : Fin (d + 1), monomial (pairExponent i j b d k)
        (SupportShift.deform A (SupportShift.shiftMatrix (K := K) d)
          (fun a ↦ Polynomial.C (c a) * (1 - Polynomial.X) ^ a.val) k) := by
  rw [formalBalanced_sum]
  simp_rw [formalBalanced_pairExponent i j hij b hbi hbj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [SupportShift.deform, map_sum]

/-- The balanced action fixes a fresh completion even when its base part is
zero; scalar compression does not require the extra nonvanishing hypotheses
used later by the weighted distance theorem. -/
theorem formalBalanced_core_sum (V : Finset σ) (C₀ : MvPolynomial σ K)
    (i j : σ) (hi : i ∈ V) (hj : j ∈ V) (hij : i ≠ j)
    (hiC : i ∉ C₀.vars) (hjC : j ∉ C₀.vars) :
    formalBalanced i j (C₀ + ∑ k ∈ V, X k) =
      MvPolynomial.map Polynomial.C (C₀ + ∑ k ∈ V, X k) := by
  have hiC' : i ∉ (MvPolynomial.map Polynomial.C C₀).vars :=
    fun h ↦ hiC (MvPolynomial.vars_map C₀ Polynomial.C h)
  have hjC' : j ∉ (MvPolynomial.map Polynomial.C C₀).vars :=
    fun h ↦ hjC (MvPolynomial.vars_map C₀ Polynomial.C h)
  unfold formalBalanced
  rw [map_add, map_sum]
  simp only [MvPolynomial.map_X]
  rw [map_add, balancedMap_eq_self i j (1 - Polynomial.X) _ hiC' hjC',
    balancedMap_sum V i j hi hj hij]

theorem formalBalanced_highest_multiple_of_fixed (P : MvPolynomial σ K)
    (i j : σ) (hfixed : formalBalanced i j P = MvPolynomial.map Polynomial.C P)
    (G : MvPolynomial σ K) (hG : G ≠ 0) (hdiv : P ∣ G) :
    parameterCoeff (parameterDegree (formalBalanced i j G)) (formalBalanced i j G) ≠ 0 ∧
      P ∣ parameterCoeff (parameterDegree (formalBalanced i j G)) (formalBalanced i j G) := by
  apply highest_parameterCoeff_multiple P _ (formalBalanced_ne_zero i j G hG)
  obtain ⟨H, rfl⟩ := hdiv
  refine ⟨formalBalanced i j H, ?_⟩
  have hprod : formalBalanced i j (P * H) =
      formalBalanced i j P * formalBalanced i j H := by
    simp only [formalBalanced, map_mul]
  rw [hprod, hfixed]

end WeightedPilz.Compression
