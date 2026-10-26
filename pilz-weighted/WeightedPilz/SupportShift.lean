import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic

/-!
Finite filtered linear algebra for `lem:two-variable-shift` in the frozen
weighted manuscript. All coefficient fields are arbitrary. Coordinate order is
increasing exponent of the first of the two fresh variables.
-/

namespace WeightedPilz.SupportShift

open scoped BigOperators
open Module

variable {K : Type*} [Field K]

/-- Triangular vectors with nonzero diagonal are linearly independent. -/
theorem linearIndependent_of_above_eq_zero {ι : Type*} [LinearOrder ι]
    (v : ι → ι → K) (hdiag : ∀ i, v i i ≠ 0)
    (htri : ∀ i j, i < j → v i j = 0) : LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci
  let t := s.filter (fun j ↦ c j ≠ 0)
  have ht : t.Nonempty := ⟨i, by simp [t, hi, hci]⟩
  obtain ⟨j, hj, hmax⟩ := t.exists_max_image id ht
  have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hzero := congrFun hsum j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hzero
  have hone : (∑ k ∈ s, c k * v k j) = c j * v j j := by
    apply Finset.sum_eq_single j
    · intro k hks hkj
      by_cases hck : c k = 0
      · simp [hck]
      · have hkle : k ≤ j := hmax k (by simp [t, hks, hck])
        rw [htri k j (lt_of_le_of_ne hkle hkj), mul_zero]
    · intro h
      exact (h hjs).elim
  rw [hone] at hzero
  exact (mul_ne_zero hcj (hdiag j)) hzero

/-- A pivot is the greatest nonzero coordinate of some vector in a subspace. -/
def IsPivot {n : ℕ} (W : Submodule K (Fin n → K)) (i : Fin n) : Prop :=
  ∃ v ∈ W, v i ≠ 0 ∧ ∀ j, i < j → v j = 0

/-- The pivot coordinates of a finite-dimensional coordinate subspace. -/
noncomputable def pivots {n : ℕ} (W : Submodule K (Fin n → K)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (IsPivot W)

@[simp] theorem mem_pivots {n : ℕ} (W : Submodule K (Fin n → K)) (i : Fin n) :
    i ∈ pivots W ↔ IsPivot W i := by
  classical
  simp [pivots]

/-- Every nonzero vector has a largest occupied coordinate, which is a pivot. -/
theorem exists_pivot_of_ne_zero {n : ℕ} {W : Submodule K (Fin n → K)}
    {v : Fin n → K} (hv : v ∈ W) (hv0 : v ≠ 0) :
    ∃ i ∈ pivots W, v i ≠ 0 ∧ ∀ j, i < j → v j = 0 := by
  classical
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv0 (funext h)
  let s := Finset.univ.filter (fun i ↦ v i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [s, hi]⟩
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image id hs
  have hvi : v i ≠ 0 := (Finset.mem_filter.mp hi).2
  have habove : ∀ j, i < j → v j = 0 := by
    intro j hij
    by_contra hj
    have hji : j ≤ i := hmax j (by simp [s, hj])
    exact (not_le_of_gt hij) hji
  exact ⟨i, (mem_pivots W i).2 ⟨v, hv, hvi, habove⟩, hvi, habove⟩

/-- Restricting a subspace vector to its pivot coordinates loses no information. -/
noncomputable def pivotRestriction {n : ℕ} (W : Submodule K (Fin n → K)) :
    W →ₗ[K] ((pivots W) → K) where
  toFun v i := v.1 i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pivotRestriction_injective {n : ℕ} (W : Submodule K (Fin n → K)) :
    Function.Injective (pivotRestriction W) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  apply Subtype.ext
  by_contra hv0
  obtain ⟨i, hi, hvi, _⟩ := exists_pivot_of_ne_zero v.property hv0
  exact hvi (congrFun hv ⟨i, hi⟩)

/-- Pivot cardinality equals dimension; this is the field-independent replacement
for a computed row-reduced echelon form. -/
theorem card_pivots {n : ℕ} (W : Submodule K (Fin n → K)) :
    (pivots W).card = finrank K W := by
  classical
  apply Nat.le_antisymm
  · choose v hv hdiag htri using
      (fun i : pivots W ↦ (mem_pivots W i.1).1 i.2)
    let u : pivots W → W := fun i ↦ ⟨v i, hv i⟩
    have hli : LinearIndependent K (fun i : pivots W ↦ fun j : pivots W ↦ v i j.1) :=
      linearIndependent_of_above_eq_zero _ hdiag
        (fun i j hij ↦ htri i j.1 hij)
    have hu : LinearIndependent K u := by
      apply LinearIndependent.of_comp (f := pivotRestriction W)
      exact hli
    simpa only [Fintype.card_coe] using hu.fintype_card_le_finrank
  · have h := (pivotRestriction W).finrank_le_finrank_of_injective
      (pivotRestriction_injective W)
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Nat.mul_one, Fintype.card_coe] using h

/-- Restriction to any specified coordinate set, as a linear map. -/
noncomputable def coordinateRestriction {n : ℕ} (A : Finset (Fin n)) :
    (Fin n → K) →ₗ[K] (A → K) where
  toFun v a := v a.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Triangularity gives the exact dimension of a chosen set of columns. -/
theorem finrank_span_columns {n : ℕ} (A : Finset (Fin n))
    (M : Fin n → Fin n → K) (hdiag : ∀ a ∈ A, M a a ≠ 0)
    (htri : ∀ a j, j < a → M a j = 0) :
    finrank K (Submodule.span K (M '' (A : Set (Fin n)))) = A.card := by
  classical
  have hli : LinearIndependent K (fun a : A ↦ M a.1) := by
    apply LinearIndependent.of_comp (coordinateRestriction A)
    exact linearIndependent_of_above_eq_zero (ι := OrderDual A)
      (fun a b ↦ M a.1 b.1) (fun a ↦ hdiag a.1 a.2)
      (fun a b hba ↦ htri a.1 b.1 hba)
  have hset : M '' (A : Set (Fin n)) = Set.range (fun a : A ↦ M a.1) := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
  rw [hset, finrank_span_eq_card hli, Fintype.card_coe]

/-- Above every coordinate threshold there are at least as many shifted pivots
as original columns. This is the sorted-coordinate domination assertion of the
support-shift lemma, expressed without choosing enumerations. -/
theorem pivot_threshold_domination {n : ℕ} (A : Finset (Fin n))
    (M : Fin n → Fin n → K) (hdiag : ∀ a ∈ A, M a a ≠ 0)
    (htri : ∀ a j, j < a → M a j = 0) (t : ℕ) :
    (A.filter (fun a ↦ t ≤ a.1)).card ≤
      ((pivots (Submodule.span K (M '' (A : Set (Fin n))))).filter
        (fun a ↦ t ≤ a.1)).card := by
  classical
  let A' := A.filter (fun a ↦ t ≤ a.1)
  let U := Submodule.span K (M '' (A' : Set (Fin n)))
  let W := Submodule.span K (M '' (A : Set (Fin n)))
  have hUW : U ≤ W := Submodule.span_mono (Set.image_mono (by
    intro a ha
    exact (Finset.mem_filter.mp ha).1))
  have hvanish : ∀ v ∈ U, ∀ j : Fin n, j.1 < t → v j = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      intro j hj
      apply htri
      have hat : t ≤ a.1 := (Finset.mem_filter.mp ha).2
      change j.1 < a.1
      omega
    | zero => simp
    | add v w _ _ hv hw =>
      intro j hj
      simp [hv j hj, hw j hj]
    | smul c v _ hv =>
      intro j hj
      simp [hv j hj]
  have hsubset : pivots U ⊆ (pivots W).filter (fun a ↦ t ≤ a.1) := by
    intro i hi
    obtain ⟨v, hv, hvi, habove⟩ := (mem_pivots U i).1 hi
    apply Finset.mem_filter.mpr
    refine ⟨(mem_pivots W i).2 ⟨v, hUW hv, hvi, habove⟩, ?_⟩
    by_contra hti
    exact hvi (hvanish v hv i (lt_of_not_ge hti))
  calc
    A'.card = finrank K U := (finrank_span_columns A' M
      (fun a ha ↦ hdiag a (Finset.mem_filter.mp ha).1) htri).symm
    _ = (pivots U).card := (card_pivots U).symm
    _ ≤ ((pivots W).filter (fun a ↦ t ≤ a.1)).card := Finset.card_le_card hsubset

theorem sum_smul_single_apply {n : ℕ} (A : Finset (Fin n)) (c : Fin n → K)
    (j : Fin n) :
    (∑ a ∈ A, c a • (Pi.single a (1 : K) : Fin n → K)) j = if j ∈ A then c j else 0 := by
  classical
  simp [Finset.sum_apply, Pi.single_apply, mul_ite]

/-- A coordinate span consists exactly of vectors vanishing elsewhere. -/
theorem mem_span_single_iff {n : ℕ} (A : Finset (Fin n)) (v : Fin n → K) :
    v ∈ Submodule.span K ((fun a ↦ Pi.single a (1 : K)) '' (A : Set (Fin n))) ↔
      ∀ j ∉ A, v j = 0 := by
  classical
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      intro j hj
      have hja : j ≠ a := fun h ↦ hj (h.symm ▸ ha)
      simp [hja]
    | zero => simp
    | add v w _ _ hv hw =>
      intro j hj
      simp [hv j hj, hw j hj]
    | smul c v _ hv =>
      intro j hj
      simp [hv j hj]
  · intro hv
    have heq : v = ∑ a ∈ A, v a • (Pi.single a (1 : K) : Fin n → K) := by
      ext j
      rw [sum_smul_single_apply]
      by_cases hj : j ∈ A
      · simp [hj]
      · simp [hj, hv j hj]
    rw [heq]
    apply Submodule.sum_mem
    intro a ha
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

/-- If an upper-triangular family has exactly its original coordinates as
pivots, every original coordinate vector belongs to its span. -/
theorem single_mem_of_pivots_eq {n : ℕ} (A : Finset (Fin n))
    (M : Fin n → Fin n → K) (hdiag : ∀ a ∈ A, M a a ≠ 0)
    (htri : ∀ a j, j < a → M a j = 0)
    (hfixed : pivots (Submodule.span K (M '' (A : Set (Fin n)))) = A) :
    ∀ a ∈ A, Pi.single a (1 : K) ∈ Submodule.span K (M '' (A : Set (Fin n))) := by
  classical
  let W := Submodule.span K (M '' (A : Set (Fin n)))
  have hind : ∀ q : ℕ, ∀ a : Fin n, n - a.1 = q → a ∈ A → Pi.single a (1 : K) ∈ W := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro a haq ha
      let S := A.filter (fun b ↦ a < b)
      let v : Fin n → K := M a - ∑ b ∈ S, M a b • (Pi.single b (1 : K) : Fin n → K)
      have hv : v ∈ W := by
        refine W.sub_mem (show M a ∈ W from Submodule.subset_span ⟨a, ha, rfl⟩) ?_
        apply Submodule.sum_mem
        intro b hb
        apply Submodule.smul_mem
        have hab : a.1 < b.1 := (Finset.mem_filter.mp hb).2
        exact ih (n - b.1) (by omega) b rfl (Finset.mem_filter.mp hb).1
      have hva : v a = M a a := by
        simp only [v, Pi.sub_apply, sum_smul_single_apply]
        simp [S]
      have hv0 : v ≠ 0 := by
        intro h
        have := congrFun h a
        rw [hva] at this
        exact hdiag a ha this
      obtain ⟨b, hb, hvb, habove⟩ := exists_pivot_of_ne_zero hv hv0
      have hbA : b ∈ A := by simpa only [W, hfixed] using hb
      have hba : b = a := by
        by_contra hba
        rcases lt_or_gt_of_ne hba with hlt | hgt
        · have := habove a hlt
          rw [hva] at this
          exact hdiag a ha this
        · have hbS : b ∈ S := Finset.mem_filter.mpr ⟨hbA, hgt⟩
          have : v b = 0 := by
            simp only [v, Pi.sub_apply, sum_smul_single_apply, if_pos hbS, sub_self]
          exact hvb this
      have heq : v = (M a a) • (Pi.single a (1 : K) : Fin n → K) := by
        ext j
        by_cases hja : j = a
        · subst j
          simp [hva]
        · have hzero : v j = 0 := by
            rcases lt_or_gt_of_ne hja with hlt | hgt
            · have hjS : j ∉ S := by simp [S, not_lt_of_gt hlt]
              simp only [v, Pi.sub_apply, sum_smul_single_apply, if_neg hjS,
                htri a j hlt, sub_zero]
            · exact habove j (hba ▸ hgt)
          simp [hzero, hja]
      have hscale := Submodule.smul_mem W (M a a)⁻¹ hv
      rw [heq, smul_smul, inv_mul_cancel₀ (hdiag a ha), one_smul] at hscale
      exact hscale
  intro a ha
  exact hind (n - a.1) a rfl ha

/-- Unchanged pivot support forces preservation of the coordinate span. -/
theorem columns_supported_of_pivots_eq {n : ℕ} (A : Finset (Fin n))
    (M : Fin n → Fin n → K) (hdiag : ∀ a ∈ A, M a a ≠ 0)
    (htri : ∀ a j, j < a → M a j = 0)
    (hfixed : pivots (Submodule.span K (M '' (A : Set (Fin n)))) = A) :
    ∀ a ∈ A, ∀ j ∉ A, M a j = 0 := by
  classical
  let V := Submodule.span K ((fun a ↦ Pi.single a (1 : K)) '' (A : Set (Fin n)))
  let W := Submodule.span K (M '' (A : Set (Fin n)))
  have hVW : V ≤ W := by
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, rfl⟩
    exact single_mem_of_pivots_eq A M hdiag htri hfixed a ha
  have hdimV : finrank K V = A.card := by
    apply finrank_span_columns
    · intro a _
      simp
    · intro a j hja
      simp [ne_of_lt hja]
  have hdimW : finrank K W = A.card := finrank_span_columns A M hdiag htri
  have heq : V = W := Submodule.eq_of_le_of_finrank_eq hVW (hdimV.trans hdimW.symm)
  intro a ha j hj
  have hm : M a ∈ V := heq ▸ Submodule.subset_span ⟨a, ha, rfl⟩
  exact (mem_span_single_iff A (M a)).1 hm j hj

/-- A formal one-parameter upper-triangular deformation. The parameter is the
polynomial variable, while the index records the exponent in the fresh pair. -/
noncomputable def deform {n : ℕ} (A : Finset (Fin n))
    (M : Fin n → Fin n → K) (h : Fin n → Polynomial K) (k : Fin n) : Polynomial K :=
  ∑ a ∈ A, Polynomial.C (M a k) *
    (h a * Polynomial.X ^ (k.1 - a.1))

/-- The coefficient used to cut across a diagonal of the parameter/exponent
grading. The explicit zero branch handles negative parameter degrees. -/
noncomputable def diagonalCoeff {n : ℕ} (h : Fin n → Polynomial K)
    (D : ℕ) (k a : Fin n) : K :=
  if k.1 ≤ D + a.1 then (h a).coeff (D + a.1 - k.1) else 0

theorem coeff_deform_diagonal {n : ℕ} (A : Finset (Fin n))
    (M : Fin n → Fin n → K) (htri : ∀ a j, j < a → M a j = 0)
    (h : Fin n → Polynomial K) (D : ℕ) (k j : Fin n) (hkj : k ≤ j) :
    (deform A M h j).coeff (D + j.1 - k.1) =
      ∑ a ∈ A, diagonalCoeff h D k a * M a j := by
  classical
  simp only [deform, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases haj : a ≤ j
  · rw [Polynomial.coeff_mul_X_pow']
    have hle : j.1 - a.1 ≤ D + j.1 - k.1 ↔ k.1 ≤ D + a.1 := by
      have : a.1 ≤ j.1 := haj
      have : k.1 ≤ j.1 := hkj
      omega
    by_cases hka : k.1 ≤ D + a.1
    · rw [if_pos (hle.mpr hka), diagonalCoeff, if_pos hka]
      have heq : D + j.1 - k.1 - (j.1 - a.1) = D + a.1 - k.1 := by
        have : a.1 ≤ j.1 := haj
        have : k.1 ≤ j.1 := hkj
        omega
      rw [heq, mul_comm]
    · rw [if_neg (fun ht ↦ hka (hle.mp ht)), diagonalCoeff, if_neg hka]
      simp
  · rw [htri a j (lt_of_not_ge haj)]
    simp

/-- The highest parameter coefficient of a polynomial combination of the
deformed columns lies on the pivot coordinates of the undeformed column span.
This is the main support-containment mechanism in the two-variable shift. -/
theorem highest_coeff_supported_on_pivots {n : ℕ} (A : Finset (Fin n))
    (M : Fin n → Fin n → K) (htri : ∀ a j, j < a → M a j = 0)
    (h : Fin n → Polynomial K) (D : ℕ)
    (hD : ∀ j, (deform A M h j).natDegree ≤ D) :
    ∀ k, (deform A M h k).coeff D ≠ 0 →
      k ∈ pivots (Submodule.span K (M '' (A : Set (Fin n)))) := by
  classical
  intro k hk
  let W := Submodule.span K (M '' (A : Set (Fin n)))
  let v : Fin n → K := ∑ a ∈ A, diagonalCoeff h D k a • M a
  have hv : v ∈ W := by
    apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  have hvj : ∀ j, k ≤ j → v j = (deform A M h j).coeff (D + j.1 - k.1) := by
    intro j hkj
    simpa only [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      (coeff_deform_diagonal A M htri h D k j hkj).symm
  apply (mem_pivots W k).2
  refine ⟨v, hv, ?_, ?_⟩
  · simpa [hvj k le_rfl] using hk
  · intro j hkj
    rw [hvj j hkj.le]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hkjn : k.1 < j.1 := hkj
    exact lt_of_le_of_lt (hD j) (by omega)

/-- Coefficients of `X^a (X+1)^(d-a)`, the specialization at parameter one
of `X^a (Y+tX)^(d-a)` after dehomogenizing at `Y=1`. -/
noncomputable def shiftMatrix (d : ℕ) (a k : Fin (d + 1)) : K :=
  if a ≤ k then ((d - a.1).choose (k.1 - a.1) : K) else 0

theorem shiftMatrix_eq_coeff (d : ℕ) (a k : Fin (d + 1)) :
    shiftMatrix (K := K) d a k =
      ((Polynomial.X : Polynomial K) ^ a.1 *
        (Polynomial.X + 1) ^ (d - a.1)).coeff k.1 := by
  rw [Polynomial.coeff_X_pow_mul']
  simp only [Polynomial.coeff_X_add_one_pow, shiftMatrix]
  rfl

@[simp] theorem shiftMatrix_diag (d : ℕ) (a : Fin (d + 1)) :
    shiftMatrix (K := K) d a a = 1 := by
  simp [shiftMatrix]

theorem shiftMatrix_below (d : ℕ) (a k : Fin (d + 1)) (h : k < a) :
    shiftMatrix (K := K) d a k = 0 := by
  simp [shiftMatrix, not_le_of_gt h]

/-- The support selected by the two-variable shift; no characteristic is fixed. -/
noncomputable def shiftedSupport (d : ℕ) (A : Finset (Fin (d + 1))) :
    Finset (Fin (d + 1)) :=
  pivots (Submodule.span K (shiftMatrix (K := K) d '' (A : Set (Fin (d + 1)))))

theorem shiftedSupport_card (d : ℕ) (A : Finset (Fin (d + 1))) :
    (shiftedSupport (K := K) d A).card = A.card := by
  rw [shiftedSupport, card_pivots]
  exact finrank_span_columns A (shiftMatrix d) (by simp) (shiftMatrix_below d)

theorem shiftedSupport_threshold (d : ℕ) (A : Finset (Fin (d + 1))) (t : ℕ) :
    (A.filter (fun a ↦ t ≤ a.1)).card ≤
      ((shiftedSupport (K := K) d A).filter (fun a ↦ t ≤ a.1)).card :=
  pivot_threshold_domination A (shiftMatrix d) (by simp) (shiftMatrix_below d) t

/-- The formal parameter shift creates no coordinate outside `A` when the
shifted support is unchanged. -/
theorem shift_fixed_support {d : ℕ} (A : Finset (Fin (d + 1)))
    (hfixed : shiftedSupport (K := K) d A = A) (h : Fin (d + 1) → Polynomial K) :
    ∀ j ∉ A, deform A (shiftMatrix d) h j = 0 := by
  classical
  intro j hj
  apply Finset.sum_eq_zero
  intro a ha
  have hm := columns_supported_of_pivots_eq A (shiftMatrix (K := K) d)
    (by simp) (shiftMatrix_below d) hfixed a ha j hj
  simp [hm]

/-- Highest-parameter-coefficient statement for every polynomial combination
of the shifted monomials, including combinations with polynomial parameters. -/
theorem shift_highest_coeff {d : ℕ} (A : Finset (Fin (d + 1)))
    (h : Fin (d + 1) → Polynomial K) (D : ℕ)
    (hD : ∀ j, (deform A (shiftMatrix d) h j).natDegree ≤ D) :
    ∀ k, (deform A (shiftMatrix d) h k).coeff D ≠ 0 →
      k ∈ shiftedSupport (K := K) d A :=
  highest_coeff_supported_on_pivots A (shiftMatrix d) (shiftMatrix_below d) h D hD

/-- Membership of a polynomial vector in a rational-function span admits a
single nonzero polynomial denominator. This makes the `K(t)` interpretation
of the shifted-span statement explicit. -/
theorem clear_denominators_of_vector_span {ι κ : Type*} [Fintype ι]
    (g : ι → κ → Polynomial K) (F : κ → Polynomial K)
    (hF : (fun k ↦ algebraMap (Polynomial K) (RatFunc K) (F k)) ∈
      Submodule.span (RatFunc K)
        (Set.range (fun i ↦ fun k ↦ algebraMap (Polynomial K) (RatFunc K) (g i k)))) :
    ∃ q : Polynomial K, q ≠ 0 ∧ ∃ h : ι → Polynomial K,
      ∀ k, q * F k = ∑ i, h i * g i k := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (RatFunc K)).1 hF
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) c
  choose h hh using hq
  refine ⟨q.1, mem_nonZeroDivisors_iff_ne_zero.mp q.2, h, ?_⟩
  intro k
  apply IsFractionRing.injective (Polynomial K) (RatFunc K)
  have hck := congrFun hc k
  simp only [Finset.sum_apply] at hck
  change (∑ i, c i * algebraMap (Polynomial K) (RatFunc K) (g i k)) =
    algebraMap (Polynomial K) (RatFunc K) (F k) at hck
  rw [map_mul, ← hck, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, hh i, Algebra.smul_def, mul_assoc]

/-- Clearing denominators does not change the support of the highest parameter
coefficient: it multiplies that coefficient by the denominator's leading
coefficient. -/
theorem highest_coeff_of_cleared_deform {n : ℕ} (A : Finset (Fin n))
    (M : Fin n → Fin n → K) (htri : ∀ a j, j < a → M a j = 0)
    (F : Fin n → Polynomial K) (D : ℕ) (hD : ∀ j, (F j).natDegree ≤ D)
    (q : Polynomial K) (hq : q ≠ 0) (h : Fin n → Polynomial K)
    (hclear : ∀ j, q * F j = deform A M h j) :
    ∀ k, (F k).coeff D ≠ 0 →
      k ∈ pivots (Submodule.span K (M '' (A : Set (Fin n)))) := by
  intro k hk
  apply highest_coeff_supported_on_pivots A M htri h (q.natDegree + D)
  · intro j
    rw [← hclear j]
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left (hD j) _)
  · rw [← hclear k, Polynomial.coeff_mul_add_eq_of_natDegree_le le_rfl (hD k),
      Polynomial.coeff_natDegree]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq) hk

/-- The full `K(t)` leading-coefficient assertion of the support shift. The
polynomial vector itself need not have polynomial coordinates in the spanning
family; its membership is taken over the rational function field. -/
theorem highest_coeff_of_rational_span {n : ℕ} (A : Finset (Fin n))
    (M : Fin n → Fin n → K) (htri : ∀ a j, j < a → M a j = 0)
    (F : Fin n → Polynomial K) (D : ℕ) (hD : ∀ j, (F j).natDegree ≤ D)
    (hF : (fun k ↦ algebraMap (Polynomial K) (RatFunc K) (F k)) ∈
      Submodule.span (RatFunc K) (Set.range (fun a : A ↦ fun k ↦
        algebraMap (Polynomial K) (RatFunc K)
          (Polynomial.C (M a.1 k) * Polynomial.X ^ (k.1 - a.1.1))))) :
    ∀ k, (F k).coeff D ≠ 0 →
      k ∈ pivots (Submodule.span K (M '' (A : Set (Fin n)))) := by
  classical
  let g : A → Fin n → Polynomial K := fun a k ↦
    Polynomial.C (M a.1 k) * Polynomial.X ^ (k.1 - a.1.1)
  obtain ⟨q, hq, h, hclear⟩ := clear_denominators_of_vector_span g F hF
  let h' : Fin n → Polynomial K := fun a ↦ if ha : a ∈ A then h ⟨a, ha⟩ else 0
  apply highest_coeff_of_cleared_deform A M htri F D hD q hq h'
  intro k
  rw [hclear k]
  calc
    (∑ a : A, h a * g a k) =
        ∑ a : A, Polynomial.C (M a.1 k) *
          (h' a.1 * Polynomial.X ^ (k.1 - a.1.1)) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [g, h', dif_pos a.2]
      ring
    _ = deform A M h' k := Finset.sum_coe_sort A
      (fun a : Fin n ↦ Polynomial.C (M a k) * (h' a * Polynomial.X ^ (k.1 - a.1)))

/-- Matrix of the actual formal transvection on homogeneous degree `d`, with
coefficients in `K(t)`. Its `a,k` entry is
`choose (d-a) (k-a) * t^(k-a)` for `k ≥ a`, and zero otherwise. -/
noncomputable def rationalShiftMatrix (d : ℕ) (a k : Fin (d + 1)) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K)
    (Polynomial.C (shiftMatrix (K := K) d a k) * Polynomial.X ^ (k.1 - a.1))

@[simp] theorem rationalShiftMatrix_diag (d : ℕ) (a : Fin (d + 1)) :
    rationalShiftMatrix (K := K) d a a = 1 := by
  simp [rationalShiftMatrix]

theorem rationalShiftMatrix_below (d : ℕ) (a k : Fin (d + 1)) (h : k < a) :
    rationalShiftMatrix (K := K) d a k = 0 := by
  simp [rationalShiftMatrix, shiftMatrix_below d a k h]

/-- Formal-parameter invariance, as equality of subspaces over `K(t)`. -/
theorem rational_shift_span_fixed {d : ℕ} (A : Finset (Fin (d + 1)))
    (hfixed : shiftedSupport (K := K) d A = A) :
    Submodule.span (RatFunc K)
        (rationalShiftMatrix (K := K) d '' (A : Set (Fin (d + 1)))) =
      Submodule.span (RatFunc K)
        ((fun a ↦ Pi.single a (1 : RatFunc K)) '' (A : Set (Fin (d + 1)))) := by
  classical
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro v ⟨a, ha, rfl⟩
    apply (mem_span_single_iff A _).2
    intro k hk
    have hm := columns_supported_of_pivots_eq A (shiftMatrix (K := K) d)
      (by simp) (shiftMatrix_below d) hfixed a ha k hk
    simp [rationalShiftMatrix, hm]
  · rw [finrank_span_columns A (rationalShiftMatrix d) (by simp)
      (rationalShiftMatrix_below d)]
    symm
    apply finrank_span_columns
    · simp
    · intro a j hja
      simp [ne_of_lt hja]

/-- The three assertions of `lem:two-variable-shift`. The comparison is given
in its equivalent threshold-count form; the leading coefficient is the
coefficient at any common upper degree bound, so zero vectors are harmless. -/
theorem two_variable_shift (d : ℕ) (A : Finset (Fin (d + 1))) :
    ∃ B : Finset (Fin (d + 1)),
      B.card = A.card ∧
      (∀ t : ℕ, (A.filter (fun a ↦ t ≤ a.1)).card ≤
        (B.filter (fun b ↦ t ≤ b.1)).card) ∧
      (∀ (F : Fin (d + 1) → Polynomial K) (D : ℕ),
        (∀ j, (F j).natDegree ≤ D) →
        (fun k ↦ algebraMap (Polynomial K) (RatFunc K) (F k)) ∈
          Submodule.span (RatFunc K)
            (Set.range (fun a : A ↦ rationalShiftMatrix (K := K) d a.1)) →
        ∀ k, (F k).coeff D ≠ 0 → k ∈ B) ∧
      (B = A → Submodule.span (RatFunc K)
        (rationalShiftMatrix (K := K) d '' (A : Set (Fin (d + 1)))) =
        Submodule.span (RatFunc K)
          ((fun a ↦ Pi.single a (1 : RatFunc K)) '' (A : Set (Fin (d + 1))))) := by
  refine ⟨shiftedSupport (K := K) d A, shiftedSupport_card d A,
    shiftedSupport_threshold d A, ?_, rational_shift_span_fixed A⟩
  intro F D hD hF
  exact highest_coeff_of_rational_span A (shiftMatrix d) (shiftMatrix_below d) F D hD hF

/-- The sum of all upper-tail counts is the exponent sum plus cardinality. -/
theorem sum_tail_counts {n : ℕ} (A : Finset (Fin n)) :
    (∑ t ∈ Finset.range (n + 1), (A.filter (fun a ↦ t ≤ a.1)).card) =
      (∑ a ∈ A, a.1) + A.card := by
  classical
  calc
    (∑ t ∈ Finset.range (n + 1), (A.filter (fun a ↦ t ≤ a.1)).card) =
        ∑ t ∈ Finset.range (n + 1), ∑ a ∈ A, if t ≤ a.1 then 1 else 0 := by
      simp
    _ = ∑ a ∈ A, ∑ t ∈ Finset.range (n + 1), if t ≤ a.1 then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ a ∈ A, (a.1 + 1) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_boole]
      have heq : (Finset.range (n + 1)).filter (fun t ↦ t ≤ a.1) =
          Finset.range (a.1 + 1) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_range]
        have := a.isLt
        omega
      simp [heq]
    _ = (∑ a ∈ A, a.1) + A.card := by simp [Finset.sum_add_distrib]

/-- Upper-tail counts determine a finite coordinate support exactly. -/
theorem eq_of_tail_counts_eq {n : ℕ} (A B : Finset (Fin n))
    (h : ∀ t ≤ n, (A.filter (fun a ↦ t ≤ a.1)).card =
      (B.filter (fun b ↦ t ≤ b.1)).card) : A = B := by
  classical
  have hstep : ∀ (S : Finset (Fin n)) (a : Fin n),
      (S.filter (fun b ↦ a.1 ≤ b.1)).card =
        (S.filter (fun b ↦ a.1 + 1 ≤ b.1)).card + if a ∈ S then 1 else 0 := by
    intro S a
    by_cases ha : a ∈ S
    · have heq : S.filter (fun b ↦ a.1 ≤ b.1) =
          insert a (S.filter (fun b ↦ a.1 + 1 ≤ b.1)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hb, hab⟩
          by_cases hba : b = a
          · exact Or.inl hba
          · exact Or.inr ⟨hb, by have : b.1 ≠ a.1 := Fin.val_ne_of_ne hba; omega⟩
        · rintro (rfl | ⟨hb, hab⟩)
          · exact ⟨ha, le_rfl⟩
          · exact ⟨hb, by omega⟩
      rw [heq, Finset.card_insert_of_notMem (by simp), if_pos ha]
    · have heq : S.filter (fun b ↦ a.1 ≤ b.1) =
          S.filter (fun b ↦ a.1 + 1 ≤ b.1) := by
        ext b
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hb, hab⟩
          have hba : b ≠ a := fun hba ↦ ha (hba ▸ hb)
          exact ⟨hb, by have : b.1 ≠ a.1 := Fin.val_ne_of_ne hba; omega⟩
        · rintro ⟨hb, hab⟩
          exact ⟨hb, by omega⟩
      rw [heq, if_neg ha, add_zero]
  ext a
  have h0 := h a.1 a.isLt.le
  have h1 := h (a.1 + 1) a.isLt
  rw [hstep A a, hstep B a, h1] at h0
  split_ifs at h0 <;> simp_all

/-- Threshold domination raises the exponent sum, strictly unless the two
supports agree. This is the finite potential used in scalar compression. -/
theorem exponent_sum_lt_of_shift {n : ℕ} (A B : Finset (Fin n))
    (hcard : A.card = B.card)
    (hdom : ∀ t : ℕ, (A.filter (fun a ↦ t ≤ a.1)).card ≤
      (B.filter (fun b ↦ t ≤ b.1)).card) (hne : A ≠ B) :
    (∑ a ∈ A, a.1) < ∑ b ∈ B, b.1 := by
  classical
  have hle := Finset.sum_le_sum (s := Finset.range (n + 1)) (fun t _ ↦ hdom t)
  rw [sum_tail_counts A, sum_tail_counts B, hcard] at hle
  have hsumle : (∑ a ∈ A, a.1) ≤ ∑ b ∈ B, b.1 := by omega
  apply lt_of_le_of_ne hsumle
  intro heq
  have hall : ∀ t ∈ Finset.range (n + 1),
      (A.filter (fun a ↦ t ≤ a.1)).card = (B.filter (fun b ↦ t ≤ b.1)).card := by
    apply (Finset.sum_eq_sum_iff_of_le (fun t _ ↦ hdom t)).1
    rw [sum_tail_counts A, sum_tail_counts B, heq, hcard]
  apply hne
  apply eq_of_tail_counts_eq A B
  intro t ht
  exact hall t (Finset.mem_range.mpr (by omega))

/-- Every nontrivial two-variable support shift strictly increases the first
fresh exponent's sum. This supplies strictness in the compression potential. -/
theorem shiftedSupport_sum_lt {d : ℕ} (A : Finset (Fin (d + 1)))
    (hne : shiftedSupport (K := K) d A ≠ A) :
    (∑ a ∈ A, a.1) < ∑ b ∈ shiftedSupport (K := K) d A, b.1 := by
  apply exponent_sum_lt_of_shift A (shiftedSupport (K := K) d A)
    (shiftedSupport_card d A).symm (shiftedSupport_threshold d A)
  exact Ne.symm hne

end WeightedPilz.SupportShift
