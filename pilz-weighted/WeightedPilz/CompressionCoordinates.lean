import WeightedPilz.VariableSlices
import WeightedPilz.CoefficientExtension
import WeightedPilz.Fresh

/-! The invertible change from individual fresh variables to their sum. -/

noncomputable section
namespace WeightedPilz.Compression
open MvPolynomial
open scoped BigOperators

variable {σ K L : Type*} [DecidableEq σ]

section Ring
variable [CommRing K]

def freshRest (V : Finset σ) (j : σ) : MvPolynomial σ K := ∑ i ∈ V.erase j, X i

def sumChangeMap (V : Finset σ) (j : σ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (fun i => if i = j then X j + freshRest V j else X i)

def sumUnchangeMap (V : Finset σ) (j : σ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (fun i => if i = j then X j - freshRest V j else X i)

@[simp] theorem sumChangeMap_C (V : Finset σ) (j : σ) (c : K) :
    sumChangeMap V j (C c) = C c := by simp [sumChangeMap]

@[simp] theorem sumUnchangeMap_C (V : Finset σ) (j : σ) (c : K) :
    sumUnchangeMap V j (C c) = C c := by simp [sumUnchangeMap]

@[simp] theorem sumChangeMap_X (V : Finset σ) (j i : σ) :
    sumChangeMap (K := K) V j (X i) = if i = j then X j + freshRest V j else X i := by
  simp [sumChangeMap]

@[simp] theorem sumUnchangeMap_X (V : Finset σ) (j i : σ) :
    sumUnchangeMap (K := K) V j (X i) = if i = j then X j - freshRest V j else X i := by
  simp [sumUnchangeMap]

@[simp] theorem sumChangeMap_rest (V : Finset σ) (j : σ) :
    sumChangeMap (K := K) V j (freshRest V j) = freshRest V j := by
  simp only [freshRest, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_erase.mp hi |>.1]

@[simp] theorem sumUnchangeMap_rest (V : Finset σ) (j : σ) :
    sumUnchangeMap (K := K) V j (freshRest V j) = freshRest V j := by
  simp only [freshRest, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_erase.mp hi |>.1]

/-- Replace the distinguished fresh variable by the sum of all fresh variables. -/
def sumChange (V : Finset σ) (j : σ) : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (sumChangeMap V j) (sumUnchangeMap V j)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      by_cases hi : i = j
      · subst i; simp [AlgHom.comp_apply]
      · simp [AlgHom.comp_apply, hi])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      by_cases hi : i = j
      · subst i; simp [AlgHom.comp_apply]
      · simp [AlgHom.comp_apply, hi])

@[simp] theorem sumChange_apply (V : Finset σ) (j : σ) (P : MvPolynomial σ K) :
    sumChange V j P = sumChangeMap V j P := rfl

@[simp] theorem sumChange_symm_apply (V : Finset σ) (j : σ) (P : MvPolynomial σ K) :
    (sumChange V j).symm P = sumUnchangeMap V j P := rfl

theorem sumChange_X_self (V : Finset σ) (j : σ) (hj : j ∈ V) :
    sumChange (K := K) V j (X j) = ∑ i ∈ V, X i := by
  simp only [sumChange_apply, sumChangeMap_X, if_pos rfl, freshRest]
  exact Finset.add_sum_erase V (fun i => (X i : MvPolynomial σ K)) hj

theorem sumChange_eq_self (V : Finset σ) (j : σ) (P : MvPolynomial σ K)
    (hj : j ∉ P.vars) : sumChange V j P = P := by
  change (sumChange V j).toRingHom P = (RingHom.id _) P
  apply MvPolynomial.hom_congr_vars
  · ext c
    simp
  · intro i hi _
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [hij]
  · rfl

theorem map_sumChange [CommRing L] (f : K →+* L) (V : Finset σ) (j : σ)
    (P : MvPolynomial σ K) :
    MvPolynomial.map f (sumChange V j P) = sumChange V j (MvPolynomial.map f P) := by
  have h : (MvPolynomial.map f).comp (sumChange V j).toRingHom =
      (sumChange V j).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i
      by_cases hi : i = j
      · subst i; simp [freshRest]
      · simp [hi]
  exact RingHom.congr_fun h P

end Ring

section Projection
variable [CommRing K] [CommRing L] [Algebra K L]

theorem coeffProject_add (φ : L →ₗ[K] K) (P Q : MvPolynomial σ L) :
    coeffProject φ (P + Q) = coeffProject φ P + coeffProject φ Q := by
  ext d
  simp [coeff_coeffProject]

theorem coeffProject_C (φ : L →ₗ[K] K) (c : L) :
    coeffProject (σ := σ) φ (C c) = C (φ c) := by
  ext d
  simp only [coeff_coeffProject, coeff_C]
  by_cases hd : d = 0 <;> simp [hd, eq_comm]

/-- Coefficient extraction commutes with a substitution defined over the
base field, even though extraction is only linear. -/
theorem coeffProject_substitution (φ : L →ₗ[K] K) (f : σ → MvPolynomial σ K)
    (P : MvPolynomial σ L) :
    coeffProject φ (eval₂Hom C (fun i => MvPolynomial.map (algebraMap K L) (f i)) P) =
      aeval f (coeffProject φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [coeffProject_C]
  | add P Q hP hQ => simp only [map_add, coeffProject_add, hP, hQ]
  | mul_X P i hP =>
    have hPX : coeffProject φ (P * X i) = coeffProject φ P * X i := by
      rw [mul_comm, ← MvPolynomial.map_X (algebraMap K L) i, coeffProject_mul_map,
        mul_comm]
    rw [map_mul, eval₂Hom_X', mul_comm, coeffProject_mul_map, hP,
      hPX, map_mul, aeval_X, mul_comm]

theorem coeffProject_sumChange (φ : L →ₗ[K] K) (V : Finset σ) (j : σ)
    (P : MvPolynomial σ L) :
    coeffProject φ (sumChange V j P) = sumChange V j (coeffProject φ P) := by
  have hh : (sumChange (K := L) V j).toRingHom =
      eval₂Hom C (fun i => MvPolynomial.map (algebraMap K L)
        (if i = j then X j + freshRest V j else X i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i
      by_cases hi : i = j <;> simp [hi, freshRest]
  change coeffProject φ ((sumChange V j).toRingHom P) = _
  rw [hh, coeffProject_substitution]
  rfl

end Projection

end WeightedPilz.Compression
