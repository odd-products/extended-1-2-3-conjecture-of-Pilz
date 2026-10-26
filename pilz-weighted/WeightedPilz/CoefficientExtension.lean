import WeightedPilz.Distance
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Coefficient extension and descent for the frozen weighted manuscript.

The coefficientwise projection used here is linear, not multiplicative. It
nevertheless commutes with multiplication by a polynomial whose coefficients
lie in the base field. A dual functional detecting a nonzero output coefficient
therefore gives a nonzero descended multiple, with both supports contained in
the original supports. No finite-dimensionality or perfectness assumption is
needed.
-/

namespace WeightedPilz

open MvPolynomial

variable {σ K L : Type*}

/-- A faithful coefficient map preserves exactly the monomial support. -/
theorem support_map_eq [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (hf : Function.Injective f) (P : MvPolynomial σ K) :
    (MvPolynomial.map f P).support = P.support :=
  MvPolynomial.support_map_of_injective P hf

/-- A faithful coefficient map preserves weight. -/
theorem weight_map_eq [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (hf : Function.Injective f) (P : MvPolynomial σ K) :
    weight (MvPolynomial.map f P) = weight P := by
  simp only [weight, support_map_eq f hf]

section Projection

variable [CommSemiring K] [CommSemiring L] [Algebra K L]

/-- Apply a base-field linear functional to every coefficient. -/
noncomputable def coeffProject (φ : L →ₗ[K] K) (P : MvPolynomial σ L) :
    MvPolynomial σ K := Finsupp.mapRange φ φ.map_zero P

@[simp]
theorem coeff_coeffProject (φ : L →ₗ[K] K) (P : MvPolynomial σ L)
    (m : σ →₀ ℕ) :
    coeff m (coeffProject φ P) = φ (coeff m P) := rfl

theorem support_coeffProject_subset (φ : L →ₗ[K] K) (P : MvPolynomial σ L) :
    (coeffProject φ P).support ⊆ P.support :=
  Finsupp.support_mapRange

theorem weight_coeffProject_le (φ : L →ₗ[K] K) (P : MvPolynomial σ L) :
    weight (coeffProject φ P) ≤ weight P :=
  Finset.card_le_card (support_coeffProject_subset φ P)

/-- Projection commutes with multiplication by a polynomial over the base field. -/
theorem coeffProject_mul_map (φ : L →ₗ[K] K) (P : MvPolynomial σ K)
    (H : MvPolynomial σ L) :
    coeffProject φ (MvPolynomial.map (algebraMap K L) P * H) =
      P * coeffProject φ H := by
  classical
  ext m
  simp only [coeff_coeffProject, coeff_mul, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simpa only [Algebra.smul_def, smul_eq_mul] using
    φ.map_smul (coeff x.1 P) (coeff x.2 H)

end Projection

section Descent

variable [Field K] [Field L] [Algebra K L]

/-- A nonzero coefficient can always be detected by a base-field linear functional. -/
theorem exists_coeffProject_ne_zero (P : MvPolynomial σ L) (hP : P ≠ 0) :
    ∃ φ : L →ₗ[K] K, coeffProject φ P ≠ 0 := by
  classical
  by_contra! h
  apply hP
  ext m
  apply (Module.forall_dual_apply_eq_zero_iff K (coeff m P)).mp
  intro φ
  have hm := congrArg (coeff m) (h φ)
  simpa only [coeff_coeffProject, coeff_zero] using hm

/-- Descent of a nonzero multiple preserves containment of input and output supports. -/
theorem exists_nonzero_multiple_descent (P : MvPolynomial σ K)
    (H : MvPolynomial σ L) (hPH : MvPolynomial.map (algebraMap K L) P * H ≠ 0) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      J.support ⊆ H.support ∧
      (P * J).support ⊆ (MvPolynomial.map (algebraMap K L) P * H).support := by
  obtain ⟨φ, hφ⟩ := exists_coeffProject_ne_zero (K := K)
    (MvPolynomial.map (algebraMap K L) P * H) hPH
  have hPJ : P * coeffProject φ H ≠ 0 := by
    rwa [coeffProject_mul_map] at hφ
  refine ⟨coeffProject φ H, ?_, hPJ, support_coeffProject_subset φ H, ?_⟩
  · intro hJ
    apply hPJ
    rw [hJ, mul_zero]
  · rw [← coeffProject_mul_map]
    exact support_coeffProject_subset φ _

/-- The descended input and output have no greater weight. -/
theorem exists_nonzero_multiple_descent_weight (P : MvPolynomial σ K)
    (H : MvPolynomial σ L) (hPH : MvPolynomial.map (algebraMap K L) P * H ≠ 0) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      weight J ≤ weight H ∧
      weight (P * J) ≤ weight (MvPolynomial.map (algebraMap K L) P * H) := by
  obtain ⟨J, hJ, hPJ, hJs, hPJs⟩ := exists_nonzero_multiple_descent P H hPH
  exact ⟨J, hJ, hPJ, Finset.card_le_card hJs, Finset.card_le_card hPJs⟩

/-- A finite prescribed input and output support admits a nonzero multiple over
an extension exactly when it does over the original field. -/
theorem exists_supported_multiple_iff (P : MvPolynomial σ K) (hP : P ≠ 0)
    (A B : Finset (σ →₀ ℕ)) :
    (∃ J : MvPolynomial σ K, J ≠ 0 ∧ J.support ⊆ A ∧ (P * J).support ⊆ B) ↔
      ∃ H : MvPolynomial σ L, H ≠ 0 ∧ H.support ⊆ A ∧
        (MvPolynomial.map (algebraMap K L) P * H).support ⊆ B := by
  have hinj : Function.Injective (algebraMap K L) :=
    FaithfulSMul.algebraMap_injective K L
  have hmapinj := MvPolynomial.map_injective (σ := σ) (algebraMap K L) hinj
  constructor
  · rintro ⟨J, hJ, hA, hB⟩
    refine ⟨MvPolynomial.map (algebraMap K L) J, ?_, ?_, ?_⟩
    · intro h
      exact hJ (hmapinj (by simpa only [map_zero] using h))
    · rwa [support_map_eq _ hinj]
    · rwa [← map_mul, support_map_eq _ hinj]
  · rintro ⟨H, hH, hA, hB⟩
    have hP' : MvPolynomial.map (algebraMap K L) P ≠ 0 := by
      intro h
      exact hP (hmapinj (by simpa only [map_zero] using h))
    obtain ⟨J, hJ, _, hJs, hPJs⟩ :=
      exists_nonzero_multiple_descent P H (mul_ne_zero hP' hH)
    exact ⟨J, hJ, hJs.trans hA, hPJs.trans hB⟩

/-- Extending the coefficient field does not change the attained support minimum. -/
theorem distance_map_algebraMap (P : MvPolynomial σ K) :
    distance (MvPolynomial.map (algebraMap K L) P) = distance P := by
  have hinj : Function.Injective (algebraMap K L) :=
    FaithfulSMul.algebraMap_injective K L
  have hmapinj := MvPolynomial.map_injective (σ := σ) (algebraMap K L) hinj
  by_cases hP : P = 0
  · simp [hP]
  apply Nat.le_antisymm
  · obtain ⟨H, hH, hweight⟩ := exists_weight_eq_distance P
    have hH' : MvPolynomial.map (algebraMap K L) H ≠ 0 := by
      intro h
      exact hH (hmapinj (by simpa only [map_zero] using h))
    have hle := distance_le_weight_mul (MvPolynomial.map (algebraMap K L) P)
      (MvPolynomial.map (algebraMap K L) H) hH'
    rw [← map_mul, weight_map_eq _ hinj, hweight] at hle
    exact hle
  · obtain ⟨H, hH, hweight⟩ :=
      exists_weight_eq_distance (MvPolynomial.map (algebraMap K L) P)
    have hP' : MvPolynomial.map (algebraMap K L) P ≠ 0 := by
      intro h
      exact hP (hmapinj (by simpa only [map_zero] using h))
    obtain ⟨J, hJ, _, _, hle⟩ :=
      exists_nonzero_multiple_descent_weight P H (mul_ne_zero hP' hH)
    exact (distance_le_weight_mul P J hJ).trans (hweight ▸ hle)

end Descent

section RingHom

variable [Field K] [Field L]

/-- The descent theorem for a specified field homomorphism. This formulation also
permits a Frobenius map from a field to itself, without a perfectness hypothesis. -/
theorem exists_nonzero_multiple_descent_map (f : K →+* L)
    (P : MvPolynomial σ K) (H : MvPolynomial σ L)
    (hPH : MvPolynomial.map f P * H ≠ 0) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      J.support ⊆ H.support ∧ (P * J).support ⊆ (MvPolynomial.map f P * H).support := by
  letI : Algebra K L := f.toAlgebra
  exact exists_nonzero_multiple_descent P H hPH

/-- Distance is invariant under every field homomorphism, including Frobenius. -/
theorem distance_map (f : K →+* L) (P : MvPolynomial σ K) :
    distance (MvPolynomial.map f P) = distance P := by
  letI : Algebra K L := f.toAlgebra
  exact distance_map_algebraMap P

end RingHom

end WeightedPilz
