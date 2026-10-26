import WeightedPilz.Dilation
import WeightedPilz.CoefficientExtension
import WeightedPilz.Width
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Frobenius extraction over arbitrary fields

The extraction is coefficient-space descent through the Frobenius field
embedding. It applies unchanged to imperfect fields. No coefficient root in
the original field is assumed or chosen.
-/

noncomputable section

namespace WeightedPilz

open MvPolynomial

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {σ K : Type*} [Field K]

/-- Frobenius powers act by coefficient Frobenius and exponent dilation. -/
theorem pow_expChar_eq_dilate_map (p e : ℕ) [ExpChar K p]
    (P : MvPolynomial σ K) :
    P ^ p ^ e = dilate (p ^ e) (MvPolynomial.map (iterateFrobenius K p e) P) := by
  letI : ExpChar (MvPolynomial σ K) p :=
    expChar_of_injective_ringHom (MvPolynomial.C_injective (σ := σ) (R := K)) p
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [monomial_pow, map_monomial, dilate_monomial]
      rfl
  | add P Q hP hQ =>
      rw [add_pow_expChar_pow, map_add, dilate_add, hP, hQ]

theorem support_pow_expChar (p e : ℕ) [ExpChar K p] (P : MvPolynomial σ K) :
    (P ^ p ^ e).support = P.support.image (scaleExponent (p ^ e)) := by
  classical
  rw [pow_expChar_eq_dilate_map, support_dilate (pow_pos (expChar_pos K p) e),
    support_map_eq _ (iterateFrobenius K p e).injective]

theorem weight_pow_expChar (p e : ℕ) [ExpChar K p] (P : MvPolynomial σ K) :
    weight (P ^ p ^ e) = weight P := by
  rw [pow_expChar_eq_dilate_map, weight_dilate (pow_pos (expChar_pos K p) e),
    weight_map_eq _ (iterateFrobenius K p e).injective]

/-- Frobenius preserves minimum support, even when the field is imperfect. -/
theorem distance_pow_expChar (p e : ℕ) [ExpChar K p] (P : MvPolynomial σ K) :
    distance (P ^ p ^ e) = distance P := by
  rw [pow_expChar_eq_dilate_map, distance_dilate (pow_pos (expChar_pos K p) e)]
  letI : Algebra K K := (iterateFrobenius K p e).toAlgebra
  exact distance_map_algebraMap (K := K) (L := K) P

/-- Simultaneous support descent after exponent dilation and an arbitrary
field embedding. This separates the two operations needed for Frobenius. -/
theorem exists_dilate_map_extraction (f : K →+* K) {q : ℕ} (hq : 0 < q)
    (P E : MvPolynomial σ K) (α : σ →₀ ℕ)
    (hU : residuePart q (dilate q (MvPolynomial.map f P) * E) α ≠ 0) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      (∀ d ∈ J.support, α + scaleExponent q d ∈ E.support) ∧
      (∀ d ∈ (P * J).support, α + scaleExponent q d ∈
        (residuePart q (dilate q (MvPolynomial.map f P) * E) α).support) := by
  classical
  have hW : MvPolynomial.map f P * residueRoot q E α ≠ 0 := by
    intro hz
    apply hU
    rw [residuePart_dilate_mul_eq, hz, dilate_zero, mul_zero]
  letI : Algebra K K := f.toAlgebra
  obtain ⟨J, hJ, hPJ, hJs, hPJs⟩ :=
    exists_nonzero_multiple_descent (K := K) (L := K) P (residueRoot q E α) hW
  refine ⟨J, hJ, hPJ, ?_, ?_⟩
  · intro d hd
    exact residueRoot_support_lift hq E α d (hJs hd)
  · intro d hd
    rw [residuePart_dilate_mul_eq, support_monomial_dilate hq]
    exact Finset.mem_image.mpr ⟨d, hPJs hd, rfl⟩

/-- `lem:frobenius-extraction`, in the stronger form extracting from any
nonzero full exponent residue class of the given multiple. -/
theorem frobenius_extraction_residue (p e : ℕ) [ExpChar K p]
    (P E : MvPolynomial σ K) (α : σ →₀ ℕ)
    (hU : residuePart (p ^ e) (P ^ p ^ e * E) α ≠ 0) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      (∀ d ∈ J.support, α + scaleExponent (p ^ e) d ∈ E.support) ∧
      (∀ d ∈ (P * J).support, α + scaleExponent (p ^ e) d ∈
        (residuePart (p ^ e) (P ^ p ^ e * E) α).support) := by
  rw [pow_expChar_eq_dilate_map] at hU ⊢
  exact exists_dilate_map_extraction (iterateFrobenius K p e)
    (pow_pos (expChar_pos K p) e) P E α hU

theorem residuePart_eq_self_of_support (q : ℕ) (P : MvPolynomial σ K)
    (α : σ →₀ ℕ) (h : ∀ d ∈ P.support, residueExponent q d = α) :
    residuePart q P α = P := by
  classical
  ext d
  rw [coeff_residuePart]
  by_cases hd : d ∈ P.support
  · rw [if_pos (h d hd)]
  · simp [MvPolynomial.notMem_support_iff.mp hd]

/-- The manuscript's extraction statement, with both support containments. -/
theorem frobenius_extraction (p e : ℕ) [ExpChar K p]
    (P E : MvPolynomial σ K) (α : σ →₀ ℕ)
    (hU : P ^ p ^ e * E ≠ 0)
    (hres : ∀ d ∈ (P ^ p ^ e * E).support, residueExponent (p ^ e) d = α) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      (∀ d ∈ J.support, α + scaleExponent (p ^ e) d ∈ E.support) ∧
      (∀ d ∈ (P * J).support, α + scaleExponent (p ^ e) d ∈
        (P ^ p ^ e * E).support) := by
  have heq := residuePart_eq_self_of_support (p ^ e) (P ^ p ^ e * E) α hres
  have hn : residuePart (p ^ e) (P ^ p ^ e * E) α ≠ 0 := by rwa [heq]
  obtain ⟨J, hJ, hPJ, hJs, hPJs⟩ := frobenius_extraction_residue p e P E α hn
  exact ⟨J, hJ, hPJ, hJs, heq ▸ hPJs⟩

/-- The extracted ordinary multiple has no more terms than the original. -/
theorem frobenius_extraction_weight (p e : ℕ) [ExpChar K p]
    (P E : MvPolynomial σ K) (hU : P ^ p ^ e * E ≠ 0) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      weight (P * J) ≤ weight (P ^ p ^ e * E) := by
  classical
  obtain ⟨α, hα⟩ := exists_nonzero_residuePart (p ^ e) (P ^ p ^ e * E) hU
  obtain ⟨J, hJ, hPJ, _, hPJs⟩ := frobenius_extraction_residue p e P E α hα
  refine ⟨J, hJ, hPJ, ?_⟩
  have hinj : Function.Injective (fun d : σ →₀ ℕ => α + scaleExponent (p ^ e) d) :=
    (add_right_injective α).comp (scaleExponent_injective (pow_pos (expChar_pos K p) e))
  have hs : (P * J).support.image (fun d => α + scaleExponent (p ^ e) d) ⊆
      (residuePart (p ^ e) (P ^ p ^ e * E) α).support := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact hPJs a ha
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hinj] at hc
  exact hc.trans (weight_residuePart_le _ _ _)

/-- Support containment after affine exponent dilation bounds each coordinate
width, with the denominator cleared in natural-number arithmetic. -/
theorem scaled_width_le_of_support_image [DecidableEq σ] (q : ℕ) (i : σ)
    (P Q : MvPolynomial σ K) (α : σ →₀ ℕ) (hP : P ≠ 0)
    (hPQ : ∀ d ∈ P.support, α + scaleExponent q d ∈ Q.support) :
    q * widthOf i P ≤ widthOf i Q := by
  classical
  obtain ⟨dlo, hlo, heqlo⟩ := exists_support_orderOf i hP
  have hhi : (coordinateEquiv i P).natDegree ∈ (coordinateEquiv i P).support :=
    Polynomial.natDegree_mem_support_of_nonzero (coordinateEquiv_ne_zero i hP)
  rw [natDegree_coordinateEquiv, support_coordinateEquiv] at hhi
  obtain ⟨dhi, hhi, heqhi⟩ := Finset.mem_image.mp hhi
  have hlow := orderOf_le_support i (hPQ dlo hlo)
  have hhigh := monomial_le_degreeOf i (hPQ dhi hhi)
  simp only [Finsupp.add_apply, scaleExponent_apply, heqlo, heqhi] at hlow hhigh
  have hmul := Nat.mul_le_mul_left q (orderOf_le_degreeOf i P)
  simp only [widthOf, Nat.mul_sub_left_distrib]
  omega

/-- The width conclusion of `lem:frobenius-extraction`, simultaneously for
the extracted input and output. No division or rounding is hidden. -/
theorem frobenius_extraction_width [DecidableEq σ] (p e : ℕ) [ExpChar K p]
    (P E : MvPolynomial σ K) (α : σ →₀ ℕ)
    (hU : P ^ p ^ e * E ≠ 0)
    (hres : ∀ d ∈ (P ^ p ^ e * E).support, residueExponent (p ^ e) d = α) :
    ∃ J : MvPolynomial σ K, J ≠ 0 ∧ P * J ≠ 0 ∧
      (∀ i, p ^ e * widthOf i J ≤ widthOf i E) ∧
      (∀ i, p ^ e * widthOf i (P * J) ≤ widthOf i (P ^ p ^ e * E)) := by
  obtain ⟨J, hJ, hPJ, hJs, hPJs⟩ := frobenius_extraction p e P E α hU hres
  exact ⟨J, hJ, hPJ,
    fun i => scaled_width_le_of_support_image (p ^ e) i J E α hJ hJs,
    fun i => scaled_width_le_of_support_image (p ^ e) i (P * J) _ α hPJ hPJs⟩

end WeightedPilz
