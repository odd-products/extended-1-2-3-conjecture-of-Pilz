import WeightedPilz.BinomialZeroSlices
import WeightedPilz.Endpoints
import WeightedPilz.VariableSlices

/-! Setting one variable to zero and the resulting transverse binomial bound. -/
noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [Field K] [DecidableEq σ]

def coordinateZero (j : σ) : MvPolynomial σ K →+* MvPolynomial σ K :=
  (rename (Subtype.val : {i : σ // i ≠ j} → σ)).toRingHom.comp
    (Polynomial.constantCoeff.comp (coordinateEquiv j).toRingHom)

@[simp] theorem coordinateZero_C (j : σ) (c : K) : coordinateZero j (C c) = C c := by
  simp [coordinateZero, coordinateEquiv, renameEquiv_apply, optionEquivLeft_C]

@[simp] theorem coordinateZero_X (j i : σ) :
    coordinateZero j (X i : MvPolynomial σ K) = if i = j then 0 else X i := by
  by_cases h : i = j
  · subst i
    simp [coordinateZero, coordinateEquiv, renameEquiv_apply,
      Equiv.optionSubtypeNe_symm_self, optionEquivLeft_X_none]
  · simp [coordinateZero, coordinateEquiv, renameEquiv_apply,
      Equiv.optionSubtypeNe_symm_of_ne h, optionEquivLeft_X_some, h]

theorem weight_coordinateZero (j : σ) (P : MvPolynomial σ K) :
    weight (coordinateZero j P) = weight ((coordinateEquiv j P).coeff 0) := by
  exact weight_rename_of_injective Subtype.val Subtype.val_injective _

private theorem option_zero_slice_binomial (F : MvPolynomial (Option σ) K)
    (a b : Option σ →₀ ℕ) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0)
    (hab : a none ≠ b none) :
    2 * weight ((optionEquivLeft K σ F).coeff 0) ≤
      weight (F * (monomial a u + monomial b v)) := by
  classical
  let Q := (optionEquivLeft K σ F).coeff 0
  let T := Q.support.image (Finsupp.embDomain Function.Embedding.some)
  have hcard : T.card = weight Q :=
    Finset.card_image_of_injective _ (Finsupp.embDomain_injective _)
  have hT : T ⊆ F.support := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    have heq := optionEquivLeft_coeff_coeff K σ (s.embDomain .some) F
    have heq' : coeff s Q = coeff (s.embDomain .some) F := by
      simpa [Q] using heq
    exact mem_support_iff.mpr (heq' ▸ mem_support_iff.mp hs)
  have h := weight_mul_binomial_of_zero_slice F T hT a b u v hu hv none hab (by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    simp)
  rwa [hcard] at h

theorem weight_mul_binomial_of_coordinateZero (F : MvPolynomial σ K)
    (a b : σ →₀ ℕ) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0)
    (j : σ) (hj : a j ≠ b j) :
    2 * weight (coordinateZero j F) ≤ weight (F * (monomial a u + monomial b v)) := by
  let e := (Equiv.optionSubtypeNe j).symm
  let E := renameEquiv K e
  have ha : (a.mapDomain e) none = a j := by
    rw [show none = e j from (Equiv.optionSubtypeNe_symm_self j).symm]
    exact Finsupp.mapDomain_apply e.injective a j
  have hb : (b.mapDomain e) none = b j := by
    rw [show none = e j from (Equiv.optionSubtypeNe_symm_self j).symm]
    exact Finsupp.mapDomain_apply e.injective b j
  have h := option_zero_slice_binomial (E F) (a.mapDomain e) (b.mapDomain e) u v hu hv
    (by rwa [ha, hb])
  rw [weight_coordinateZero]
  change 2 * weight ((optionEquivLeft K {i : σ // i ≠ j} (E F)).coeff 0) ≤ _
  have heq : E (F * (monomial a u + monomial b v)) =
      E F * (monomial (a.mapDomain e) u + monomial (b.mapDomain e) v) := by
    simp [E, renameEquiv_apply, rename_monomial]
  rw [← heq, weight_renameEquiv] at h
  exact h

theorem weight_mul_binomial_of_all_coordinateZero (F : MvPolynomial σ K) (m : ℕ)
    (hzero : ∀ j, m ≤ weight (coordinateZero j F))
    (B : MvPolynomial σ K) (hB : weight B = 2) :
    2 * m ≤ weight (F * B) := by
  obtain ⟨a, b, u, v, hab, hu, hv, rfl⟩ := exists_two_monomials_of_weight_two B hB
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ b j := by
    by_contra! hn
    exact hab (Finsupp.ext hn)
  exact (Nat.mul_le_mul_left 2 (hzero j)).trans
    (weight_mul_binomial_of_coordinateZero F a b u v hu hv j hj)

end WeightedPilz

