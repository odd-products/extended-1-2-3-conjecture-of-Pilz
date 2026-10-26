import WeightedPilz.Endpoints
import WeightedPilz.VariableSlices

/-! Same-ambient coordinate rows and their exact support geometry. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
variable {σ K : Type*} [DecidableEq σ] [Field K]

/-- A coordinate coefficient returned to the original variable alphabet. -/
def coordinateRow (p : σ) (k : ℕ) (P : MvPolynomial σ K) : MvPolynomial σ K :=
  rename Subtype.val ((coordinateEquiv p P).coeff k)

theorem distance_coordinateRow (p : σ) (k : ℕ) (P : MvPolynomial σ K) :
    distance (coordinateRow p k P) = distance ((coordinateEquiv p P).coeff k) := by
  exact distance_rename_of_injective Subtype.val Subtype.val_injective _

private def rowEmbedding (p : σ) : {q : σ // q ≠ p} ↪ σ :=
  ⟨Subtype.val, Subtype.val_injective⟩

private def rowRest (p : σ) (d : σ →₀ ℕ) : {q : σ // q ≠ p} →₀ ℕ :=
  (d.mapDomain (Equiv.optionSubtypeNe p).symm).some

private theorem rowRest_apply (p : σ) (d : σ →₀ ℕ) (q : {q : σ // q ≠ p}) :
    rowRest p d q = d q.val := by
  change d.mapDomain (Equiv.optionSubtypeNe p).symm (some q) = d q.val
  rw [← Equiv.optionSubtypeNe_symm_of_ne q.property, Finsupp.mapDomain_apply]
  exact (Equiv.optionSubtypeNe p).symm.injective

private theorem rowEmbedding_zero (p : σ) (e : {q : σ // q ≠ p} →₀ ℕ) :
    e.embDomain (rowEmbedding p) p = 0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨q, hq⟩
  exact q.property hq

private theorem rowRest_embed_erase (p : σ) (d : σ →₀ ℕ) :
    (rowRest p d).embDomain (rowEmbedding p) = d.erase p := by
  ext q
  by_cases hq : q = p
  · subst q
    simp only [rowEmbedding_zero, Finsupp.erase_same]
  · calc
      (rowRest p d).embDomain (rowEmbedding p) q = rowRest p d ⟨q, hq⟩ :=
        Finsupp.embDomain_apply (rowEmbedding p) (rowRest p d) ⟨q, hq⟩
      _ = d q := rowRest_apply p d ⟨q, hq⟩
      _ = d.erase p q := (Finsupp.erase_ne hq).symm

private def rowLift (p : σ) (k : ℕ) (e : {q : σ // q ≠ p} →₀ ℕ) : σ →₀ ℕ :=
  e.embDomain (rowEmbedding p) + Finsupp.single p k

private theorem rowLift_self (p : σ) (k : ℕ) (e : {q : σ // q ≠ p} →₀ ℕ) :
    rowLift p k e p = k := by
  simp [rowLift, rowEmbedding_zero]

private theorem rowRest_lift (p : σ) (k : ℕ) (e : {q : σ // q ≠ p} →₀ ℕ) :
    rowRest p (rowLift p k e) = e := by
  ext q
  rw [rowRest_apply]
  simp only [rowLift, Finsupp.add_apply, Finsupp.single_apply, Ne.symm q.property, if_false,
    add_zero]
  exact Finsupp.embDomain_apply (rowEmbedding p) e q

private theorem rowLift_erase (p : σ) (k : ℕ) (e : {q : σ // q ≠ p} →₀ ℕ) :
    (rowLift p k e).erase p = e.embDomain (rowEmbedding p) := by
  rw [← rowRest_embed_erase, rowRest_lift]

/-- Extracting a row retains its terms and erases precisely the sliced coordinate. -/
theorem support_coordinateRow (p : σ) (k : ℕ) (P : MvPolynomial σ K) :
    (coordinateRow p k P).support =
      (P.support.filter (fun d => d p = k)).image (fun d => d.erase p) := by
  classical
  rw [coordinateRow, support_rename_of_injective Subtype.val_injective]
  ext d
  constructor
  · intro hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    have hcoeff := coordinate_coeff_coeff p P (rowLift p k e)
    change coeff (rowRest p (rowLift p k e))
      ((coordinateEquiv p P).coeff (rowLift p k e p)) = _ at hcoeff
    rw [rowRest_lift, rowLift_self] at hcoeff
    refine Finset.mem_image.mpr ⟨rowLift p k e,
      Finset.mem_filter.mpr ⟨?_, rowLift_self p k e⟩, ?_⟩
    · exact mem_support_iff.mpr (hcoeff ▸ mem_support_iff.mp he)
    · rw [rowLift_erase, Finsupp.embDomain_eq_mapDomain]
      rfl
  · intro hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨he, hek⟩ := Finset.mem_filter.mp he
    refine Finset.mem_image.mpr ⟨rowRest p e, ?_, ?_⟩
    · apply mem_support_iff.mpr
      have hcoeff := coordinate_coeff_coeff p P e
      change coeff (rowRest p e) ((coordinateEquiv p P).coeff (e p)) = _ at hcoeff
      rw [hek] at hcoeff
      exact hcoeff.symm ▸ mem_support_iff.mp he
    · change (rowRest p e).mapDomain (rowEmbedding p) = e.erase p
      rw [← Finsupp.embDomain_eq_mapDomain (rowEmbedding p)]
      exact rowRest_embed_erase p e

end WeightedPilz

namespace WeightedPilz.Arithmetic

def rowSupport (p k : ℕ) (S : Finset (ℕ →₀ ℕ)) : Finset (ℕ →₀ ℕ) :=
  (S.filter (fun d => d p = k)).image (fun d => d.erase p)

/-- The finite support hypotheses of the odd-coefficient third-row obstruction. -/
structure ThreeRowsSupport (S : Finset (ℕ →₀ ℕ)) (p m : ℕ) : Prop where
  degree_ge_two : 2 ≤ m
  degree_bound : ∀ d ∈ S, d p ≤ m
  bottom_nonempty : (rowSupport p 0 S).Nonempty
  lower_nonempty : (rowSupport p (m - 2) S).Nonempty
  middle_nonempty : (rowSupport p (m - 1) S).Nonempty
  top_nonempty : (rowSupport p m S).Nonempty
  odd_unique : ∃ a ∈ rowSupport p (m - 2) S, ∃ b ∈ rowSupport p m S, ∃ j : ℕ,
    (a + b) j % 2 = 1 ∧
      ∀ u ∈ rowSupport p (m - 2) S, ∀ v ∈ rowSupport p m S,
        u + v = a + b → u = a ∧ v = b

end WeightedPilz.Arithmetic
