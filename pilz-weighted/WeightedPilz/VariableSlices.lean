import Mathlib.Algebra.MvPolynomial.Division
import WeightedPilz.Support
import WeightedPilz.Distance
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Slicing in variables outside a prescribed set

The projection records the entire exponent vector outside the base set,
not just its total degree. A polynomial supported in the base set preserves
each such fiber under multiplication.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace WeightedPilz

variable {σ K : Type*} [DecidableEq σ] [CommSemiring K]

open MvPolynomial
open scoped BigOperators

/-- The exponent vector in variables outside `S`. -/
def outsideExponent (S : Set σ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.filter (fun p => p ∉ S)

@[simp] theorem outsideExponent_apply (S : Set σ) (d : σ →₀ ℕ) (p : σ) :
    outsideExponent S d p = if p ∉ S then d p else 0 := rfl

@[simp] theorem outsideExponent_zero (S : Set σ) : outsideExponent S 0 = 0 := by
  ext p
  simp only [outsideExponent_apply, Finsupp.zero_apply, ite_self]

theorem outsideExponent_add (S : Set σ) (d e : σ →₀ ℕ) :
    outsideExponent S (d + e) = outsideExponent S d + outsideExponent S e := by
  ext p
  by_cases hp : p ∉ S <;> simp [outsideExponent_apply, Finsupp.add_apply, hp]

@[simp] theorem outsideExponent_idempotent (S : Set σ) (d : σ →₀ ℕ) :
    outsideExponent S (outsideExponent S d) = outsideExponent S d := by
  ext p
  by_cases hp : p ∉ S <;> simp [outsideExponent_apply, hp]

theorem outsideExponent_le (S : Set σ) (d : σ →₀ ℕ) :
    outsideExponent S d ≤ d := by
  rw [Finsupp.le_def]
  intro p
  by_cases hp : p ∉ S <;> simp [outsideExponent_apply, hp]

theorem outsideExponent_sub_of_zero (S : Set σ) (d e : σ →₀ ℕ)
    (he : outsideExponent S e = 0) :
    outsideExponent S (d - e) = outsideExponent S d := by
  have hsub : outsideExponent S (d - e) = outsideExponent S d - outsideExponent S e := by
    ext p
    by_cases hp : p ∉ S <;> simp [outsideExponent_apply, Finsupp.tsub_apply, hp]
  rw [hsub, he, tsub_zero]

theorem outsideExponent_eq_zero_of_support_subset (S : Set σ) (d : σ →₀ ℕ)
    (hd : (d.support : Set σ) ⊆ S) : outsideExponent S d = 0 := by
  ext p
  by_cases hp : p ∈ S
  · simp [outsideExponent_apply, hp]
  · have hd0 : d p = 0 := Finsupp.notMem_support_iff.mp (fun hm => hp (hd hm))
    simp [outsideExponent_apply, hp, hd0]

theorem vars_subset_iff_outsideExponent_zero (S : Set σ) (P : MvPolynomial σ K) :
    (P.vars : Set σ) ⊆ S ↔ ∀ d ∈ P.support, outsideExponent S d = 0 := by
  constructor
  · intro hP d hd
    apply outsideExponent_eq_zero_of_support_subset
    intro p hp
    exact hP ((MvPolynomial.mem_vars p).mpr ⟨d, hd, hp⟩)
  · intro hP p hp
    obtain ⟨d, hd, hdp⟩ := (MvPolynomial.mem_vars p).mp hp
    by_contra hps
    have hz := congrArg (fun e => e p) (hP d hd)
    have hd0 : d p = 0 := by simpa [outsideExponent_apply, hps] using hz
    exact (Finsupp.mem_support_iff.mp hdp) hd0

/-- The terms in one fixed outside-variable exponent fiber. -/
def outsideSlice (S : Set σ) (β : σ →₀ ℕ) (P : MvPolynomial σ K) : MvPolynomial σ K := by
  classical
  exact Finsupp.filter (fun d => outsideExponent S d = β) P

theorem coeff_outsideSlice (S : Set σ) (β d : σ →₀ ℕ) (P : MvPolynomial σ K) :
    MvPolynomial.coeff d (outsideSlice S β P) =
      if outsideExponent S d = β then MvPolynomial.coeff d P else 0 := by
  classical
  rfl

theorem support_outsideSlice (S : Set σ) (β : σ →₀ ℕ) (P : MvPolynomial σ K) :
    (outsideSlice S β P).support = P.support.filter (fun d => outsideExponent S d = β) := by
  classical
  rfl

theorem weight_outsideSlice_le (S : Set σ) (β : σ →₀ ℕ) (P : MvPolynomial σ K) :
    weight (outsideSlice S β P) ≤ weight P := by
  classical
  unfold weight
  rw [support_outsideSlice]
  exact Finset.card_filter_le _ _

theorem outsideSlice_sum {ι : Type*} (S : Set σ) (β : σ →₀ ℕ)
    (A : Finset ι) (f : ι → MvPolynomial σ K) :
    outsideSlice S β (∑ a ∈ A, f a) = ∑ a ∈ A, outsideSlice S β (f a) := by
  classical
  ext d
  simp only [coeff_outsideSlice, MvPolynomial.coeff_sum]
  by_cases h : outsideExponent S d = β <;> simp [h]

theorem outsideSlice_monomial_mul (S : Set σ) (β d : σ →₀ ℕ)
    (c : K) (H : MvPolynomial σ K) (hd : outsideExponent S d = 0) :
    outsideSlice S β (MvPolynomial.monomial d c * H) =
      MvPolynomial.monomial d c * outsideSlice S β H := by
  classical
  ext e
  by_cases hde : d ≤ e <;> by_cases hβ : outsideExponent S e = β <;>
    simp [coeff_outsideSlice, MvPolynomial.coeff_monomial_mul',
      outsideExponent_sub_of_zero S e d hd, hde, hβ]

/-- Multiplication by a base polynomial commutes with outside-variable slicing. -/
theorem outsideSlice_mul (S : Set σ) (β : σ →₀ ℕ) (P H : MvPolynomial σ K)
    (hP : (P.vars : Set σ) ⊆ S) :
    outsideSlice S β (P * H) = P * outsideSlice S β H := by
  classical
  have hPs := (vars_subset_iff_outsideExponent_zero S P).mp hP
  calc
    outsideSlice S β (P * H) =
        outsideSlice S β ((∑ d ∈ P.support, MvPolynomial.monomial d (MvPolynomial.coeff d P)) * H) :=
      congrArg (outsideSlice S β) (congrArg (fun Q : MvPolynomial σ K => Q * H) (MvPolynomial.as_sum P))
    _ = ∑ d ∈ P.support, outsideSlice S β (MvPolynomial.monomial d (MvPolynomial.coeff d P) * H) := by
      rw [Finset.sum_mul, outsideSlice_sum]
    _ = ∑ d ∈ P.support, MvPolynomial.monomial d (MvPolynomial.coeff d P) * outsideSlice S β H := by
      apply Finset.sum_congr rfl
      intro d hd
      exact outsideSlice_monomial_mul S β d (MvPolynomial.coeff d P) H (hPs d hd)
    _ = P * outsideSlice S β H := by
      rw [← Finset.sum_mul, ← MvPolynomial.as_sum P]

/-- The finite outside fibers reassemble the polynomial exactly. -/
theorem sum_outsideSlice (S : Set σ) (P : MvPolynomial σ K) :
    (∑ β ∈ P.support.image (outsideExponent S), outsideSlice S β P) = P := by
  classical
  ext d
  by_cases hd : d ∈ P.support
  · have him : outsideExponent S d ∈ P.support.image (outsideExponent S) :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    simp [MvPolynomial.coeff_sum, coeff_outsideSlice, him]
  · have hz := MvPolynomial.notMem_support_iff.mp hd
    simp [MvPolynomial.coeff_sum, coeff_outsideSlice, hz]

/-- Fibers with different outside exponents have disjoint supports. -/
theorem disjoint_support_outsideSlice (S : Set σ) (β γ : σ →₀ ℕ)
    (P Q : MvPolynomial σ K) (hβγ : β ≠ γ) :
    Disjoint (outsideSlice S β P).support (outsideSlice S γ Q).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdβ hdγ
  rw [support_outsideSlice] at hdβ hdγ
  exact hβγ ((Finset.mem_filter.mp hdβ).2.symm.trans (Finset.mem_filter.mp hdγ).2)

/-- The weight is exactly the sum of the weights of all outside fibers. -/
theorem weight_eq_sum_outsideSlice (S : Set σ) (P : MvPolynomial σ K) :
    weight P = ∑ β ∈ P.support.image (outsideExponent S), weight (outsideSlice S β P) := by
  classical
  simpa only [weight, support_outsideSlice] using
    Finset.card_eq_sum_card_image (outsideExponent S) P.support

private theorem monomial_mul_divMonomial_eq_slice (H : MvPolynomial σ K) (e : σ →₀ ℕ)
    (he : ∀ d ∈ H.support, e ≤ d) :
    monomial e 1 * divMonomial H e = H := by
  have hrem : modMonomial H e = 0 := by
    ext d
    by_cases hd : d ∈ H.support
    · exact coeff_modMonomial_of_le H (he d hd)
    · by_cases hed : e ≤ d
      · exact coeff_modMonomial_of_le H hed
      · rw [coeff_modMonomial_of_not_le H hed]
        exact notMem_support_iff.mp hd
  simpa [hrem] using divMonomial_add_modMonomial H e
/-- Dividing a fiber by its fixed outside monomial leaves a polynomial
in the base variables. -/
theorem outsideSlice_division (S : Set σ) (β : σ →₀ ℕ)
    (hβ : outsideExponent S β = β) (H : MvPolynomial σ K) :
    ∃ D : MvPolynomial σ K, outsideSlice S β H = MvPolynomial.monomial β 1 * D ∧ (D.vars : Set σ) ⊆ S := by
  classical
  let E := outsideSlice S β H
  let D := MvPolynomial.divMonomial E β
  have hcommon : ∀ d ∈ E.support, β ≤ d := by
    intro d hd
    have heq : outsideExponent S d = β := (Finset.mem_filter.mp hd).2
    rw [← heq]
    exact outsideExponent_le S d
  have hfactor : E = MvPolynomial.monomial β 1 * D :=
    (monomial_mul_divMonomial_eq_slice E β hcommon).symm
  refine ⟨D, hfactor, ?_⟩
  apply (vars_subset_iff_outsideExponent_zero S D).mpr
  intro d hd
  have hc : MvPolynomial.coeff (β + d) E ≠ 0 := by
    simpa only [D, MvPolynomial.coeff_divMonomial] using MvPolynomial.mem_support_iff.mp hd
  have hmem : β + d ∈ E.support := MvPolynomial.mem_support_iff.mpr hc
  have hout : outsideExponent S (β + d) = β := (Finset.mem_filter.mp hmem).2
  rw [outsideExponent_add, hβ] at hout
  exact add_left_cancel (show β + outsideExponent S d = β + 0 by simpa only [add_zero] using hout)

/-- Paper, elementary reductions (b): variables absent from the base
polynomial can be removed from a multiplier without increasing its product
weight. The selected multiplier is nonzero and uses only the chosen base set. -/
theorem exists_base_multiplier_with_weight (S : Set σ) (P H : MvPolynomial σ K)
    (hP : (P.vars : Set σ) ⊆ S) (hH : H ≠ 0) :
    ∃ D : MvPolynomial σ K, D ≠ 0 ∧ (D.vars : Set σ) ⊆ S ∧ weight D ≤ weight H ∧
      weight (P * D) ≤ weight (P * H) := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
  let β := outsideExponent S d
  let E := outsideSlice S β H
  have hE : E ≠ 0 := by
    apply MvPolynomial.support_nonempty.mp
    refine ⟨d, ?_⟩
    rw [support_outsideSlice]
    exact Finset.mem_filter.mpr ⟨hd, rfl⟩
  have hβ : outsideExponent S β = β := outsideExponent_idempotent S d
  obtain ⟨D, hfactor, hDvars⟩ := outsideSlice_division S β hβ H
  have hfactorE : E = MvPolynomial.monomial β 1 * D := hfactor
  have hD : D ≠ 0 := by
    intro hz
    apply hE
    rw [hfactorE, hz, mul_zero]
  have hDEweight : weight D = weight E := by
    rw [hfactorE, weight_monomial_mul]
  have hDweight : weight D ≤ weight H :=
    hDEweight.trans_le (weight_outsideSlice_le S β H)
  refine ⟨D, hD, hDvars, hDweight, ?_⟩
  have hbound := weight_outsideSlice_le S β (P * H)
  rw [outsideSlice_mul S β P H hP] at hbound
  have hweight : weight (P * D) = weight (P * E) := by
    rw [hfactorE]
    calc
      weight (P * D) = weight (MvPolynomial.monomial β 1 * (P * D)) :=
        (weight_monomial_mul β (P * D)).symm
      _ = weight (P * (MvPolynomial.monomial β 1 * D)) := by rw [mul_left_comm]
  exact hweight.trans_le hbound

theorem exists_base_multiplier (S : Set σ) (P H : MvPolynomial σ K)
    (hP : (P.vars : Set σ) ⊆ S) (hH : H ≠ 0) :
    ∃ D : MvPolynomial σ K, D ≠ 0 ∧ (D.vars : Set σ) ⊆ S ∧ weight (P * D) ≤ weight (P * H) := by
  obtain ⟨D, hD, hDvars, _, hprod⟩ := exists_base_multiplier_with_weight S P H hP hH
  exact ⟨D, hD, hDvars, hprod⟩

/-- Injectively renaming variables preserves the exact number of monomials. -/
theorem weight_rename_of_injective {τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ K) :
    weight (rename f P) = weight P := by
  classical
  rw [weight, support_rename_of_injective hf]
  exact Finset.card_image_of_injective _ (Finsupp.mapDomain_injective hf)

/-- A multiple in a larger variable set supplies a nonzero cofactor in the
original variables without increasing its output support. -/
theorem exists_multiplier_of_rename {τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ K) (H : MvPolynomial τ K)
    (hH : H ≠ 0) :
    ∃ D : MvPolynomial σ K, D ≠ 0 ∧
      weight (P * D) ≤ weight (rename f P * H) := by
  classical
  have hvars : ((rename f P).vars : Set τ) ⊆ Set.range f := by
    intro i hi
    obtain ⟨j, _, hji⟩ := mem_vars_rename f P hi
    exact ⟨j, hji⟩
  obtain ⟨D, hD, hDvars, hweight⟩ := exists_base_multiplier (Set.range f)
    (rename f P) H hvars hH
  obtain ⟨E, hE⟩ := exists_rename_eq_of_vars_subset_range D f hf hDvars
  refine ⟨E, ?_, ?_⟩
  · intro hz
    apply hD
    rw [← hE, hz, map_zero]
  · rw [← hE, ← map_mul, weight_rename_of_injective f hf] at hweight
    exact hweight

end WeightedPilz

namespace WeightedPilz

variable {σ τ K : Type*} [Field K]

/-- Adjoining any collection of extra variables does not change distance. -/
theorem distance_rename_of_injective (f : σ → τ) (hf : Function.Injective f)
    (P : MvPolynomial σ K) : distance (MvPolynomial.rename f P) = distance P := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨H, hH, hmin⟩ := exists_weight_eq_distance P
    have hn : MvPolynomial.rename f H ≠ 0 := by
      intro hz
      apply hH
      exact MvPolynomial.rename_injective f hf (by simpa using hz)
    have h := distance_le_weight_mul (MvPolynomial.rename f P) (MvPolynomial.rename f H) hn
    rw [← map_mul, weight_rename_of_injective f hf, hmin] at h
    exact h
  · apply (le_distance_iff _ _).mpr
    intro H hH
    obtain ⟨D, hD, hweight⟩ := exists_multiplier_of_rename f hf P H hH
    exact (distance_le_weight_mul P D hD).trans hweight

end WeightedPilz

