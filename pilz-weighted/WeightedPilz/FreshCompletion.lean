import WeightedPilz.SharpCompletion
import WeightedPilz.VariableSlices
import WeightedPilz.Fresh

/-! Sharp completion for explicitly designated fresh coordinates. -/

noncomputable section
namespace WeightedPilz
open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

theorem independent_option_form (A : MvPolynomial σ K) (p : σ)
    (hind : ∀ d ∈ A.support, d p = 0) :
    ∃ A0 : MvPolynomial {q : σ // q ≠ p} K,
      renameEquiv K (Equiv.optionSubtypeNe p).symm A = rename some A0 ∧
      renameEquiv K (Equiv.optionSubtypeNe p).symm (A + X p) = freshCompletion A0 := by
  let A0 := (coordinateEquiv p A).coeff 0
  have hdeg : A.degreeOf p = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [degreeOf_le_iff]
    exact fun d hd => (hind d hd).le
  have hconst : coordinateEquiv p A = Polynomial.C A0 := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rw [natDegree_coordinateEquiv, hdeg]
  have hrename : renameEquiv K (Equiv.optionSubtypeNe p).symm A = rename some A0 := by
    apply (optionEquivLeft K {q : σ // q ≠ p}).injective
    rw [optionEquivLeft_rename_some]
    exact hconst
  refine ⟨A0, hrename, ?_⟩
  rw [map_add, hrename]
  simp [freshCompletion]

theorem weight_add_independent_variable (A : MvPolynomial σ K) (p : σ)
    (hind : ∀ d ∈ A.support, d p = 0) :
    weight (A + X p) = weight A + 1 := by
  obtain ⟨A0, hA, hF⟩ := independent_option_form A p hind
  have hwA := weight_renameEquiv (Equiv.optionSubtypeNe p).symm A
  have hwF := weight_renameEquiv (Equiv.optionSubtypeNe p).symm (A + X p)
  rw [hA, weight_rename_some] at hwA
  rw [hF, weight_freshCompletion, hwA] at hwF
  exact hwF.symm

/-- The one-coordinate sharp bound in an arbitrary ambient variable type. -/
theorem sharp_completion_coordinate (A : MvPolynomial σ K) (p : σ) (hA : A ≠ 0)
    (hind : ∀ d ∈ A.support, d p = 0) :
    min (weight A + 1) (distance A + 2) ≤ distance (A + X p) := by
  obtain ⟨A0, hrename, hF⟩ := independent_option_form A p hind
  have hA0 : A0 ≠ 0 := by
    intro hz
    have hh : renameEquiv K (Equiv.optionSubtypeNe p).symm A = 0 := by
      rw [hrename, hz, map_zero]
    exact hA ((renameEquiv K (Equiv.optionSubtypeNe p).symm).injective (by simpa using hh))
  have hwA := weight_renameEquiv (Equiv.optionSubtypeNe p).symm A
  rw [hrename, weight_rename_some] at hwA
  have hdA := distance_renameEquiv (Equiv.optionSubtypeNe p).symm A
  rw [hrename, distance_rename_of_injective some (Option.some_injective _)] at hdA
  have hdF := distance_renameEquiv (Equiv.optionSubtypeNe p).symm (A + X p)
  rw [hF] at hdF
  have hb := sharp_completion_one A0 hA0
  rwa [hwA, hdA, hdF] at hb

theorem independent_sum_variables (C : MvPolynomial σ K) (V : Finset σ) (p : σ)
    (hC : ∀ d ∈ C.support, d p = 0) (hp : p ∉ V) :
    ∀ d ∈ (C + ∑ i ∈ V, (X i : MvPolynomial σ K)).support, d p = 0 := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hc | hs
  · exact hC d hc
  · have hmem : d ∈ V.biUnion (fun i => (X i : MvPolynomial σ K).support) :=
      MvPolynomial.support_sum hs
    obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp hmem
    rw [MvPolynomial.support_X] at hdi
    have hd : d = Finsupp.single i 1 := Finset.mem_singleton.mp hdi
    have hpi : p ≠ i := fun h => hp (h.symm ▸ hi)
    rw [hd]
    simp [hpi]

theorem weight_add_sum_variables (V : Finset σ) (C : MvPolynomial σ K)
    (hind : ∀ p ∈ V, ∀ d ∈ C.support, d p = 0) :
    weight (C + ∑ i ∈ V, (X i : MvPolynomial σ K)) = weight C + V.card := by
  induction V using Finset.induction_on with
  | empty => simp
  | @insert p V hp ih =>
    have hCV : ∀ q ∈ V, ∀ d ∈ C.support, d q = 0 :=
      fun q hq => hind q (Finset.mem_insert_of_mem hq)
    have heq : C + ∑ i ∈ insert p V, (X i : MvPolynomial σ K) =
        (C + ∑ i ∈ V, X i) + X p := by rw [Finset.sum_insert hp]; ac_rfl
    rw [heq, weight_add_independent_variable _ p
      (independent_sum_variables C V p (hind p (Finset.mem_insert_self p V)) hp),
      ih hCV, Finset.card_insert_of_notMem hp]
    omega

/-- The sharp completion bound for any finite collection of independent
variables in the original ambient polynomial ring. -/
theorem sharp_completion_finset (V : Finset σ) (C : MvPolynomial σ K) (hC : C ≠ 0)
    (hind : ∀ p ∈ V, ∀ d ∈ C.support, d p = 0) :
    min (weight C + V.card) (distance C + 2 * V.card) ≤
      distance (C + ∑ i ∈ V, (X i : MvPolynomial σ K)) := by
  induction V using Finset.induction_on with
  | empty => simp [Nat.min_le_right]
  | @insert p V hp ih =>
    have hCV : ∀ q ∈ V, ∀ d ∈ C.support, d q = 0 :=
      fun q hq => hind q (Finset.mem_insert_of_mem hq)
    have hbound := ih hCV
    let A : MvPolynomial σ K := C + ∑ i ∈ V, X i
    have hA : A ≠ 0 := by
      intro hz
      have hpos := distance_pos hC
      have hle := distance_le_weight C
      change min (weight C + V.card) (distance C + 2 * V.card) ≤ distance A at hbound
      rw [hz, distance_zero] at hbound
      omega
    have hAind : ∀ d ∈ A.support, d p = 0 :=
      independent_sum_variables C V p (hind p (Finset.mem_insert_self p V)) hp
    have hstep := sharp_completion_coordinate A p hA hAind
    have hweight : weight A = weight C + V.card := weight_add_sum_variables V C hCV
    have heq : C + ∑ i ∈ insert p V, (X i : MvPolynomial σ K) = A + X p := by
      rw [Finset.sum_insert hp]
      dsimp [A]
      ac_rfl
    rw [heq, Finset.card_insert_of_notMem hp]
    change min (weight C + V.card) (distance C + 2 * V.card) ≤ distance A at hbound
    rw [hweight] at hstep
    omega

namespace FreshData

theorem sharp_completion (S : FreshData σ K) :
    min (weight S.C + S.vars.card) (distance S.C + 2 * S.vars.card) ≤ distance S.F :=
  sharp_completion_finset S.vars S.C S.C_ne_zero S.independent

theorem distance_eq_weight_of_threshold (S : FreshData σ K)
    (h : weight S.C - distance S.C ≤ S.vars.card) :
    distance S.F = weight S.C + S.vars.card := by
  have hlo := S.sharp_completion
  have hhi := distance_le_weight S.F
  rw [S.weight_F] at hhi
  have hc := distance_le_weight S.C
  omega

end FreshData
end WeightedPilz
