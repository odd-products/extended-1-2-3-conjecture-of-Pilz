import Pilz.NormalForm
import Pilz.FreshDistance
import Pilz.Slices
import Pilz.SeparatedRows

/-!
# Fresh-variable elimination

The residual cost and parity-class capacity force every residual class to
vanish when the number of fresh variables is at least `sigma C`. Slicing
the remaining multiplier outside the core variables then gives a nonzero
base multiplier with no greater objective. The final theorem states the
paper's exact equality of minimum distances.
-/

noncomputable section

namespace Pilz
namespace FreshData

/-- A base multiplier gives disjoint core and fresh rows, exactly as in the
objective on the right-hand side of the elimination theorem. -/
theorem weight_F_mul_base (S : FreshData) (E : Poly) (hvars : E.vars ⊆ S.base) :
    weight (S.F * E) = weight (S.C * E) + S.vars.card * weight E := by
  have hE : ∀ z ∈ S.vars, IndependentOf E z := by
    intro z hz d hd
    apply MvPolynomial.mem_support_notMem_vars_zero hd
    intro he
    exact S.not_mem_fresh_of_mem_base (hvars he) hz
  have hevenE : S.EvenInFresh E := by
    intro z hz d hd
    rw [hE z hz d hd]
    exact ⟨0, rfl⟩
  have hevenCE : S.EvenInFresh (S.C * E) := by
    intro z hz d hd
    rw [((S.independent z hz).mul (hE z hz)) d hd]
    exact ⟨0, rfl⟩
  rw [FreshData.F, add_mul]
  exact S.weight_normalForm (S.C * E) E hevenCE hevenE

/-- All residual classes are protected by the fresh-row budget. -/
theorem normalForm_residual_zero (S : FreshData) (N : ℕ) (nf : NormalFormData S N)
    (hN : N ≤ weight S.C + S.vars.card) (hσ : sigma S.C ≤ S.vars.card) :
    nf.G₀ + S.C * nf.D = 0 := by
  apply eq_zero_of_all_classWeight_eq_zero
  intro ε
  have hcapacity : classWeight (S.C * nf.D) ε ≤ S.vars.card * weight nf.D :=
    (classWeight_mul_le_sigma S.C nf.D ε).trans
      (Nat.mul_le_mul_right (weight nf.D) hσ)
  exact protected_class nf.G₀ S.C nf.D (nf.G₀ + S.C * nf.D) ε
    N (weight nf.G) S.vars.card (weight nf.D) rfl
    nf.extremal.1.2.2 (normalForm_weight S N nf) hcapacity
    (normalForm_residual_cost S N nf hN ε)

/-- A short multiple can be replaced by one whose multiplier uses only
the core variables. This is the main content of fresh-variable elimination. -/
theorem eliminate_short (S : FreshData) (N : ℕ)
    (hN : N ≤ weight S.C + S.vars.card) (hσ : sigma S.C ≤ S.vars.card)
    (hex : ∃ G : Poly, ShortMultiple S.F N G) :
    ∃ E : Poly, E ≠ 0 ∧ E.vars ⊆ S.base ∧ weight (S.F * E) < N := by
  obtain ⟨nf⟩ := exists_normalForm S N (S.two_le_weight_C_of_short N hN hex) hex
  have hres := S.normalForm_residual_zero N nf hN hσ
  have hG₀ : nf.G₀ = S.C * nf.D :=
    (eq_neg_of_add_eq_zero_left hres).trans (CharTwo.neg_eq _)
  obtain ⟨E, hE, hvars, hweight, hproduct⟩ :=
    exists_base_multiplier_with_weight S.base S.C nf.D
      (Finset.Subset.refl _) nf.D_ne_zero
  refine ⟨E, hE, hvars, ?_⟩
  rw [S.weight_F_mul_base E hvars]
  have hbudget := normalForm_weight S N nf
  rw [hG₀] at hbudget
  have hobjective : weight (S.C * E) + S.vars.card * weight E ≤
      weight (S.C * nf.D) + S.vars.card * weight nf.D :=
    Nat.add_le_add hproduct (Nat.mul_le_mul_left S.vars.card hweight)
  rw [hbudget] at hobjective
  exact hobjective.trans_lt nf.extremal.1.2.2

private theorem weight_one_for_objective : weight (1 : Poly) = 1 := by
  change (MvPolynomial.monomial (0 : ℕ →₀ ℕ) (1 : ZMod 2)).support.card = 1
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero]
  exact Finset.card_singleton _

private theorem exists_base_objective (S : FreshData) :
    ∃ m : ℕ, ∃ E : Poly, E ≠ 0 ∧ E.vars ⊆ S.base ∧
      weight (S.C * E) + S.vars.card * weight E = m := by
  refine ⟨weight S.C + S.vars.card, 1, one_ne_zero, ?_, ?_⟩
  · simp
  · simp only [mul_one, weight_one_for_objective]

/-- The exact minimum of the paper's base-only objective. -/
def baseDistance (S : FreshData) : ℕ := by
  classical
  exact Nat.find (exists_base_objective S)

theorem exists_objective_eq_baseDistance (S : FreshData) :
    ∃ E : Poly, E ≠ 0 ∧ E.vars ⊆ S.base ∧
      weight (S.C * E) + S.vars.card * weight E = S.baseDistance := by
  classical
  exact Nat.find_spec (exists_base_objective S)

theorem baseDistance_le_objective (S : FreshData) (E : Poly) (hE : E ≠ 0)
    (hvars : E.vars ⊆ S.base) :
    S.baseDistance ≤ weight (S.C * E) + S.vars.card * weight E := by
  classical
  exact Nat.find_min' (exists_base_objective S) ⟨E, hE, hvars, rfl⟩

theorem baseDistance_le_weight_F (S : FreshData) :
    S.baseDistance ≤ weight S.C + S.vars.card := by
  have hh := S.baseDistance_le_objective 1 one_ne_zero (by simp)
  simpa only [mul_one, weight_one_for_objective] using hh

/-- Paper, fresh-variable elimination: the unrestricted minimum distance
equals the minimum of `wt(C*E) + r*wt(E)` over nonzero base multipliers. -/
theorem distance_F_eq_baseDistance (S : FreshData) (hσ : sigma S.C ≤ S.vars.card) :
    distance S.F = S.baseDistance := by
  apply le_antisymm
  · obtain ⟨E, hE, hvars, hobjective⟩ := S.exists_objective_eq_baseDistance
    have hh : distance S.F ≤ weight (S.F * E) := distance_le_weight_mul S.F E hE
    rw [S.weight_F_mul_base E hvars, hobjective] at hh
    exact hh
  · by_contra hnot
    have hlt : distance S.F < S.baseDistance := by omega
    obtain ⟨H, hH, hweight⟩ := exists_weight_eq_distance S.F
    have hshort : ShortMultiple S.F S.baseDistance (S.F * H) :=
      ⟨mul_ne_zero S.prime_F.ne_zero hH, dvd_mul_right S.F H, by
        change weight (S.F * H) = distance S.F at hweight
        omega⟩
    obtain ⟨E, hE, hvars, hsmall⟩ := S.eliminate_short S.baseDistance
      S.baseDistance_le_weight_F hσ ⟨S.F * H, hshort⟩
    have hminimum := S.baseDistance_le_objective E hE hvars
    rw [← S.weight_F_mul_base E hvars] at hminimum
    omega

/-- In particular the minimum distance has a multiplier using no fresh variable. -/
theorem distance_attained_on_base (S : FreshData) (hσ : sigma S.C ≤ S.vars.card) :
    ∃ E : Poly, E ≠ 0 ∧ E.vars ⊆ S.base ∧ weight (S.F * E) = distance S.F := by
  obtain ⟨E, hE, hvars, hobjective⟩ := S.exists_objective_eq_baseDistance
  refine ⟨E, hE, hvars, ?_⟩
  rw [S.weight_F_mul_base E hvars, hobjective, S.distance_F_eq_baseDistance hσ]

end FreshData
end Pilz
