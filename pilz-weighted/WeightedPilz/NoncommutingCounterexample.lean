import WeightedPilz.ModuleActions
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The frozen manuscript's noncommuting invertible weights on ℚ².
In coordinates, B is diag(1,-1), C interchanges the coordinates, and the
four weights are I, B, C, (1/2)I. Every nonzero vector supplies a four-term
input whose output has precisely the three indices 1, 9 and 16. -/

namespace WeightedPilz
open scoped BigOperators

def noncommutingB : AddMonoid.End (ℚ × ℚ) where
  toFun v := (v.1, -v.2)
  map_zero' := by simp
  map_add' v w := by ext <;> simp [add_comm]

def noncommutingC : AddMonoid.End (ℚ × ℚ) where
  toFun v := (v.2, v.1)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem noncommutingB_apply (v : ℚ × ℚ) : noncommutingB v = (v.1, -v.2) := rfl
@[simp] theorem noncommutingC_apply (v : ℚ × ℚ) : noncommutingC v = (v.2, v.1) := rfl

@[simp] private theorem scalarWeightEnd_rat_apply (a : ℚ) (v : ℚ × ℚ) :
    scalarWeightEnd a v = a • v := rfl

@[simp] private theorem id_rat_apply (v : ℚ × ℚ) :
    (AddMonoidHom.id (ℚ × ℚ)) v = v := rfl

def noncommutingWeights (a : ℕ) : AddMonoid.End (ℚ × ℚ) :=
  if a = 2 then noncommutingB else if a = 3 then noncommutingC else
    if a = 4 then scalarWeightEnd (1 / 2 : ℚ) else AddMonoidHom.id _

theorem noncommutingB_involutive : Function.Involutive noncommutingB := by
  intro v
  ext <;> simp

theorem noncommutingC_involutive : Function.Involutive noncommutingC := by
  intro v
  rfl

theorem noncommutingWeights_bijective (a : ℕ) : Function.Bijective (noncommutingWeights a) := by
  unfold noncommutingWeights
  split_ifs
  · exact noncommutingB_involutive.bijective
  · exact noncommutingC_involutive.bijective
  · exact (isUnit_iff_ne_zero.mpr (by norm_num : (1 / 2 : ℚ) ≠ 0)).smul_bijective
  · exact Function.bijective_id

theorem noncommutingWeights_do_not_commute :
    ¬Function.Commute (noncommutingWeights 2) (noncommutingWeights 3) := by
  intro h
  have hh := congrArg Prod.snd (h (1, 0))
  change (-1 : ℚ) = 1 at hh
  norm_num at hh

noncomputable def noncommutingInput (v : ℚ × ℚ) : ℕ+ →₀ (ℚ × ℚ) :=
  Finsupp.single 1 v + Finsupp.single 2 (-noncommutingB v) +
    Finsupp.single 3 (-noncommutingC v) + Finsupp.single 4 ((1 / 2 : ℚ) • v)

noncomputable def noncommutingOutput (v : ℚ × ℚ) : ℕ+ →₀ (ℚ × ℚ) :=
  Finsupp.single 1 v + Finsupp.single 16 ((1 / 4 : ℚ) • v) + Finsupp.single 9 (-v)

private theorem intervalEndAction_add {M : Type*} [AddCommMonoid M]
    (n : ℕ) (φ : ℕ → AddMonoid.End M) (f g : ℕ+ →₀ M) :
    intervalEndAction n φ (f + g) = intervalEndAction n φ f + intervalEndAction n φ g := by
  classical
  simp only [intervalEndAction, Finsupp.mapRange_add (map_add _),
    Finsupp.mapDomain_add, Finset.sum_add_distrib]

set_option maxHeartbeats 1000000 in
theorem noncommuting_interval_output (v : ℚ × ℚ) :
    intervalEndAction 4 noncommutingWeights (noncommutingInput v) = noncommutingOutput v := by
  classical
  rcases v with ⟨x, y⟩
  rw [noncommutingInput, intervalEndAction_add, intervalEndAction_add, intervalEndAction_add]
  simp only [intervalEndAction_single, Finset.sum_range_succ, Finset.sum_range_zero]
  apply Finsupp.ext
  intro m
  by_cases hm : m ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16} : Finset ℕ+)
  · fin_cases hm <;>
      norm_num [intervalIndex, noncommutingWeights,
        noncommutingOutput, Finsupp.single_apply, Prod.smul_mk, smul_eq_mul,
        show (2 : ℕ+) * 2 = 4 by decide, show (3 : ℕ+) * 2 = 6 by decide,
        show (4 : ℕ+) * 2 = 8 by decide, show (2 : ℕ+) * 3 = 6 by decide,
        show (3 : ℕ+) * 3 = 9 by decide, show (4 : ℕ+) * 3 = 12 by decide,
        show (2 : ℕ+) * 4 = 8 by decide, show (3 : ℕ+) * 4 = 12 by decide,
        show (4 : ℕ+) * 4 = 16 by decide]
    · rfl
    · change (x, -y) + (-x, y) = (0, 0)
      ext <;> dsimp <;> ring
    · change (y, x) + (-y, -x) = (0, 0)
      ext <;> dsimp <;> ring
    · change ((1 / 2 : ℚ) * x + -x + 1 / 2 * x,
        (1 / 2 : ℚ) * y + -y + 1 / 2 * y) = (0, 0)
      ext <;> dsimp <;> ring
    · constructor <;> ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨h1, h2, h3, h4, h6, h8, h9, h12, h16⟩ := hm
    simp [intervalIndex, noncommutingWeights, noncommutingOutput, Finsupp.single_apply,
      show (2 : ℕ+) * 2 = 4 by decide, show (3 : ℕ+) * 2 = 6 by decide,
      show (4 : ℕ+) * 2 = 8 by decide, show (2 : ℕ+) * 3 = 6 by decide,
      show (3 : ℕ+) * 3 = 9 by decide, show (4 : ℕ+) * 3 = 12 by decide,
      show (2 : ℕ+) * 4 = 8 by decide, show (3 : ℕ+) * 4 = 12 by decide,
      show (4 : ℕ+) * 4 = 16 by decide,
      Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h6,
      Ne.symm h8, Ne.symm h9, Ne.symm h12, Ne.symm h16]

theorem noncommutingInput_ne_zero (v : ℚ × ℚ) (hv : v ≠ 0) : noncommutingInput v ≠ 0 := by
  intro h
  have hh := congrArg (fun f : ℕ+ →₀ (ℚ × ℚ) => f 1) h
  exact hv (by simpa [noncommutingInput] using hh)

theorem noncommutingOutput_support (v : ℚ × ℚ) (hv : v ≠ 0) :
    (noncommutingOutput v).support = {1, 9, 16} := by
  classical
  have hquarter : (1 / 4 : ℚ) • v ≠ 0 := smul_ne_zero (by norm_num) hv
  ext m
  by_cases h1 : m = 1
  · subst m
    simp [noncommutingOutput, hv]
  by_cases h9 : m = 9
  · subst m
    simp [noncommutingOutput, hv]
  by_cases h16 : m = 16
  · subst m
    simp [noncommutingOutput, hquarter, hv]
  · simp [noncommutingOutput, Finsupp.mem_support_iff, Finsupp.single_apply,
      h1, h9, h16, Ne.symm h1, Ne.symm h9, Ne.symm h16]

/-- Four bijective interval weights can have only three outputs when they
do not commute. This is the necessity-of-commutativity example in the paper. -/
theorem noncommuting_interval_counterexample :
    (∀ a, 1 ≤ a → a ≤ 4 → Function.Bijective (noncommutingWeights a)) ∧
    ¬Function.Commute (noncommutingWeights 2) (noncommutingWeights 3) ∧
    ∀ v : ℚ × ℚ, v ≠ 0 → noncommutingInput v ≠ 0 ∧
      (intervalEndAction 4 noncommutingWeights (noncommutingInput v)).support.card = 3 := by
  refine ⟨fun a _ _ => noncommutingWeights_bijective a, noncommutingWeights_do_not_commute, ?_⟩
  intro v hv
  refine ⟨noncommutingInput_ne_zero v hv, ?_⟩
  rw [noncommuting_interval_output, noncommutingOutput_support v hv]
  decide

theorem noncommuting_interval_bound_fails : ¬IntervalEndBound 4 noncommutingWeights := by
  intro h
  have hv : ((1, 0) : ℚ × ℚ) ≠ 0 := by norm_num
  have hsmall := (noncommuting_interval_counterexample.2.2 (1, 0) hv).2
  have hbound := h _ (noncommutingInput_ne_zero (1, 0) hv)
  omega

end WeightedPilz
