import WeightedPilz.FinalConsequences

/-! The scalar monoid criterion also covers semimodules over commutative semirings. -/

namespace WeightedPilz
universe u v
variable {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem intervalEndBound_semimodule_iff_reflectsZero (n : ℕ) (c : ℕ → R) :
    IntervalEndBound (M := M) n (fun a => scalarWeightEnd (c a)) ↔
      ∀ a, 1 ≤ a → a ≤ n → ReflectsZero (scalarWeightEnd (M := M) (c a)) :=
  intervalEndBound_commuting_monoid_iff n (fun a => scalarWeightEnd (c a))
    (fun a _ _ b _ _ => scalarWeightEnd_commute (c a) (c b))

theorem intervalEndBound_semimodule_sharp [Nontrivial M] (n : ℕ) (c : ℕ → R)
    (hc : ∀ a, 1 ≤ a → a ≤ n → ∀ x : M, c a • x = 0 → x = 0) :
    ∃ f : ℕ+ →₀ M, f ≠ 0 ∧
      (intervalEndAction n (fun a => scalarWeightEnd (c a)) f).support.card = n :=
  intervalEndAction_sharp n (fun a => scalarWeightEnd (c a)) hc

end WeightedPilz
