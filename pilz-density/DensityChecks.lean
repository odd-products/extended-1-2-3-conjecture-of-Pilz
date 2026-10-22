import Density
import Lean.Util.CollectAxioms

open Filter
open scoped Topology

-- These examples expose the actual count and the complete public quantifiers.
example (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty)
    (hnot : ¬ ∃ a : ℕ, 0 < a ∧ (A = {a} ∨ A = {a, 2 * a})) :
    ∃ d : ℝ,
      Tendsto (fun n : ℕ =>
        ((Pilz.oddProduct A (Finset.Icc 1 n)).card : ℝ) / (n : ℝ))
        atTop (𝓝 d) ∧ (4 : ℝ) / 3 ≤ d :=
  PilzDensity.sharp_density_limit A hA hne hnot

example : Tendsto (fun n : ℕ =>
    ((Pilz.oddProduct {1, 3} (Finset.Icc 1 n)).card : ℝ) / (n : ℝ))
    atTop (𝓝 ((4 : ℝ) / 3)) := PilzDensity.sharpness_limit

example (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    ∃ q : ℚ, PilzDensity.HasDensity A (q : ℝ) ∧
      ((q : ℝ) = 1 ↔ ∃ a : ℕ, 0 < a ∧ (A = {a} ∨ A = {a, 2 * a})) ∧
      (¬ (∃ a : ℕ, 0 < a ∧ (A = {a} ∨ A = {a, 2 * a})) →
        (4 : ℝ) / 3 ≤ (q : ℝ)) := PilzDensity.companion_theorem A hA hne

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``PilzDensity.count_floor_formula, ``PilzDensity.hasDensity,
      ``PilzDensity.density_scale, ``PilzDensity.baseline_density,
      ``PilzDensity.dyadic_lower_bound, ``PilzDensity.sharp_density_bound,
      ``PilzDensity.density_eq_one_iff, ``PilzDensity.companion_theorem,
      ``PilzDensity.four_thirds_optimal, ``PilzDensity.sharpness_limit] do
    match env.checked.get.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected a checked theorem: {name}"
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unexpected axiom: {axiomName}"
    let (_, dependencies) := ((Lean.CollectAxioms.collect name).run env).run {}
    for forbidden in ["Pilz.pilz_conjecture", "Pilz.conjecture", "Pilz.distance_interval"] do
      if dependencies.visited.contains forbidden.toName then
        throwError "{name} unexpectedly uses the finite-interval theorem: {forbidden}"

#print axioms PilzDensity.companion_theorem
#print axioms PilzDensity.four_thirds_optimal
#print axioms PilzDensity.sharpness_limit
