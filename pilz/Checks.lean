import Pilz
import Lean.Util.CollectAxioms

example (n : ℕ) : Pilz.ConjectureAt n := Pilz.conjecture n

example (n : ℕ) : Pilz.distance (Pilz.interval n) = n :=
  Pilz.distance_interval n

example (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (Pilz.oddProduct A (Finset.Icc 1 n)).card :=
  Pilz.pilz_conjecture n A hA hne

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Pilz.conjecture, ``Pilz.distance_interval, ``Pilz.pilz_conjecture] do
    match env.checked.get.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected a checked theorem: {name}"
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unexpected axiom: {axiomName}"

#print axioms Pilz.conjecture
#print axioms Pilz.distance_interval
#print axioms Pilz.pilz_conjecture
