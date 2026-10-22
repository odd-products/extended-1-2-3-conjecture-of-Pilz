# The optimal 4/3 density bound

A Lean 4 proof of the optimal density bound in Pilz's problem.

**[Read the paper (PDF)](paper/main.pdf)** · [LaTeX source](paper/main.tex) ·
[proof map](paper/README.md)

For every finite nonempty set `A` of positive integers, the limit
`h(A) = lim |A * [n]| / n` exists and is rational. It equals 1 exactly for
`A = {a}` and `A = {a, 2a}`; for every other `A` it is at least 4/3, and
`{1, 3}` attains 4/3. This answers the question raised by Holdridge and
Pach in Remark 1.9 of [arXiv:2607.00934](https://arxiv.org/abs/2607.00934).

## The theorem

The complete statement is `PilzDensity.companion_theorem` in
[Density/Certificate.lean](Density/Certificate.lean):

```lean
theorem PilzDensity.companion_theorem (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    ∃ q : ℚ, HasDensity A (q : ℝ) ∧
      ((q : ℝ) = 1 ↔ Exceptional A) ∧
      (¬ Exceptional A → (4 : ℝ) / 3 ≤ (q : ℝ))
```

`HasDensity A d` says that `|Pilz.oddProduct A [1..n]| / n` tends to `d`.
`PilzDensity.four_thirds_optimal` proves that no larger uniform constant
works, and `PilzDensity.sharpness_limit` gives the limit 4/3 for `{1, 3}`.

This project does not depend on the finite-interval Pilz theorem. It
includes only the definitions `Pilz/Basic.lean` and `Pilz/OddProduct.lean`
from the main development.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run these commands
from this `pilz-density/` directory:

```sh
lake exe cache get
lake build
lake env lean DensityChecks.lean
```

Lean **4.24.0** is selected by `lean-toolchain`, and all dependency
revisions are fixed in `lake-manifest.json`.

[DensityChecks.lean](DensityChecks.lean) checks the public theorem
statements against the actual ordered representation count, fails if any
of them depends on an axiom outside `propext`, `Classical.choice` and
`Quot.sound`, and fails if any of them uses the finite-interval theorem.
The development uses no `sorry`, no added axioms and no `native_decide`.

## License

The Lean code and repository tooling are licensed under
[Apache-2.0](LICENSE). The paper is licensed under
[CC BY 4.0](paper/LICENSE). Dependencies retain their own licenses.
