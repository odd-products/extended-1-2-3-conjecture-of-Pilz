# Pilz

A Lean 4 proof of Pilz's Extended 1–2–3 Conjecture.

**[Read the paper (PDF)](paper/pilz.pdf)** · [LaTeX source](paper/main.tex)

For every finite nonempty set `A` of positive integers and every `n ≥ 1`,
at least `n` integers have an odd number of **ordered** representations
`m = a · b`, where `a ∈ A` and `1 ≤ b ≤ n`.

## The theorem

The finite-set statement is [Pilz.pilz_conjecture](Pilz/Assembly.lean):

```lean
theorem Pilz.pilz_conjecture (n : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    n ≤ (Pilz.oddProduct A (Finset.Icc 1 n)).card
```

[oddProduct](Pilz/OddProduct.lean) counts pairs in the Cartesian product
and retains exactly the products with odd representation counts. The statement
also includes the trivial case `n = 0`.

The polynomial formulation and the exact minimum distance are
`Pilz.conjecture` and `Pilz.distance_interval`.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run these commands
from this `pilz/` directory:

```sh
lake exe cache get
lake build
lake env lean Checks.lean
```

The same commands work on Linux, macOS, and Windows. The first command fetches
the pinned mathlib dependencies and their compiled cache. Lean **4.24.0** is
selected by `lean-toolchain`; all dependency revisions are fixed in
`lake-manifest.json`. Keep that manifest when reproducing the build.

[Checks.lean](Checks.lean) checks the three public theorem types, prints their
transitive axiom dependencies, and fails if a dependency is outside
`propext`, `Classical.choice`, and `Quot.sound`. The GitHub Actions workflow
runs the build and this check.

To use the result in Lean:

```lean
import Pilz

#check Pilz.pilz_conjecture
```

## Source map

| Entry point | Content |
|---|---|
| [Pilz/OddProduct.lean](Pilz/OddProduct.lean) | Ordered counts and the polynomial encoding |
| [Pilz/Elimination.lean](Pilz/Elimination.lean) | Fresh-variable elimination |
| [Pilz/LargeConclusion.lean](Pilz/LargeConclusion.lean) | All interval lengths at least 67 |
| [Pilz/SmallConclusion.lean](Pilz/SmallConclusion.lean) | All interval lengths at most 66 |
| [Pilz/Assembly.lean](Pilz/Assembly.lean) | The unconditional theorems |
| [paper/main.tex](paper/main.tex) | The mathematical paper |

The development proves the paper's main finite-set theorem. Intermediate
results are specialized to the hypotheses needed for that theorem; broader
field and vector-coefficient generalizations in the paper are not separate
claims of this Lean library.

## Paper

The [compiled paper](paper/pilz.pdf) and its LaTeX source are in `paper/`.
To rebuild the PDF with a standard TeX Live or MiKTeX installation:

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

This produces `paper/main.pdf`.

## License

The Lean code and repository tooling are licensed under
[Apache-2.0](LICENSE). The paper is licensed under
[CC BY 4.0](paper/LICENSE). Dependencies retain their own licenses.
