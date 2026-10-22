# The optimal 4/3 density bound

The paper is `main.pdf`; its complete editable source is `main.tex`.
It gives an elementary proof independent of the finite-interval Pilz theorem.

For every finite nonempty set A of positive integers, the actual limit
of `|A * [n]| / n` exists and is rational. It equals one exactly for
`A = {a}` and `A = {a, 2a}`. Outside these families it is at least 4/3,
and `{1, 3}` attains 4/3.

## Formal statements

The companion development is in `../Density/`, using Lean 4.24.0 and the
repository's pinned mathlib revision. `../Density.lean` is its import entry.

| Paper claim | Lean theorem |
|---|---|
| Exact counting formula | `PilzDensity.count_floor_formula` |
| Actual limit exists | `PilzDensity.hasDensity` |
| Rational formula | `PilzDensity.density_formula`, `density_rational` |
| Scale invariance | `PilzDensity.density_scale` |
| Divisibility cut | `PilzDensity.HasDensity.exact_cut` |
| Baseline density one | `PilzDensity.baseline_density` |
| Dyadic bound 3/2 | `PilzDensity.dyadic_lower_bound` |
| Universal bound 4/3 | `PilzDensity.sharp_density_bound` |
| Exact density-one exceptions | `PilzDensity.density_eq_one_iff` |
| Complete rational-limit theorem | `PilzDensity.companion_theorem` |
| Equality example as an actual limit | `PilzDensity.sharpness_limit` |
| No larger uniform constant works | `PilzDensity.four_thirds_optimal` |

`density` selects the actual limit when it exists. The unconditional
`hasDensity` theorem proves its existence for every allowed input; the
public theorem has no assumed limit or assumed counting identity.

From the project root:

```sh
lake build Density
lake env lean DensityChecks.lean
```

For a fresh installation, install elan, then run `lake exe cache get`
before the build. Keep `lake-manifest.json`
and `lean-toolchain` to reproduce the exact dependencies.

`DensityChecks.lean` exposes the actual `Pilz.oddProduct` limit and all
input quantifiers, checks that the public results are kernel-checked
theorems, and rejects every axiom outside `propext`, `Classical.choice`,
and `Quot.sound`. It also rejects a transitive dependency on the original
finite-interval Pilz theorems. The standalone source package contains only
two original modules, `Pilz/Basic.lean` and `Pilz/OddProduct.lean`, used for
the definitions and their elementary bridge.

The development uses no `sorry`, `admit`, added axioms, or `native_decide`.
Standard Lean kernel and toolchain trust remain part of formal verification.
