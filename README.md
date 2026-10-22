# Pilz's Extended 1-2-3 Conjecture

Two results on Pilz's odd-product problem, each with a paper and a
complete Lean 4 proof.

For a finite set `A` of positive integers, write `A * [n]` for the set of
integers with an odd number of ordered representations `m = a · b`, where
`a ∈ A` and `1 ≤ b ≤ n`.

| | Result | Paper | Lean theorem |
|---|---|---|---|
| [`pilz/`](pilz/) | **Pilz's Extended 1-2-3 Conjecture.** For every finite nonempty `A` and every `n ≥ 1`, `\|A * [n]\| ≥ n`. | [PDF](pilz/paper/pilz.pdf) | `Pilz.pilz_conjecture` |
| [`pilz-density/`](pilz-density/) | **The optimal 4/3 density bound.** The limit `h(A) = lim \|A * [n]\| / n` exists and is rational; `h(A) ≥ 4/3` unless `A = {a}` or `A = {a, 2a}`; `{1, 3}` attains 4/3. | [PDF](pilz-density/paper/main.pdf) | `PilzDensity.companion_theorem` |

The two developments are independent Lean projects. The density result
does not use the finite-interval theorem; its audit file checks this.

## Verification

Both projects use Lean 4.24.0 and the same pinned mathlib revision. Each
builds with no `sorry`, no added axioms and no `native_decide`. Their
public theorems depend only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`, which the check files enforce.

To verify either project, install
[elan](https://github.com/leanprover/elan), enter its directory and run:

```sh
lake exe cache get
lake build
lake env lean Checks.lean          # in pilz/
lake env lean DensityChecks.lean   # in pilz-density/
```

The GitHub Actions workflow runs these steps for both projects on every push.

## Background

The problem comes from Pilz's work on the minimal distance of polynomial
near-ring codes, and was stated as the Extended 1-2-3 Conjecture by Huang,
Ke and Pilz. Holdridge and Pach
([arXiv:2607.00934](https://arxiv.org/abs/2607.00934)) proved it for all
sufficiently large `n`, proved `h(A) ≥ 8/7` outside the two exceptional
families, and expected the constant 4/3 (their Remark 1.9). Both papers
here build on their work; see each paper's acknowledgements.

## License

The Lean code and repository tooling are licensed under
[Apache-2.0](LICENSE). The papers are licensed under CC BY 4.0
([pilz](pilz/paper/LICENSE), [pilz-density](pilz-density/paper/LICENSE)).
Dependencies retain their own licenses.
