# Pilz's Extended 1–2–3 Conjecture, over every field

Papers and complete Lean 4 proofs on Pilz's odd-product problem.

For a finite set `A` of positive integers, write `A * [n]` for the set of
integers with an odd number of ordered representations `m = a · b`, where
`a ∈ A` and `1 ≤ b ≤ n`. **Pilz's Extended 1-2-3 Conjecture** asserts that
`|A * [n]| ≥ n` for every finite nonempty `A` and every `n ≥ 1`.

## Main result

**Weighted interval theorem.** For every field `K`, every `n ≥ 1`, and every
choice of nonzero weights `c₁, …, cₙ ∈ K`, every nonzero multiple of

    P = Σ_{a=1}^{n} c_a · X(a),     X(a) = Π_p x_p^{v_p(a)},

has at least `n` nonzero terms. The bound is sharp. Pilz's conjecture is the
special case `K = 𝔽₂`, `c_a = 1`. Equivalently, convolving any nonzero
finitely supported function with a nowhere-zero weighting of `{1,…,n}`
leaves at least `n` nonzero values.

## Contents

| Folder | Result | Paper | Lean |
|---|---|---|---|
| [`pilz-weighted/`](pilz-weighted/) | **Weighted interval theorem over every field** (implies Pilz's conjecture), with module, action, rank, equality and erasure consequences | [PDF](pilz-weighted/paper/main.pdf) | `WeightedPilz.weighted_interval`, `WeightedPilz.weighted_symmetric_difference` |
| [`pilz/`](pilz/) | The earlier, independent proof of the binary case (Pilz's conjecture itself) | [PDF](pilz/paper/pilz.pdf) | `Pilz.pilz_conjecture` |
| [`pilz-density/`](pilz-density/) | The optimal 4/3 density bound, answering Remark 1.9 of Holdridge–Pach | [PDF](pilz-density/paper/main.pdf) | `PilzDensity.companion_theorem` |

The three are separate Lean projects. The weighted theorem does not use the
earlier binary theorem as an input, so Pilz's conjecture has two formal proofs
by different methods (they share their arithmetic estimates); the two state
literally the same assertion (`intervalSymmetricDifference_eq_oddProduct`).
The density result uses neither. The earlier binary formalisation is over 𝔽₂
only; its paper's general-field remarks are superseded by the weighted theorem.

## Verification

All projects use Lean 4.24.0 and the same pinned mathlib revision. They contain
no `sorry`, no added axioms and no `native_decide`; their public theorems depend
only on `propext`, `Classical.choice` and `Quot.sound`, which their check files
enforce. To verify a project, install [elan](https://github.com/leanprover/elan),
enter its folder and follow its README. In short:

```sh
lake exe cache get
lake build
lake env lean WeightedPilzFinalChecks.lean   # in pilz-weighted/ (also WeightedPilzChecks.lean)
lake env lean Checks.lean                    # in pilz/
lake env lean DensityChecks.lean             # in pilz-density/
```

The GitHub Actions workflow runs these steps for all three projects on every push.

## Credit

This work builds directly on Pilz's original question and early results, on
the work of Huang, Ke and Pilz, Pach and Szabó, Ke and Meyer, and Nagy and Pach,
and above all on the framework of Holdridge and Pach
([arXiv:2607.00934](https://arxiv.org/abs/2607.00934)). Each paper's
introduction and acknowledgements describe these debts in detail.

## How this work was produced

The mathematics, the written proofs and the Lean formalisations were developed
with substantial assistance from AI systems. The written proofs have not been
checked line by line by a human mathematician. Correctness rests on the Lean
formalisations, which use only the standard axioms and have been re-checked
by an independent kernel replay (`lean4checker`); where a paper and its formal
proof differ, the formal proof is authoritative.

Archived at [doi:10.5281/zenodo.23568997](https://doi.org/10.5281/zenodo.23568997)
(this DOI always resolves to the latest version).

Preprints, with AI-use disclosure certificates, on Diderot:
[the weighted theorem](https://projectdiderot.com/papers/7a4dbcd9-54dd-4058-9d04-a79f9d0df491)
and [the 4/3 density bound](https://projectdiderot.com/papers/8678929f-755f-48c0-9fec-ef552502cb8f).

## Licence

Lean code and tooling: [Apache-2.0](LICENSE). Papers: CC BY 4.0 (see each
`paper/LICENSE`). Dependencies retain their own licences.
