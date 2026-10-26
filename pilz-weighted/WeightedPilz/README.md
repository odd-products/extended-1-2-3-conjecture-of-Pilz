# Weighted Pilz formalisation

Lean 4 sources accompanying the weighted Pilz paper, release v1.2.0
of 23 October 2026. This release adds four consequence modules and imports
the existing `Pilz.Parity` module. The root import closure has 325 local
modules: 278 `WeightedPilz` modules, 46 `Pilz` modules, and `WeightedPilz.lean`.
The 319 library proof modules from v1.1.0 are unchanged; the root imports
and final acceptance interfaces are extended.
The public theorem interfaces are collected in
`WeightedPilzFinalChecks.lean`.
The detailed correspondence is in `WeightedPilz/PROOF_MAP.md`.

## Public results

The public entry point is `import WeightedPilz`. The final interfaces are:

- `WeightedPilz.weighted_interval`: every nonzero polynomial multiplier,
  over every field, with arbitrary nonzero weights.
- `weighted_interval_laurent`, `weighted_interval_distance`, and
  `weighted_interval_laurent_distance`: Laurent multipliers and sharpness.
- `weighted_convolution` and `weighted_symmetric_difference`: finite
  multiplicative convolution and the original statement over F₂.
- `Compression.scalar_support_compression`, `frobenius_extraction`,
  `frobenius_strict_width_extraction`, and the `FreshData` completion,
  rigidity, residue-capacity and finite-residue theorems.
- `intervalMatrix_units_erasure_inverse`, the exact scalar-module and
  commuting group/monoid criteria, `vectorInterval_rank_bound`, and the
  scalar/vector prime-index rigidity theorems.

- `binary_prime_equality_iff` and `binary_prime_equality_output`: complete
  equality classification for nonempty finite sets of positive integers at
  prime indices at least three, with the exact output set.
- `weighted_convolution_errors_erasures_unique`,
  `module_interval_errors_erasures_unique`, and
  `commuting_interval_errors_erasures_unique`: uniqueness when
  `2 * t + E.card < n`, for field weights, injective scalar actions, or
  commuting injective additive actions. These are uniqueness statements;
  they do not supply a decoding algorithm.
- `symmetric_difference_card_mod_two`,
  `symmetric_difference_odd_even_bound`, and
  `symmetric_difference_odd_even_sharpness`: the parity identity, the
  improvement to `n + 1` for odd `n` and nonempty even-cardinality input,
  and sharpness witnessed by `{1, 2}`.
- `intervalBound_iff_nonzeroWeights` and
  `noninterval_binary_counterexample`: necessity as well as sufficiency
  of nonzero interval weights, and a three-term noninterval polynomial
  with a nonzero multiplier producing only two terms.

Conditional infrastructure remains available under names such as
`*_of_field_bounds`; the final interfaces discharge those premises.
Initial intervals, all middle-range exceptions, finite arithmetic, and
unbounded analytic estimates are separate proved components. The earlier
unweighted interval theorem is not an input to the weighted field theorem.

## Reproduction

Install the toolchain specified by `lean-toolchain`, then run from the package
root:

```text
lake exe cache get
lake build WeightedPilz
lake env lean WeightedPilzFinalChecks.lean
lake env lean WeightedPilzChecks.lean
```

`lake exe cache get` downloads the pinned mathlib dependency cache; it is an
optional speed-up. The build command compiles all project sources in the root
import closure. The acceptance file checks explicit public types and audits
every declaration originating in the imported `WeightedPilz` and `Pilz`
modules, including private declarations and their transitive dependencies.
It rejects every axiom except `propext`, `Classical.choice`, and `Quot.sound`.
It includes the hypotheses about nonzero weights and multipliers, arbitrary
fields, imperfect-field extraction, and the distinction between group
injectivity and monoid reflection of zero.

On Windows, `lake.ps1` locates Lake through PATH or an installed elan toolchain.
Run `./verify-weighted.ps1` for manifest verification, the main build, and both
acceptance files. `python checks/verify_release.py` checks the complete release manifest on any platform.

The pinned versions are:

- Lean 4.24.0, compiler commit
  `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
- mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- All transitive dependency revisions are recorded in `lake-manifest.json`.

Dependency sources and caches are fetched by Lake and are not bundled.

The source package defaults to the `WeightedPilz` target. The original
workspace's `Pilz` and `Density` targets and source developments are preserved.
The package includes only the earlier `Pilz` source dependencies actually
imported by the weighted development, chiefly exact arithmetic and analytic
estimates.

## Representation

`Poly K` is `MvPolynomial ℕ K`. Positive integers are encoded by
`Nat.factorization`; arbitrary multiplier variables are permitted, including
variables that do not encode primes. `NonzeroWeights n c` says exactly that
`c a ≠ 0` for `1 ≤ a ≤ n`, and `weight` is actual support cardinality.

`LaurentPoly σ K` is the additive monoid algebra on finitely supported
integer exponent vectors. `ArithmeticFunction K` is the multiplicative monoid
algebra on positive integers. Its multiplication is finite multiplicative
convolution. The support and change-of-representation identities are proved.

`distance P` is the attained minimum over all nonzero multipliers. The
finite-residue result chooses a suitable minimum representative; it does not
assert a degree bound for every minimum. Frobenius extraction uses finite
coefficient-space arguments and does not assume that the coefficient field
is perfect.

Finite arithmetic uses natural-number counts, integer division, exact square
roots, and rational certificates. Finite evaluation is kernel checked.
Unbounded estimates use proved analytic inequalities.

## Paper version and frozen baseline

The v1.2.0 manuscript retains all 123 labels of the frozen original and
adds four mathematical labels: `rem:scope`, `rem:errors-erasures`,
`cor:binary-prime-equality`, and `cor:binary-parity`. The complete inventory
is 127 labels: 112 mathematical and 15 navigation labels. The four additions
have dedicated Lean modules and exact statement correspondences in the proof map.

The v1.1.0 review revision made the rank theorem's `n ≥ 1` hypothesis, the
recalled endpoint inequality's `e > 0` hypothesis, and the prime equality
corollary's nonzero weights explicit; these hypotheses were already present
in Lean. Its cancellation and residue-correction examples remain as
illustrations.

The project's uniform `4/3` density result was already proved in its separate
`Density` development, proving the strengthening proposed in Holdridge–Pach,
Remark 1.9; it is not a new
result of this release or part of this package's import closure. The separate
group-algebra research note is outside the weighted manuscript certificate.

The original frozen archive contains the manuscript PDF, complete 3347-line
TeX source, and README. Its unchanged SHA-256 hashes are:

- ZIP: `1ca0028bd091939fd3410c0ad78702c53763f23bc1157169de82e5f61057e30c`
- TeX: `ab2a04db12243d99f5ba3a0ee86605a2c4d839cf16fcd97f8ca868ad298db03b`
- PDF: `6dcc5811d72e498bc98ec30e5e64b8ebf889c4fff932c6a488c051cc2e832c9a`

The release's `paper/main.pdf` and `paper/main.tex` contain the revised
v1.2.0 paper. The original frozen archive and extracted manuscript are
preserved in the workspace's `deliverable/baselines/weighted-pilz-2026-10-23/`;
the hashes above identify only that original baseline. See
[`paper/README.md`](../paper/README.md) for current-paper provenance.
The proof map records alternative proved arguments for intermediate results
where the Lean proof differs from the printed proof; the correspondence is
not a line-by-line transcription. Generated caches, tool installations, logs,
and exploratory scripts are excluded from the source package.

## Acceptance record

The v1.0.0 complete root build passed (3,477 build jobs), together with all
58 original explicit public-type examples and the compact regression file.
That independent clean project-source build compiled all 320 then-local
modules from source, reusing only third-party dependency caches whose
revisions and tracked sources were verified against the pinned manifest.
No original project build outputs were available on its Lean search path.

The v1.1.0 review revision preserved those library sources and examples and
strengthened the audit to select declarations by originating module,
including private declarations and transitive dependencies. Its recorded
6,938 module-origin declarations and 1,766 private declarations are
historical v1.1.0 counts, not the totals for this release. The accepted axiom
set is `propext`, `Classical.choice`, and `Quot.sound`.

For v1.2.0, all 58 previous public-type examples are retained and 11 new
examples cover the added consequences, giving 69 explicit public-type
checks. The 325-module closure includes the four new consequence modules
and the existing `Pilz.Parity` dependency. The release's
`verification/VERIFICATION.md` and `verification/results.json` record the
v1.2.0 build, acceptance runs, and actual module-origin audit counts.

The source package contains the complete
import closure, pinned dependency manifest, acceptance files, build and verification
scripts, and the proof map. `SOURCE_MANIFEST.sha256` records every packaged
source file; the ZIP has a separate SHA-256 checksum.
