# Weighted Pilz

**Pilz's Extended 1–2–3 Conjecture over every field**  
Sparse multiples of weighted integer intervals  
Paper and complete Lean 4 formalisation · release v1.2.1

**[Read the paper](paper/main.pdf)** · [LaTeX source](paper/main.tex) ·
[Proof map](WeightedPilz/PROOF_MAP.md) · [Verification](verification/VERIFICATION.md) ·
[Release notes](RELEASE_NOTES.md) · [Citation](CITATION.md)

For every field, every interval length `n ≥ 1`, and every choice of nonzero
weights, every nonzero polynomial or Laurent-polynomial multiple of the
weighted interval polynomial has at least `n` nonzero terms. The bound is sharp.
The theorem permits arbitrary characteristic, infinite and imperfect fields,
and unrestricted multipliers.

The library also proves sharp completion and rigidity, scalar support
compression, imperfect-field Frobenius extraction and width descent,
finite-residue reduction, the universal erasure inverse, exact module and
commuting-action criteria, coefficient-rank bounds, and prime-index equality.
Convolution and the original symmetric-difference theorem over F₂ are consequences.
Version 1.2.0 makes the binary prime-index equality cases explicit, adds the
sharp odd-index parity refinement and errors-and-erasures uniqueness, and
proves the exact nonzero-weight criterion. See the [release notes](RELEASE_NOTES.md).

## Start here

| File | Purpose |
|---|---|
| [paper/main.pdf](paper/main.pdf) | Revised 47-page paper |
| [paper/main.tex](paper/main.tex) | Complete standalone LaTeX source |
| [WeightedPilz.lean](WeightedPilz.lean) | Public library entry point |
| [WeightedPilz/FieldTheorem.lean](WeightedPilz/FieldTheorem.lean) | All-field theorem, Laurent form, sharpness and convolution |
| [WeightedPilz/FinalConsequences.lean](WeightedPilz/FinalConsequences.lean) | Module/action criteria, rank bound and prime rigidity |
| [WeightedPilz/BinaryPrimeEquality.lean](WeightedPilz/BinaryPrimeEquality.lean) | All original Pilz equality cases at prime indices and their exact output sets |
| [WeightedPilz/PROOF_MAP.md](WeightedPilz/PROOF_MAP.md) | Correspondence for all 127 manuscript labels |
| [WeightedPilzFinalChecks.lean](WeightedPilzFinalChecks.lean) | Exact public types and module-origin transitive axiom audit |

## Build and verify

Install Lean using elan, then run from this directory:

```sh
lake exe cache get
lake build WeightedPilz
lake env lean WeightedPilzFinalChecks.lean
lake env lean WeightedPilzChecks.lean
```

The cache download is optional. `lean-toolchain` selects Lean **4.24.0**;
`lake-manifest.json` pins mathlib and every transitive dependency. Keep these
files unchanged. The default `lake build` also targets `WeightedPilz`.

On Windows, `./verify-weighted.ps1` verifies the source hashes, builds the
library, and runs both acceptance suites. On any platform with Python 3,
`python checks/verify_release.py` verifies the release manifest; add `--build`
to run the Lean build and both acceptance suites as well.
For a checksum-only PowerShell check, use `./verify-weighted.ps1 -HashesOnly`.

```lean
import WeightedPilz

#check WeightedPilz.weighted_interval
#check WeightedPilz.weighted_interval_laurent
#check WeightedPilz.weighted_convolution
```

To rebuild the paper, see [paper/README.md](paper/README.md).

## Verification and provenance

The original independent build compiled all 320 local library modules from
source, reusing only pinned third-party dependency caches. Version 1.2.0
preserves all 319 earlier proof modules, extends the root imports, adds four
consequence modules, and imports the existing elementary `Pilz.Parity` module.
The resulting **325-module** library build passed **3,482 jobs** using the
retained independent build. Both acceptance suites passed, including **69
explicit public-type checks**: all 58 earlier checks and 11 new checks.

The audit selects **7,008 declarations by originating project module**,
including **1,788 private declarations**, and checks their transitive
axioms. The separate namespace inventory contains 5,219 declarations,
including 3,783 WeightedPilz theorems and 928 imported Pilz theorems.
The only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`, custom axioms, or outstanding proof obligations.
Finite certificates are kernel checked; unbounded ranges use proved analytic
estimates. The earlier unweighted interval theorem is not an input to the
weighted field theorem.

The paper is a **new revision** of the preserved frozen baseline. It clarifies
local hypotheses and adds examples, navigation, historical context and
formalisation information. Version 1.2.0 adds the short consequences above;
all 123 baseline labels remain, alongside four new labels. The proof map
documents alternative formal proofs of some intermediate results.
[Paper provenance](paper/README.md) records the current paper and preserved baselines.
[MANIFEST.json](MANIFEST.json) records release contents, and
`SOURCE_MANIFEST.sha256` protects every other packaged file. The versioned ZIP
is `pilz-weighted-v1.2.1.zip`, with an adjacent SHA-256 checksum.
Version 1.2.1 revises the paper (an explicit Pilz corollary, corrected credit
and history, a clearer proof outline, and a candid statement of how the work
was produced) and corrects two out-of-date documentation comments in the Lean
sources; no Lean statement or proof changed.

The archive contains source, the paper, licences, citation metadata and concise
verification records. Dependency downloads, compiler installations, caches,
raw logs, exploratory scripts and earlier drafts are excluded.

## Licences

The Lean sources, tooling and project documentation are licensed under
[Apache-2.0](LICENSE). The paper PDF and LaTeX source are licensed under
[CC BY 4.0](paper/LICENSE). Dependencies retain their own licences.
