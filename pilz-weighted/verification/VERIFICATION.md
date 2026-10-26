# Verification record

## v1.2.1 · 26 October 2026

| Check | Result |
|---|---|
| From-scratch library build | Passed: all project outputs deleted first; 3,482 jobs, exit 0 (third-party mathlib cache reused at the pinned revision) |
| Both acceptance suites | Passed with exit code 0 |
| Module-origin transitive axiom audit | 7,008 declarations, including 1,788 private declarations; exactly `propext`, `Classical.choice`, `Quot.sound` |
| Named namespace inventory | 5,219 declarations; 3,783 WeightedPilz theorems and 928 Pilz theorems |
| Kernel replay (`lean4checker` v4.24.0) | All 295 `WeightedPilz` and `Pilz` modules and both root modules replayed with no failures (v1.2.0 sources); the two modules whose comments changed in v1.2.1 replayed again with no failures |
| Lean source changes since v1.2.0 | Documentation comments only, in `WeightedPilz/Binary.lean` and `WeightedPilz/ModuleConsequences.lean` |

The v1.2.0 record below is retained for reference.

## v1.2.0

**pilz-weighted v1.2.0 · 23 October 2026**

| Check | Result |
|---|---|
| Original independent project-source build | All 320 original library modules compiled from source |
| Current library build | Passed; 325 local modules, 3,482 jobs |
| Both current acceptance suites | Passed with exit code 0 |
| Explicit public theorem types | 69 checks: 58 retained and 11 new |
| Module-origin transitive axiom audit | 7,008 declarations, including 1,788 private declarations |
| Named namespace inventory | 5,219 declarations; 3,783 WeightedPilz theorems and 928 Pilz theorems |
| Earlier proof modules | All 319 unchanged; root imports extended |
| Manuscript correspondence | 127 labels: 123 retained plus four new mathematical labels |
| Revised PDF presentation | All 46 pages inspected; additions checked at higher resolution |
| Transitive axioms | Exactly `propext`, `Classical.choice`, `Quot.sound` |

The original v1.0.0 independent build started without local project outputs.
It reused only third-party caches after checking their revisions and tracked
sources against the pinned manifest. All 320 local modules compiled from
source and both acceptance files passed. Version 1.1.0 broadened the audit
to declarations selected by originating module, including private declarations.

Version 1.2.0 adds `BinaryPrimeEquality`, `ErrorCorrection`, `BinaryParity` and
`ScopeLimits`, plus the existing elementary `Pilz.Parity` dependency. The root
imports are extended. All 319 earlier proof modules and all 58 previous type
examples remain byte-identical. Eleven new explicit-type examples check the
added interfaces, and the compact regression suite also passes.

The current build ran in the retained independent verification tree. It
compiled the new source modules and updated root using the unchanged verified
library and pinned dependency outputs, then ran both acceptance suites. This
is incremental validation of the additions, not a second from-scratch build
of unchanged proofs. All 327 packaged Lean files and all dependency/configuration
files match the sources used in this run. A source snapshot and build logs are
retained in the workspace; the original verification tree was restored after
the release comparison.

The audit visits every declaration originating in imported `WeightedPilz` or
`Pilz` modules, including private/generated names, and its transitive
dependencies. It rejects any axiom outside the three listed above.

The paper's [proof map](../WeightedPilz/PROOF_MAP.md) covers all 127 labels and
documents alternative formal proofs of intermediate claims. The new binary
classification includes the positive-integer monomial bridge, the converse and
the exact output set. Error correction asserts uniqueness, not an efficient
decoder. The group-algebra research note is outside the certificate. The
separate `4/3` density theorem is already proved in its own release.

The [machine-readable record](results.json) records exact versions, counts and
evidence hashes. [Paper provenance](../paper/PROVENANCE.json) distinguishes the
new bytes from all preserved baselines. Raw logs, caches and tools are excluded.

Reproduce the build and audit using the [release README](../README.md), and
verify all packaged files with `python checks/verify_release.py`.
