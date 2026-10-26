# Release notes

## v1.2.1 — October 2026

A paper revision, made after an independent referee-style read by a separate AI reviewer. No Lean
statement or proof changed.

- **Title and abstract** now lead with Pilz's Extended 1–2–3 Conjecture.
- **Pilz's conjecture stated explicitly** as Corollary 1.2, with the formal
  name `WeightedPilz.weighted_symmetric_difference` and its proved identity
  with `Pilz.oddProduct` from the binary formalisation.
- **History and credit corrected and expanded:** Holdridge–Pach's density
  theorem is quoted with its exceptions, their notation `A*[n]` is defined,
  their `{1,2,4}` example and density computations are credited, and the
  Pach–Szabó constant is stated precisely.
- **What is new / outline:** a paragraph stating the new ingredient relative to
  Holdridge–Pach, three displayed statements outlining the proof, and a short
  route through the binary case.
- **Notation:** two clashes in Section 4 removed (`d₀` for `1+π(n/2)`; the
  weight vector and `wt C` no longer share a letter there).
- **How this work was produced:** states plainly that the written proofs have
  not been checked line by line by a human mathematician and that the Lean
  formalisation is authoritative.
- **Archive:** cited by its Zenodo concept DOI 10.5281/zenodo.23568997.
- **Lean documentation:** two out-of-date module comments (`Binary.lean`,
  `ModuleConsequences.lean`) that described the field theorem as an
  unproved hypothesis now point to where it is discharged. The project was
  rebuilt from scratch and all checks re-run.

## v1.2.0 — 23 October 2026

Four short consequences round out the weighted theorem without changing its
core proofs or hypotheses.

- **Binary prime-index equality:** for prime `ℓ ≥ 3`, equality holds exactly
  when `F_A = X(b) P_ℓ^(2^e - 1)` for a positive integer `b` and `e ≥ 0`.
  The output is exactly `{b*a^(2^e) : 1 ≤ a ≤ ℓ}`. The Lean proof establishes
  that the translating monomial comes from a positive integer.
- **Errors and erasures:** `2t + s < n` guarantees uniqueness of a finitely
  supported input with at most `t` errors outside `s` known erasures. Formal
  versions cover fields, modules with injective scalar weights, and commuting
  injective additive-group weights. No efficient decoder is asserted.
- **Sharp parity refinement:** the output cardinality is congruent to
  `n*|A|` modulo two. Odd `n` and even nonzero `|A|` force at least `n+1`
  outputs; `{1,2}` attains equality for every odd `n`.
- **Exact scope:** the universal weighted interval bound is equivalent to
  every interval weight being nonzero. The three-term binary polynomial
  `1+x+x²` has a two-term nonzero multiple, demonstrating why arbitrary
  monomial sets cannot replace the interval.

The paper is now 46 pages. All 123 original labels remain, with four new
mathematical labels. The release includes four new Lean modules and the existing
elementary `Pilz.Parity` dependency; every earlier proof module is unchanged.
All 58 previous explicit-type checks remain, and 11 new checks bring the total
to 69. The library build, both acceptance suites and module-origin axiom audit
passed; see the [verification record](verification/VERIFICATION.md).

The separate density companion already proves the uniform `4/3` strengthening
in Holdridge–Pach Remark 1.9, with exactly the stated exceptions. Its paper and
release were checked and require no new proof or mathematical revision.
The group-algebra observation is retained as a written research note in the
workspace and is outside this release's Lean certificate.

The author remains blank. Version 1.1.0 and the original frozen baseline are
preserved; citation metadata, provenance and manifests identify this new version.

## v1.1.0 — 23 October 2026

This revision improves the paper's standalone statements, exposition and
attribution, and strengthens the formalisation's acceptance audit. The main
theorem and the 320 Lean library modules are unchanged.

- The coefficient-rank theorem explicitly assumes `n ≥ 1`; the recalled
  endpoint inequality in Appendix B explicitly assumes positive degree;
  prime-index equality restates the nonzero-weight assumption. These
  hypotheses were already present in the relevant Lean interfaces.
- The title and abstract identify Pilz's conjecture. The introduction adds
  historical and methodological context, six primary references, a compact
  contents, and a range/dependency guide. It explains that the finite ranges
  are uniform in the field, weights and multiplier.
- Two worked examples illustrate cancellation at `n = 4` and residue correction
  in characteristic two, including the distinction between aggregate powers
  and fixed fresh-variable squares and the decrease in base-cofactor width.
- The paper identifies this release, the pinned Lean and mathlib versions,
  principal theorem names, and the proof map. It states precisely that some
  intermediate formal proofs use alternative arguments.
- The final acceptance suite selects declarations by originating source module.
  It audits all 6,938 imported project-module declarations, including 1,766
  private declarations, and their transitive dependencies. The separate
  namespace inventory is 5,171 declarations. Only `propext`, `Classical.choice`
  and `Quot.sound` occur.
- Versioned citation metadata and explicit current/baseline provenance accompany
  refreshed manifests and checksums. The author field is intentionally omitted.

All 58 public-type examples and all 123 original TeX labels are retained.
The new examples are explanatory; they do not introduce additional formal
theorem claims. The library build and both acceptance suites passed for this
configuration. This rerun reused the independently verified library outputs;
the original independent clean source build remains the provenance for the
unchanged library. See the [verification record](verification/VERIFICATION.md).

The v1.0.0 release and the original frozen manuscript remain preserved in the
workspace archive. The revised paper is not represented as byte-identical to
that baseline; [paper/PROVENANCE.json](paper/PROVENANCE.json) identifies both.

## v1.0.0 — 23 October 2026

Initial combined release of the frozen 42-page paper and complete Lean
formalisation, with pinned dependencies, proof map, acceptance checks,
independent clean-build evidence, separate code/paper licences, and manifests.
