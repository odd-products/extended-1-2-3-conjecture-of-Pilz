# Pilz's Extended 1–2–3 Conjecture over every field

*Sparse multiples of weighted integer intervals*

**[Read the paper](main.pdf)** · [LaTeX source](main.tex) ·
[Citation](../CITATION.md) · [Release notes](../RELEASE_NOTES.md)

46 A4 pages. The paper proves a sharp weighted form of Pilz's Extended
1–2–3 Conjecture over every field; the conjecture itself is Corollary 1.2.
The [proof map](../WeightedPilz/PROOF_MAP.md) records the correspondence with
the Lean development, including the intermediate results whose formal proofs
follow an alternative argument.

## Rebuild

From this directory, with a standard TeX Live or MiKTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The bibliography is included in the source; only standard LaTeX packages are
needed. Rebuilding may change PDF metadata or bytes, so the hashes below
identify the supplied files.

| File | SHA-256 |
|---|---|
| `main.tex` | `746d43a46b1c71e3283dcda4ef57d1d3b310d51a5a6ce139d87fe3c503da2117` |
| `main.pdf` | `b57668dd439ce8f274bb1c9fc241eead4bca9315f19a6a7fd41df72783fab6db` |

Machine-readable provenance, including hashes of earlier revisions, is in
[PROVENANCE.json](PROVENANCE.json).

The paper is licensed under
[Creative Commons Attribution 4.0 International](LICENSE).
