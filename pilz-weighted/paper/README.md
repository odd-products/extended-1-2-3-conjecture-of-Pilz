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
| `main.tex` | `8a5be3f08f6a493a517837312940cf0915f2c1eacc906b89ee1e42f946fd38bf` |
| `main.pdf` | `124133a084c659e40cc35d4b8ed51c326dde26e6375aca503eb0ba2b761496a4` |

Machine-readable provenance, including hashes of earlier revisions, is in
[PROVENANCE.json](PROVENANCE.json).

The paper is licensed under
[Creative Commons Attribution 4.0 International](LICENSE).
