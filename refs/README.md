# MLC reference store

This directory has two different jobs:

1. keep canonical bibliographic inputs for the review; and
2. keep reproducible source material used while formalizing definitions and
   proofs.

The arXiv source inventory is `mlc_sources.json`.  It is deliberately
separate from the historical research notes and from papers that are only
indirectly related to MLC.  To fetch metadata and the TeX source archive for
all entries, run:

```sh
python scripts/fetch_arxiv_sources.py
```

The fetcher retains the compressed source archive, arXiv metadata, and an
extracted directory.  It never replaces an existing source unless `--force`
is supplied.  The extracted main file is selected by the presence of
`\documentclass`/`\begin{document}` or a recognizable plain-TeX entry point;
the choice is recorded in `00README.json`.

## Canonical MLC references

| Key | Source | Role |
| --- | --- | --- |
| `douady-hubbard-orsay` | Douady--Hubbard, *Exploring the Mandelbrot Set: The Orsay Notes* | phase--parameter, external rays, foundational topology |
| `yoccoz-1995` | Yoccoz, *Theoreme de Siegel...*, Asterisque 231 | finitely-renormalizable puzzle/modulus theorem |
| `lyubich-geometry-1993` | Lyubich, *Geometry of quadratic polynomials...*, arXiv:math/9309215 | rigidity, moduli, local connectivity |
| `lyubich-dynamics-1997` | Lyubich, *Dynamics of quadratic polynomials, I--II* | renormalization and a priori bounds |
| `lyubich-dynamics-iii` | Lyubich, *Dynamics of quadratic polynomials, III* | parapuzzles and SBR measures |
| `lyubich-conformal-notes` | Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials* | lecture-note exposition and notation |
| `dudko-lyubich-satellite` | Dudko--Lyubich, bounded-type satellite parameters | proved MLC case |
| `dudko-lyubich-feigenbaum` | Dudko--Lyubich, *MLC at Feigenbaum points* | proved MLC case |
| `dudko-mlc-2025` | Dudko, *On the MLC Conjecture...* | current status and renormalization roadmap |

The label “Volume III” refers to the Astérisque paper above.  The review
does not assume that there is a canonical standalone “Volume IV”: later
results are cited as separate papers until a primary source establishes a
formal volume label.

## Storage policy

Files with the same arXiv identifier must have one canonical source archive.
Version changes are represented in metadata and filenames, not by copying the
same PDF under multiple author-based names.  Existing PDFs and research notes
are retained until their provenance and duplication status have been checked.
No deletion is performed merely because two filenames look similar.

The 2026-10-24 exact-hash audit removed two byte-identical author-named PDF
copies (`Dudko_1703.01206.pdf` and `Dudko_2512.24171.pdf`); the corresponding
versioned arXiv filenames remain.
