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
| `douady-hubbard-polynomial-like` | Douady--Hubbard, *On the dynamics of polynomial-like mappings*, Ann. Sci. ENS 18 (1985), 287--343 | polynomial-like maps and straightening |
| `hubbard-yoccoz` | Hubbard, *Local connectivity of Julia sets and bifurcation loci: three theorems of J.-C. Yoccoz* | exposition of the puzzle and MLC theorems |
| `yoccoz-1995` | Yoccoz, *Theoreme de Siegel...*, Asterisque 231 | Siegel/Brjuno foundation; distinct from the Hubbard puzzle exposition |
| `lyubich-geometry-1993` | Lyubich, *Geometry of quadratic polynomials...*, arXiv:math/9309215 | rigidity, moduli, local connectivity |
| `lyubich-dynamics-1997` | Lyubich, *Dynamics of quadratic polynomials, I--II* | renormalization and a priori bounds |
| `lyubich-dynamics-iii` | Lyubich, *Dynamics of quadratic polynomials, III* | parapuzzles and SBR measures |
| `lyubich-conformal-notes` | Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*, ICTP manuscript (2013), 256 PDF pages | existing local lecture-note version |
| `lyubich-conformal-book` | Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*, online book I--II | author-maintained book manuscript, 702 pages, stored as `Lyubich_book_vol_I-II_2023.pdf` (Git LFS); Volumes III--IV are announced in the preface (printed p. 5) and are not published |
| `dudko-lyubich-satellite` | Dudko--Lyubich, some bounded-type satellite parameters | source-specific MLC construction |
| `dudko-lyubich-feigenbaum` | Dudko--Lyubich, *MLC at Feigenbaum points* | proved MLC case |
| `dudko-mlc-2025` | Dudko, *On the MLC Conjecture...* | current status and renormalization roadmap |
| `kahn-kapiamba-lyubich-parabolic-primitive` | *MLC for parabolically bounded primitive renormalization* | 2026 MLC case |
| `elephant-puzzles` | Dudko--Kapiamba--Lyubich--Peterson, *Elephant puzzles*, in preparation as cited in arXiv:2606.27272v1 | puzzle Teichmuller-diameter dependency; no public manuscript specified there |
| `kahn-lyubich-elephant-eyes` | Kahn--Lyubich, *A priori bounds ... IV. Elephant Eyes*, arXiv:2601.21905 | Part IV of the a priori bounds series (elephant-eye combinatorics) |
| `kahn-lyubich-primitive` | Kahn, *A priori bounds ... I. Bounded primitive combinatorics*, arXiv:math/0609045 | Part I: bounded primitive type; length comparison; cited bounded-period theorem |
| `kahn-lyubich-decorations` | Kahn--Lyubich, *A priori bounds ... II. Decorations*, arXiv:math/0609046 | Part II: decoration condition |
| `kahn-lyubich-molecules` | Kahn--Lyubich, *A priori bounds ... III. Molecules*, arXiv:0712.2444 | Part III: molecule condition |
| `martens-nowicki-invariant-measures` | Martens--Nowicki, *Invariant measures for typical quadratic maps*, arXiv:math/9606220 (Asterisque 261 (2000), 239--252) | acim criterion (summable scaling factors); typical unique SBR measure, joint with Lyubich |
| `gaidashev-yampolsky-golden-mean` | Gaidashev--Yampolsky, *Golden mean Siegel disk universality and renormalization*, arXiv:1604.00717 (2016) | golden-mean Siegel disks; computer-assisted fixed point; no statement about local connectivity of M |
| `dudko-lyubich-selinger-pacman` | Dudko--Lyubich--Selinger, *Pacman renormalization and self-similarity of the Mandelbrot set near Siegel parameters*, arXiv:1703.01206 | Pacman renormalization near Siegel parameters; LaTeX fetched |
| `dudko-matings-laminations` | Dudko, *Matings with laminations*, arXiv:1112.4780 | matings and laminations; LaTeX fetched |
| `dudko-schleicher-core-entropy` | Dudko--Schleicher, *Core entropy of quadratic polynomials*, arXiv:1412.8760 | core entropy; LaTeX fetched |
| `dudko-lyubich-neutral-uniform-bounds` | Dudko--Lyubich, *Uniform a priori bounds for neutral renormalization*, arXiv:2210.09280 | neutral a priori bounds; LaTeX fetched |
| `dudko-luo-sierpinski-carpet` | Dudko--Luo, *Sierpinski carpet hyperbolic components of disjoint type are bounded*, arXiv:2509.25658 | Sierpinski-carpet components; LaTeX fetched |
| `dudko-hlushchanka-schleicher-canonical` | Dudko--Hlushchanka--Schleicher, arXiv:2209.02800 | adjacent: PCF rational maps; not about M; LaTeX fetched |
| `bartholdi-dudko-pilgrim-correspondences` | Bartholdi--Dudko--Pilgrim, arXiv:2407.15548 | adjacent: correspondences; not about M; LaTeX fetched |
| `bartholdi-dudko-branched-survey`, `-I`, `-II`, `-III`, `-IV` | Bartholdi--Dudko, *Algorithmic aspects of branched coverings*: survey arXiv:1512.05948 and Parts I–IV arXiv:1512.08539, 1603.04059, 1802.03045, 1610.02434 | adjacent: Thurston algorithms; quotes the Rees--Tan Lei criterion; LaTeX fetched |
| `efimov-continuous-k-theory`, `efimov-inverse-limits`, `efimov-devissage`, `efimov-rigidity-motives`, `efimov-theorem-of-heart-kh` | Efimov, arXiv:2405.12169, 2502.04123, 2505.13260, 2510.17010, 2603.08653 | categorical tools (Section 10 of `docs/review/10_categorical_branch.tex`); no MLC content; see the legacy-layout note below |
| `kahn-lyubich-quasi-additivity` | Kahn--Lyubich, *The Quasi-Additivity Law in Conformal Geometry*, arXiv:math/0505191 (Ann. Math. 169 (2009)) | covering and quasi-additivity laws (analytic tools) |
| `kahn-lyubich-unicritical-lc` | Kahn--Lyubich, *Local connectivity of Julia sets for unicritical polynomials*, arXiv:math/0505194 (Ann. Math. 170 (2009)) | Julia-set local connectivity for unicritical polynomials |
| `lyubich-asterisque-261` | Lyubich, *Dynamics of quadratic polynomials, III: parapuzzle and SBR measures*, Asterisque 261 (2000), 173--200 (NUMDAM: `numdam.org/article/AST_2000__261__173_0.pdf`; not stored in `refs/`) | parapuzzles, bounded shape, fine families; checked against the PDF |
| `dudko-lim-neutral-bubbles` | *Uniform bounds for bubbles of neutral quadratic polynomials* | neutral geometry |
| `dudko-lim-lyubich-neutral-rigidity` | *Rigidity of the attractor of neutral renormalization* | neutral rigidity |
| `shen-hybrid-classes` | *Complex Analytic Structure of Hybrid Classes...* | hybrid-class analytic base |
| `dudko-luo-lyubich-neutral-bounds` | *Uniform a priori bounds for neutral renormalization. Variation II* | neutral a priori bounds |

Lyubich's [publication list](https://www.math.stonybrook.edu/~mlyubich/papers/index.html)
lists the [online book](https://www.math.stonybrook.edu/~mlyubich/book.pdf)
as volumes I--II. The 2013 ICTP PDF already in this directory is a separate
manuscript version. The Astérisque paper's “III” and the a priori-bounds
series' “IV” are research-article numbers, rather than extra book volumes.
Likewise, *Elephant puzzles* and *Elephant Eyes* are different works.

The book now records the Gaussian-area obstruction proved in
[`Mlc/Literature/ModelAudit.lean`](../Mlc/Literature/ModelAudit.lean).
Classical source theorems must be formalized using genuine conformal
modulus and graph-cut pieces; their proofs cannot supply the refuted
frozen lower-bound certificate.

Note: `math/0607155` is not Kahn's Part I; it is a different paper (Bin Zhu, generalized cluster complexes) and must not be used. Kahn's Part I is `math/0609045`.

## Adjacent and categorical sources

These entries are kept because the review classifies them; none is an MLC proof.

- The five Efimov papers supply categorical tools: continuous K-theory, Mittag-Leffler limits, dévissage,
  rigidity of localizing motives, and the theorem of the heart for KH.  Their TeX sources contain none of the
  words Mandelbrot, Julia, Green, holomorphic motion, Douady or Yoccoz.  Their statements are in
  `docs/review/10_categorical_branch.tex`.
- The Bartholdi--Dudko survey and Parts I--IV, the Dudko--Hlushchanka--Schleicher paper, and the
  Bartholdi--Dudko--Pilgrim paper concern Thurston maps and correspondences.  Their only MLC-related statement is
  the quoted Rees--Tan Lei mating criterion, classified in `docs/review/17_digests_modern.tex`.
- Legacy layout: `arxiv-2405.12169/` and `arxiv-2502.04123.tex` predate the fetcher's `00README.json` marker.
  Do not run `scripts/fetch_arxiv_sources.py` for `efimov-continuous-k-theory` or `efimov-inverse-limits`: it
  would add a second main TeX file beside the existing one.  Refresh these by hand and record the version.

## Storage policy

Files with the same arXiv identifier must have one canonical source archive.
Version changes are represented in metadata and filenames, not by copying the
same PDF under multiple author-based names.  Existing PDFs and research notes
are retained until their provenance and duplication status have been checked.
No deletion is performed merely because two filenames look similar.

The 2026-10-24 exact-hash audit removed two byte-identical author-named PDF
copies (`Dudko_1703.01206.pdf` and `Dudko_2512.24171.pdf`); the corresponding
versioned arXiv filenames remain.
