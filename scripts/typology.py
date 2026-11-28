"""Typology of the parameter plane for the Progress page.

The page answers four questions.

* **How are M and its boundary assembled?** `PARTS` is the hierarchy: the interior contains the
  hyperbolic components (that they exhaust it is the hyperbolicity conjecture), the boundary
  splits by dimension into a skeleton (the boundaries of the components, of dimension at most 1)
  and a wild part (relative to the skeleton, of dimension 2), and, crossing it, by the type of
  the renormalization of the parameter. The leaves are the classes of the programme
  (`programme.CLASSES`), each with the chain of statements that it needs and their status
  (proved, reduced, literature, open). The dictionary (which parameter has which class and
  tower) is a parameter of every statement.
* **Which characteristic fragments exist?** `FRAGMENTS` are the named features of the parameter
  plane (the valleys, the rabbit, the airplane, ...). Their typing is informal and local; each
  is placed in the hierarchy and in one of the three regimes of the survey (Dudko, §3, the
  universality statement after Question 3.1).
* **Which objects does the formalization add?** `OBJECTS` are the families of Lean definitions
  (towers, levels, nests, collars, stacked annuli, ...) that act across scales; `object_usage`
  reads from the dependency graph of the Lean declarations which objects each statement and each
  reduction of the programme rest on.
* **When was each object mastered?** The ledger lists the milestones of every update;
  `MILESTONE_OBJECTS` assigns each milestone to an object, which gives the timeline.

Nothing here is a claim about the mathematics beyond the statements that the Lean sources prove
or that the programme takes as hypotheses from the literature; the statuses are computed from the
Lean sources (`programme.lemma_statuses`). The thumbnails are numerical renderings of the
parameter plane and an illustration that the Lean proof does not use.
"""

from __future__ import annotations

import base64
import re
import struct
import zlib
from dataclasses import dataclass
from pathlib import Path

from programme import CLASSES, LEMMA, LEMMAS, STATUSES, lemma_statuses, strip_lean_comments

# ---------------------------------------------------------------------------------------------
# The three regimes of a scale near a boundary parameter (Dudko, §3, after Question 3.1).
# ---------------------------------------------------------------------------------------------

REGIMES = {
    "tan": (
        "Tan Lei regime",
        "every hyperbolic component is small against the scale δ, and M looks like the Julia "
        "set J_c near c",
    ),
    "near": (
        "near-neutral regime",
        "a hyperbolic component of size ≫ δ reaches the scale δ: near-parabolic and "
        "near-Siegel effects",
    ),
    "ql": (
        "quadratic-like regime",
        "the components that matter have size comparable to δ: little copies of M",
    ),
}


# ---------------------------------------------------------------------------------------------
# The hierarchy: how M and its boundary are assembled.
# ---------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Part:
    key: str
    parent: str | None
    title: str
    dim: str  # the Hausdorff dimension that is known for the part
    text: str
    classes: tuple[str, ...] = ()  # keys of programme.CLASSES: the leaf chains
    lean: str = ""  # the Lean statement that carries the part
    brief: str = ""  # one line, shown beside the title
    node: str = ""  # the node of the proof spine that the part links to


PARTS: tuple[Part, ...] = (
    Part(
        "M",
        None,
        "The Mandelbrot set M",
        "2",
        "Compact (Lean) and connected (Douady–Hubbard, a hypothesis here). The disjoint union of "
        "its interior and its boundary. MLC means that M is locally connected at every boundary "
        "point; at interior points that is automatic.",
        lean="MLC.mlc_conjecture",
        brief="compact and connected: the interior and the boundary",
    ),
    Part(
        "interior",
        "M",
        "Interior and its hyperbolic components",
        "2",
        "The interior of M contains the hyperbolic components: the parameters with an attracting "
        "cycle of some period p. That they exhaust the interior is the hyperbolicity conjecture, "
        "a consequence of MLC that is open and lies outside the programme. Each hyperbolic "
        "component has a root, a centre and a multiplier map onto the unit disk, and carries a "
        "little copy of M (tuning). The kernel-checked grid certifies the exterior and part of "
        "the interior up to a layer along the boundary.",
        brief="contains the hyperbolic components (attracting cycle of period p); equality is "
        "the hyperbolicity conjecture",
    ),
    Part(
        "cardioid",
        "interior",
        "Main cardioid (period 1)",
        "2",
        "The parameters with an attracting fixed point. Its root is the cusp c = 1/4, where the "
        "fixed point has multiplier 1, so the census counts it as primitive; its boundary is "
        "parametrized by the multiplier e^{2πiθ}.",
        brief="period 1; the root is the cusp c = 1/4 (primitive in the census)",
    ),
    Part(
        "satellite",
        "interior",
        "Satellite components",
        "2",
        "Attached to a component of a smaller period q at a point where the cycle of that "
        "component has multiplier e^{2πik/r}, r ≥ 2; the period is qr. In the survey's gloss "
        "(Dudko, Figure 3) the satellite case is the zero-entropy case; the gloss concerns the "
        "renormalization step relative to its parent and not the entropy of the whole parameter.",
        brief="attached to a component of period q, multiplier e^{2πik/r}; zero entropy as a "
        "renormalization step",
    ),
    Part(
        "primitive",
        "interior",
        "Primitive components",
        "2",
        "The root has multiplier 1: a cusp that lies on the boundary of no other component (the "
        "main cardioid is counted here and has no parent step). For a primitive renormalization "
        "step below another copy, the survey's gloss (Dudko, Figure 3) is positive entropy "
        "relative to the parent.",
        brief="the root is a cusp with multiplier 1; a primitive step has positive relative "
        "entropy",
    ),
    Part(
        "boundary",
        "M",
        "Boundary ∂M = the unresolved set R",
        "2",
        "The set M ∖ int M that the grid certificate bounds: the same set for every depth of the "
        "grid, which lowers only the certified bound on its area. Hausdorff dimension 2 "
        "(Shishikura's theorem, taken as a hypothesis here).",
        lean="MLC.Research.frontier_mandelbrot_eq_unresolved",
        brief="the unresolved set R of the grid, of dimension 2",
    ),
    Part(
        "skeleton",
        "boundary",
        "Skeleton: boundaries of the components",
        "≤ 1",
        "The boundary of a hyperbolic component is a Jordan curve, real-analytic away from its "
        "root (a cusp at the root of a primitive component), and a parameter with an indifferent "
        "cycle lies on the boundary of a hyperbolic component. So the parameters with an "
        "indifferent cycle lie on countably many analytic images of the circle: a published "
        "fact that is not formalized and enters the Lean statements as the hypothesis hskel. "
        "Countably many C¹ loops have dimension at most 1 (Lean).",
        lean="MLC.Research.dimH_iUnion_range_le_one",
        brief="countably many analytic curves, cusps allowed: dimension at most 1",
        node="prog:dimension",
    ),
    Part(
        "parabolic",
        "skeleton",
        "Parabolic parameters",
        "0",
        "A cycle with a multiplier that is a root of unity: the roots of the components and the "
        "other points of their boundaries with a rational multiplier, countably many. M is "
        "locally connected there (Douady–Hubbard); in the programme they belong to the class "
        "finite, Lemma Y.",
        classes=("finite",),
        brief="a countable set; Lemma Y",
        node="lemma:yoccoz",
    ),
    Part(
        "indifferent",
        "skeleton",
        "Siegel and Cremer parameters",
        "≤ 1",
        "An irrationally indifferent cycle: the parameters on the boundary of a hyperbolic "
        "component where the multiplier is e^{2πiθ} with θ irrational (Siegel: the cycle has a "
        "Siegel disk; Cremer: it has none). In the programme they form the class neutral, "
        "Lemma N (Theorem 4.2 of the survey, as read by the programme).",
        classes=("neutral",),
        brief="an irrational multiplier angle; Lemma N",
        node="lemma:neutral",
    ),
    Part(
        "wild",
        "boundary",
        "Wild part: what the skeleton misses",
        "2",
        "The boundary outside the loops of the skeleton. Lean: for every countable family of C¹ "
        "loops the wild part of ∂M has dimension 2, and when the family covers the indifferent "
        "boundary parameters (hskel) the boundary parameters with no indifferent cycle have "
        "dimension 2. The wild part depends on the family (a larger family has a smaller wild "
        "part); the set of boundary parameters with no indifferent cycle does not. The extra "
        "dimension of the fractal boundary over the smooth curves lies in these parameters. It "
        "is not the set of Problems 4.3 and 4.4: it also contains parameters for which MLC is "
        "known, such as the Misiurewicz parameter c = i.",
        lean="MLC.Research.ShishikuraDimension.dimH_noIndifferentCycle_eq_two",
        brief="no indifferent cycle: the dimension 2 lies here; it also holds cases where MLC is "
        "known",
        node="prog:boundary_split",
    ),
    Part(
        "misiurewicz",
        "wild",
        "Not infinitely renormalizable",
        "—",
        "Misiurewicz parameters (the critical orbit is strictly preperiodic) are end points and "
        "branch points of the filaments of M, for example the end points c = −2 and c = i; and "
        "the other parameters that are not infinitely renormalizable (Yoccoz, Hubbard; "
        "Lemma Y). Near a Misiurewicz parameter M and the Julia set J_c look alike (Tan Lei).",
        classes=("finite",),
        brief="Misiurewicz parameters (end points and branch points of filaments), and the rest; "
        "Lemma Y",
        node="lemma:yoccoz",
    ),
    Part(
        "infinite",
        "wild",
        "Infinitely renormalizable: a nest of copies",
        "—",
        "The parameter lies in infinitely many nested little copies M ⊃ M₁ ⊃ M₂ ⊃ …; every step "
        "is primitive or satellite and has a relative period. The formalization does not "
        "construct the copies: it models the nest by a sequence of numbers (WidthTower: the "
        "relative periods, the kinds of the steps and the degenerations of the levels) that the "
        "dictionary may assign to a parameter (an optional tower), and the classes below are "
        "the combinatorial types of this sequence.",
        brief="nested copies M ⊃ M₁ ⊃ …, modelled by a tower of numbers (WidthTower)",
    ),
    Part(
        "bounded",
        "infinite",
        "Bounded type",
        "—",
        "Bounded relative periods, primitive or satellite; the Feigenbaum parameter is the "
        "model (every level is a satellite of relative period 2). Theorem 4.1.",
        classes=("boundedType",),
        brief="bounded relative periods; Theorem 4.1",
        node="lemma:boundedType",
    ),
    Part(
        "anti",
        "infinite",
        "Anti-Molecule",
        "—",
        "Primitive levels far from the Molecule, with large relative periods (Kahn–Lyubich).",
        classes=("antiMolecule",),
        brief="primitive levels far from the Molecule",
        node="lemma:antiMolecule",
    ),
    Part(
        "qg",
        "infinite",
        "Quadratic growth (satellite)",
        "—",
        "Satellite levels whose type sequence grows quadratically (Cheraghi–Shishikura, "
        "Theorem D).",
        classes=("quadraticGrowth",),
        brief="satellite levels, type sequence of quadratic growth",
        node="lemma:quadraticGrowth",
    ),
    Part(
        "unbounded",
        "infinite",
        "Unbounded satellite type · Problem 4.3",
        "—",
        "Infinitely many satellite levels with unbounded relative periods, outside the class of "
        "quadratic growth: the pseudo-Siegel a priori bounds of Problem 4.3.",
        classes=("unboundedSatellite",),
        brief="unbounded relative periods at satellite levels; open",
        node="open:4.3",
    ),
    Part(
        "virtualBounded",
        "infinite",
        "Virtual Molecule, bounded satellite chain · Problem 4.4",
        "—",
        "A primitive level close to the Molecule with a long virtual chain of satellite copies "
        "of bounded relative periods (the first subcase of Problem 4.4).",
        classes=("virtualBounded",),
        brief="a virtual chain of satellite copies of bounded periods; open",
        node="open:4.4",
    ),
    Part(
        "virtualNear",
        "infinite",
        "Virtual Molecule, near-neutral · Problem 4.4",
        "—",
        "A primitive level close to the Molecule with a virtual near-neutral step (the second "
        "subcase of Problem 4.4).",
        classes=("virtualNearNeutral",),
        brief="a virtual near-neutral step; open",
        node="open:4.4",
    ),
)
PART = {part.key: part for part in PARTS}


# ---------------------------------------------------------------------------------------------
# The characteristic fragments of the parameter plane: the existing, informal typing.
# ---------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Fragment:
    key: str
    name: str
    where: str
    center: tuple[float, float]
    half: float  # half of the side of the window
    regime: str  # a key of REGIMES; "" for the interior
    part: str  # a key of PARTS
    note: str
    mark: bool = False  # mark the centre of the window


FRAGMENTS: tuple[Fragment, ...] = (
    Fragment(
        "cardioid",
        "Cardioid and basilica disc",
        "periods 1 and 2",
        (-0.5, 0.0),
        1.0,
        "",
        "interior",
        "Hyperbolic components: the interiors are certified by the grid up to a thin layer along "
        "the boundary.",
    ),
    Fragment(
        "rabbit",
        "Rabbit",
        "period 3, rotation number 1/3; c ≈ −0.1226 + 0.7449i",
        (-0.12, 0.76),
        0.17,
        "ql",
        "satellite",
        "A satellite component with its little copy of M; the Julia set at the centre of the "
        "component is the Douady rabbit.",
    ),
    Fragment(
        "airplane",
        "Airplane",
        "period 3, primitive; c ≈ −1.7549",
        (-1.7549, 0.0),
        0.05,
        "ql",
        "primitive",
        "A primitive component with its little copy of M; the Julia set at the centre is the "
        "airplane.",
    ),
    Fragment(
        "seahorse",
        "Seahorse Valley",
        "near c = −3/4, the root of the period-2 disc",
        (-0.7453, 0.1127),
        0.012,
        "near",
        "skeleton",
        "Spirals along the boundary of a large component: near-parabolic renormalization.",
    ),
    Fragment(
        "elephant",
        "Elephant Valley",
        "near c = 1/4, the root of the cardioid",
        (0.2775, 0.0105),
        0.02,
        "near",
        "skeleton",
        "The same regime at the cusp of the cardioid, where satellite copies of large relative "
        "period accumulate.",
    ),
    Fragment(
        "siegel",
        "Siegel parameter",
        "c = μ/2 − μ²/4, μ = e^{2πiθ}, θ = (√5 − 1)/2",
        (-0.39054, -0.58679),
        0.02,
        "near",
        "indifferent",
        "A smooth arc of the skeleton, with an irrationally indifferent fixed point (class "
        "neutral, Lemma N); the parameter is a point of the boundary of the main cardioid.",
        True,
    ),
    Fragment(
        "feigenbaum",
        "Feigenbaum point",
        "c ≈ −1.40116, the limit of period doubling",
        (-1.4011551890920506, 0.0),
        0.012,
        "ql",
        "bounded",
        "Infinitely renormalizable of bounded type: every level is a satellite of relative "
        "period 2 (Theorem 4.1).",
        True,
    ),
    Fragment(
        "dendrite",
        "Tip c = i (Misiurewicz)",
        "c = i: the critical orbit 0 → i → −1+i → −i → −1+i → … is strictly preperiodic "
        "(preperiod 2, period 2)",
        (0.0, 1.0),
        0.035,
        "tan",
        "misiurewicz",
        "An end point of a filament of M: a window centred on c = i shows M crossing the ring "
        "around the centre once, at every scale that was tried. No hyperbolic component reaches "
        "the scale, and M and the Julia set J_c look alike near it (Tan Lei regime); Lemma Y "
        "covers it.",
        True,
    ),
)
FRAGMENT = {fragment.key: fragment for fragment in FRAGMENTS}


# ---------------------------------------------------------------------------------------------
# The objects that the formalization adds.
# ---------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Obj:
    key: str
    title: str
    picture: str  # what it is in the picture of M
    modules: tuple[str, ...]  # files below Mlc/, without the extension


OBJECTS: tuple[Obj, ...] = (
    Obj(
        "assembly",
        "Dictionary and assembly",
        "Each parameter gets a class and an optional tower of levels (Geometry: tower : ℂ → Option "
        "WidthTower; LevelGeometry adds their level sets); the cases assemble into MLC "
        "(ProgrammeInput, mlc_of_programme).",
        (
            "Research/CaseTree",
            "Research/Published",
            "Research/Problem43",
            "Research/Problem44",
            "Research/Programme",
            "Research/ReturnBudget",
            "Research/LevelGeometry",
            "ProgrammeRoot",
        ),
    ),
    Obj(
        "grid",
        "Certified grid",
        "A kernel-checked cover of the neighbourhood of ∂M by cells: the exterior and part of the "
        "interior outside it are resolved, and the area of the rest is bounded.",
        (
            "GridDefs",
            "GridTMCertificate",
            "GridCertificate",
            "GridCertified",
            "GridTiles/",
            "Research/AreaZero",
        ),
    ),
    Obj(
        "tower",
        "Tower of copies (a model)",
        "An abstract model of the nest M ⊃ M₁ ⊃ M₂ ⊃ …: the sequence of relative periods, of kinds "
        "(primitive or satellite) and of degenerations W_k of the levels, which the dictionary "
        "may assign to a parameter; the copies themselves are not constructed. The recursion "
        "with jumps and the a priori bounds.",
        ("Research/Degeneration", "Research/TailInvariance"),
    ),
    Obj(
        "extremal",
        "Moduli as extremal length",
        "The modulus of an annulus as the extremal width of the loops that go around it: series "
        "and parallel laws, round annuli exactly, rectangles.",
        (
            "Research/ExtremalLength",
            "Research/AnnulusModulus",
            "Research/RectangleModulus",
            "Research/RoundAnnulus",
        ),
    ),
    Obj(
        "nest",
        "Parameter nest",
        "Connected pieces of M around c with annuli between them: divergent moduli force the "
        "pieces to shrink (Lemma T in moduli form).",
        (
            "Research/NestModulus",
            "Research/DivergentNest",
            "Research/NestRate",
            "Research/ParameterGeometry",
            "Research/PhaseParameter",
        ),
    ),
    Obj(
        "pullback",
        "Pullback along the iterates",
        "How the iterates of f_c pull an annulus back, with area multiplicity 2^p.",
        ("Research/AreaMultiplicity",),
    ),
    Obj(
        "chart",
        "Charts of bounded dilatation",
        "C¹ charts between neighbourhoods change the moduli by a bounded factor.",
        ("Research/QuasiInvariance",),
    ),
    Obj(
        "collar",
        "Collars",
        "A quasi-round collar around an annulus forces a definite modulus; the pseudo-Siegel "
        "disks are expected to provide them (Lemma G).",
        ("Research/Collar",),
    ),
    Obj(
        "level",
        "Level sets and annuli",
        "A level of the tower as a pair of sets, the filled set and its range domain, and the "
        "annulus between them; Lemmas G and T as geometric statements.",
        ("Research/LevelTower", "Research/RoundTower"),
    ),
    Obj(
        "stacking",
        "Stacked annuli",
        "p disjoint sub-annuli inside the annulus of a deeper level: Lemma D as a geometric "
        "statement, exact in the round model.",
        ("Research/Stacking",),
    ),
    Obj(
        "criterion",
        "Yoccoz criterion in modulus form",
        "Divergent moduli give local connectivity at c, with a logarithmic bound on the depth.",
        ("Research/CollarCriterion",),
    ),
    Obj(
        "virtual",
        "Virtual hulls",
        "Hulls of the Cantor small Julia sets that contain the critical orbit up to several "
        "returns (Problem 4.4); their shrinking is the separation estimate.",
        (
            "Research/VirtualMolecule",
            "Research/VirtualShrinking",
            "Research/ConnectedHull",
            "FilledJuliaConnected",
        ),
    ),
    Obj(
        "dimension",
        "Dimension of the boundary",
        "The boundary has dimension 2 and a loop has dimension at most 1: the smooth skeleton "
        "and the wild part (relative to it), and the finite partition into classes that shares "
        "the dimension.",
        ("Research/Dimension", "Research/BoundarySplit"),
    ),
    Obj(
        "peano",
        "Peano parametrization",
        "M as a quotient of the interval: MLC holds exactly when M is a regular epimorphic "
        "image of [0, 1] in the category of compact Hausdorff spaces.",
        ("Research/PeanoObject",),
    ),
)
OBJECT = {obj.key: obj for obj in OBJECTS}


def object_usage(fq_index, edges, lemmas=None) -> dict[str, set[str]]:
    """For every statement of the programme, the objects whose modules hold a declaration in the
    dependency cone of the statement or of the Lean theorem that reduces it. `fq_index` maps a
    declaration to its file (`Decl.file`) and `edges` to the declarations that it uses. An entry
    of `Obj.modules` that ends with a slash stands for every file of that directory."""
    files: dict[str, str] = {}
    directories: list[tuple[str, str]] = []
    for obj in OBJECTS:
        for module in obj.modules:
            if module.endswith("/"):
                directories.append((f"Mlc/{module}", obj.key))
            else:
                files[f"Mlc/{module}.lean"] = obj.key

    def object_of(path: str) -> str | None:
        if path in files:
            return files[path]
        return next((key for prefix, key in directories if path.startswith(prefix)), None)

    usage: dict[str, set[str]] = {}
    for lemma in LEMMAS if lemmas is None else lemmas:
        stack = [lemma.lean] + ([lemma.reduction] if lemma.reduction else [])
        seen: set[str] = set()
        used: set[str] = set()
        while stack:
            name = stack.pop()
            if name in seen:
                continue
            seen.add(name)
            decl = fq_index.get(name)
            found = object_of(decl.file) if decl is not None else None
            if found is not None:
                used.add(found)
            stack.extend(edges.get(name, ()))
        usage[lemma.key] = used
    return usage

# The objects of a milestone of the ledger, by the beginning of its label.
MILESTONE_OBJECTS: tuple[tuple[str, str], ...] = (
    ("Conditional root", "assembly"),
    ("Harmonic budget", "assembly"),
    ("Connected parameter nest", "nest"),
    ("Virtual-Molecule bridge", "virtual"),
    ("Filled-Julia topology", "virtual"),
    ("Minimal connected hull", "virtual"),
    ("Mandelbrot compactness", "grid"),
    ("Residual-area envelope", "grid"),
    ("Certified interior parameter ball", "grid"),
    ("Kernel-checked grid bound", "grid"),
    ("A priori bounds from uniform control", "tower"),
    ("Both uniformities are necessary", "tower"),
    ("A priori bounds are equivalent to a jump cap", "tower"),
    ("Extremal length: series and parallel laws", "extremal"),
    ("Tail invariance", "tower"),
    ("Modulus of a round annulus", "extremal"),
    ("Modulus of a rectangle", "extremal"),
    ("Moduli of nested annuli force shrinking", "nest"),
    ("Lemma T is equivalent to its moduli form", "nest"),
    ("Grötzsch's inequality for a coarsening", "nest"),
    ("Pullback law for the iterates", "pullback"),
    ("The virtual separation estimate", "virtual"),
    ("Quasi-invariance of extremal width", "chart"),
    ("Collar estimate", "collar"),
    ("Lemma G from collars", "level"),
    ("Lemma T from the phase–parameter comparison", "level"),
    ("C¹ charts preserve the Hausdorff dimension", "dimension"),
    ("A fiber of positive Hausdorff dimension", "dimension"),
    ("The boundary parameters with no indifferent cycle", "dimension"),
    ("Peano objects of CompHaus", "peano"),
    ("The modulus of the round annulus", "extremal"),
    ("A Teichmüller-type estimate", "nest"),
    ("The Yoccoz criterion in modulus form", "criterion"),
    ("Lemma D from stacked annuli", "stacking"),
    ("In the round model Lemma D is equivalent", "stacking"),
    ("MLC from the geometric form", "assembly"),
    ("MLC from the lemmas of the programme", "assembly"),
    ("Unconditional MLC", "assembly"),
)


def object_of_label(label: str) -> str | None:
    for prefix, key in MILESTONE_OBJECTS:
        if label.startswith(prefix):
            return key
    return None


# ---------------------------------------------------------------------------------------------
# Counts that the page shows.
# ---------------------------------------------------------------------------------------------

# A declaration of a Lean source without comments: a keyword at the start of a line, after the
# attributes (`@[simp]`) and the modifiers. An anonymous instance counts, as in Lean.
DECLARATION = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*\n?[ \t]*)*"
    r"(?:(?:noncomputable|private|protected|unsafe|partial|mutual)\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|structure|inductive|class|instance)\s",
    re.MULTILINE,
)


def count_declarations(source: str) -> int:
    """The declarations of a Lean source: the lines of its comments, docstrings included, do
    not count, and the attributes before a keyword are read."""
    return len(DECLARATION.findall(strip_lean_comments(source)))


def declaration_counts(repo_root: Path) -> dict[str, int]:
    """The number of declarations in the files of every object (a directory entry, which ends
    with a slash, is not counted: the tile modules are counted apart)."""
    out = {}
    for obj in OBJECTS:
        total = 0
        for module in obj.modules:
            if module.endswith("/"):
                continue
            path = repo_root / "Mlc" / f"{module}.lean"
            if path.exists():
                total += count_declarations(path.read_text(encoding="utf-8"))
        out[obj.key] = total
    return out


def _mobius(n: int) -> int:
    result, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            result = -result
        p += 1
    return -result if n > 1 else result


def _totient(n: int) -> int:
    result, m, p = n, n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            result -= result // p
        p += 1
    return result - result // m if m > 1 else result


def census(max_period: int = 10) -> list[dict[str, int]]:
    """The hyperbolic components of M by period: the number of centres of exact period p is
    the sum over d | p of mu(p/d) 2^(d-1); a component is satellite when it is attached to a
    component of period q | p, q < p, with a rotation number k/r, gcd(k, r) = 1 (phi(r) of them
    for every component of period q), and primitive otherwise. The main cardioid, whose root has
    multiplier 1, is the primitive component of period 1."""
    total = {
        p: sum(_mobius(p // d) * 2 ** (d - 1) for d in range(1, p + 1) if p % d == 0)
        for p in range(1, max_period + 1)
    }
    rows = []
    for p in range(1, max_period + 1):
        satellite = sum(total[q] * _totient(p // q) for q in range(1, p) if p % q == 0)
        rows.append({"period": p, "total": total[p], "satellite": satellite,
                     "primitive": total[p] - satellite})
    return rows


# ---------------------------------------------------------------------------------------------
# Thumbnails of the fragments (numerical renderings, an illustration).
# ---------------------------------------------------------------------------------------------


def _png_rgb(pixels) -> bytes:  # pixels: uint8 array (h, w, 3)
    height, width, _ = pixels.shape
    raw = b"".join(b"\x00" + pixels[row].tobytes() for row in range(height))

    def chunk(tag: bytes, data: bytes) -> bytes:
        body = tag + data
        return struct.pack(">I", len(data)) + body + struct.pack(">I", zlib.crc32(body))

    return (
        b"\x89PNG\r\n\x1a\n"
        + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0))
        + chunk(b"IDAT", zlib.compress(raw, 9))
        + chunk(b"IEND", b"")
    )


def render_fragment(center: tuple[float, float], half: float, size: int = 128,
                    max_iter: int = 1500) -> bytes:
    """A PNG of the window of the parameter plane: the boundary glows (distance estimate),
    the exterior is banded by the escape time, the interior is dark."""
    import numpy as np

    xs = center[0] + half * np.linspace(-1.0, 1.0, size)
    ys = center[1] + half * np.linspace(1.0, -1.0, size)
    c = xs[None, :] + 1j * ys[:, None]
    z = np.zeros_like(c)
    dz = np.zeros_like(c)
    count = np.full(c.shape, -1.0)
    dist = np.zeros(c.shape)
    active = np.ones(c.shape, dtype=bool)
    with np.errstate(all="ignore"):
        for n in range(max_iter):
            rows, cols = np.nonzero(active)
            if rows.size == 0:
                break
            zz, dd, cc = z[rows, cols], dz[rows, cols], c[rows, cols]
            dd = 2.0 * zz * dd + 1.0
            zz = zz * zz + cc
            z[rows, cols], dz[rows, cols] = zz, dd
            gone = np.abs(zz) > 1e6
            if gone.any():
                r, k = rows[gone], cols[gone]
                modulus = np.abs(zz[gone])
                count[r, k] = n + 1 - np.log2(np.log(modulus))
                slope = np.abs(dd[gone])
                dist[r, k] = np.where(
                    np.isfinite(slope) & (slope > 0),
                    0.5 * modulus * np.log(modulus) / slope,
                    0.0,
                )
                active[r, k] = False
    pixel = 2.0 * half / size
    t = dist / pixel
    glow = np.exp(-t / 1.6)
    band = 0.5 + 0.5 * np.sin(0.35 * np.where(count > 0, count, 0.0))
    inside = active
    base = np.array([13.0, 24.0, 44.0])
    tint = np.array([22.0, 52.0, 96.0])
    edge = np.array([125.0, 211.0, 252.0])
    pixels = base + band[..., None] * tint * 0.35
    pixels = pixels * (1.0 - glow[..., None]) + edge * glow[..., None]
    pixels[inside] = np.array([5.0, 9.0, 18.0])
    return _png_rgb(np.clip(pixels, 0, 255).astype(np.uint8))


def fragment_uri(fragment: Fragment, size: int = 128) -> str:
    png = render_fragment(fragment.center, fragment.half, size)
    return "data:image/png;base64," + base64.b64encode(png).decode("ascii")


# ---------------------------------------------------------------------------------------------
# HTML.
# ---------------------------------------------------------------------------------------------

CODE = re.compile(r"^Lemma\s+(\S+)")


def lemma_code(key: str) -> str:
    found = CODE.match(LEMMA[key].title)
    return found.group(1) if found else key


STATUS_TEXT = {
    "proved": "proved in Lean",
    "reduced": "derived in Lean from a geometric statement that is open",
    "published": "motivated by the literature and taken as a hypothesis (the bridge from the "
    "published statement to the formal one is not formalized)",
    "open": "open",
}


def lemma_chip(name: str, status: str) -> str:
    """A chip of a lemma, coloured by its status and linked to its node of the proof spine."""
    from progress_report import esc

    return (
        f'<a class="lm {status}" href="#n=lemma:{esc(name)}" '
        f'title="{esc(LEMMA[name].title)}: {esc(STATUS_TEXT[status])}">'
        f"{esc(lemma_code(name))}</a>"
    )


def chain_html(class_key: str, statuses: dict[str, str]) -> str:
    lemmas = next(chain for key, _, chain in CLASSES if key == class_key)
    chips = "".join(lemma_chip(name, statuses[name]) for name in lemmas)
    counts = {status: sum(1 for name in lemmas if statuses[name] == status) for status in STATUSES}
    bar = "".join(
        f'<span class="seg {status}" style="flex:{counts[status]}"></span>'
        for status in STATUSES
        if counts[status]
    )
    return (
        f'<div class="ty-chain"><div class="ty-bar">{bar}</div>'
        f'<div class="ty-chips">{chips}</div></div>'
    )


def tree_html(statuses: dict[str, str], resolved: str, rows_census: list[dict[str, int]]) -> str:
    from progress_report import esc, html_rich

    children: dict[str | None, list[Part]] = {}
    for part in PARTS:
        children.setdefault(part.parent, []).append(part)
    in_part: dict[str, list[Fragment]] = {}
    for fragment in FRAGMENTS:
        in_part.setdefault(fragment.part, []).append(fragment)

    def census_html() -> str:
        head = "".join(f"<th>{row['period']}</th>" for row in rows_census)

        def line(label: str, key: str) -> str:
            cells = "".join(f"<td>{row[key]}</td>" for row in rows_census)
            return f"<tr><th>{label}</th>{cells}</tr>"

        return (
            '<div class="table-wrap"><table class="ty-census"><thead><tr><th>period</th>'
            f"{head}</tr></thead><tbody>{line('components', 'total')}"
            f"{line('satellite', 'satellite')}{line('primitive', 'primitive')}</tbody></table></div>"
            '<p class="ty-text">The number of components of period p is the sum over d | p of '
            "μ(p/d) 2^(d−1); a component is satellite when it is attached to a component of "
            "a smaller period.</p>"
        )

    def node(part: Part) -> str:
        dim = (
            f'<span class="chip dim">dim {esc(part.dim)}</span>'
            if part.dim not in ("—", "")
            else ""
        )
        text = part.text
        if part.key == "interior":
            text += f" The grid resolves {resolved} of the envelope."
        extra = census_html() if part.key == "interior" else ""
        lean = f'<p class="ty-lean"><code>{esc(part.lean)}</code></p>' if part.lean else ""
        names = "".join(
            f'<span class="chip fr-chip">{esc(f.name)}</span>' for f in in_part.get(part.key, [])
        )
        chains = "".join(chain_html(key, statuses) for key in part.classes)
        kids = children.get(part.key, [])
        sub = '<ul class="ty-ul">' + "".join(node(kid) for kid in kids) + "</ul>" if kids else ""
        status = ""
        if part.classes:
            order = [
                statuses[name]
                for key in part.classes
                for name in next(chain for k, _, chain in CLASSES if k == key)
            ]
            status = next((s for s in ("open", "reduced", "published", "proved") if s in order), "")
        title = html_rich(part.title)
        if part.node:
            title = f'<a href="#n={esc(part.node)}">{title}</a>'
        brief = f'<div class="ty-brief">{html_rich(part.brief)}</div>' if part.brief else ""
        more = (
            '<details class="ty-more"><summary>more</summary>'
            f'<p class="ty-text">{html_rich(text)}</p>{extra}{lean}</details>'
        )
        return (
            f'<li class="ty-li"><div class="ty-node s-{status}" id="type-{esc(part.key)}">'
            f'<div class="ty-head"><b>{title}</b> {dim}{chains}</div>{brief}'
            f'<div class="ty-meta">{names}</div>{more}</div>{sub}</li>'
        )

    return '<div class="ty-tree"><ul class="ty-ul">' + node(PARTS[0]) + "</ul></div>"


def overall_html(statuses: dict[str, str]) -> str:
    """The statements of the programme by status, as one bar with a legend."""
    from progress_report import esc

    counts = {status: sum(1 for value in statuses.values() if value == status)
              for status in STATUSES}
    segments = "".join(
        f'<span class="seg {status}" style="flex:{counts[status]}" '
        f'title="{counts[status]} {esc(status)}">{counts[status]}</span>'
        for status in STATUSES
        if counts[status]
    )
    legend = "".join(
        f'<span class="lg"><span class="lm {status}">{counts[status]}</span>'
        f"{esc(STATUS_TEXT[status])}</span>"
        for status in STATUSES
    )
    return (
        f'<div class="ty-overall"><div class="ty-bar big">{segments}</div>'
        f'<div class="ty-legend">{legend}</div></div>'
    )


def regimes_html() -> str:
    from progress_report import esc

    items = "".join(
        f"<li><b>{esc(title)}</b>: {esc(text)}</li>" for title, text in REGIMES.values()
    )
    return f'<ul class="ty-regimes">{items}</ul>'


def fragments_html(statuses: dict[str, str]) -> str:
    from progress_report import esc, html_rich

    cards = []
    for fragment in FRAGMENTS:
        part = PART[fragment.part]
        regime = REGIMES.get(fragment.regime)
        chip = (
            f'<span class="chip">{esc(regime[0])}</span>'
            if regime
            else '<span class="chip">interior</span>'
        )
        mark = '<span class="mk"></span>' if fragment.mark else ""
        chains = ""
        for key in part.classes:
            chain = next(chain for k, _, chain in CLASSES if k == key)
            chains += "".join(lemma_chip(name, statuses[name]) for name in chain)
        cards.append(
            '<figure class="fr">'
            f'<div class="fr-img"><img alt="{esc(fragment.name)}" width="128" height="128" '
            f'src="{fragment_uri(fragment)}">{mark}</div>'
            f"<figcaption><b>{esc(fragment.name)}</b> {chip}"
            f"<small>{html_rich(fragment.where)}</small>"
            f'<span class="fr-type">{html_rich(part.title)}</span>'
            f'<span class="fr-chain">{chains}</span>'
            f'<span class="fr-note">{html_rich(fragment.note)}</span></figcaption></figure>'
        )
    return '<div class="fr-grid">' + "".join(cards) + "</div>"


def class_objects(class_key: str, usage: dict[str, set[str]]) -> set[str]:
    chain = next(chain for key, _, chain in CLASSES if key == class_key)
    return {obj for name in chain for obj in usage.get(name, ())}


def mastered_at(rows: list[dict[str, object]]) -> dict[str, int | None]:
    """The number of the first update whose milestones include one of the object."""
    first: dict[str, int | None] = {obj.key: None for obj in OBJECTS}
    for row in rows:
        for label in row["milestones"]:
            key = object_of_label(label)
            if key is not None and first[key] is None:
                first[key] = int(row["number"])
    return first


def milestone_totals(milestones) -> dict[str, int]:
    totals = {obj.key: 0 for obj in OBJECTS}
    for label, _, _ in milestones:
        key = object_of_label(label)
        if key is not None:
            totals[key] += 1
    return totals


def objects_html(
    repo_root: Path,
    rows: list[dict[str, object]],
    milestones,
    usage: dict[str, set[str]] | None = None,
) -> str:
    from progress_report import esc, html_rich

    counts = declaration_counts(repo_root)
    tiles = len(list((repo_root / "Mlc" / "GridTiles").glob("*.lean")))
    first = mastered_at(rows)
    class_keys = [key for key, _, _ in CLASSES]
    used = {key: class_objects(key, usage or {}) for key in class_keys}
    head = "".join(
        f'<th class="o-cls" title="{esc(title)}"><span>{esc(title.split(" (")[0])}</span></th>'
        for _, title, _ in CLASSES
    )
    body = []
    for obj in OBJECTS:
        if obj.key == "grid":
            size = f"{tiles:,} tile modules".replace(",", " ")
        else:
            size = f"{counts[obj.key]} declarations"
        if usage is not None and not any(obj.key in used[key] for key in class_keys):
            cells = (
                f'<td class="o-all" colspan="{len(class_keys)}">'
                "no statement of the programme depends on it</td>"
            )
        else:
            cells = "".join(
                f'<td class="o-cell{" on" if obj.key in used[key] else ""}"></td>'
                for key in class_keys
            )
        stamp = first[obj.key]
        body.append(
            f'<tr><td class="o-name"><b>{esc(obj.title)}</b>'
            f'<span class="sub">{html_rich(obj.picture)}</span></td>'
            f'<td class="o-size">{esc(size)}</td>'
            f'<td class="o-first">{"" if stamp is None else f"update {stamp}"}</td>{cells}</tr>'
        )
    return (
        '<div class="table-wrap"><table class="ctable otable"><thead><tr>'
        '<th>Object</th><th>Size</th><th>First</th>' + head + "</tr></thead><tbody>"
        + "".join(body) + "</tbody></table></div>"
    )


def timeline_html(rows: list[dict[str, object]], milestones) -> str:
    from progress_report import esc

    totals = milestone_totals(milestones)
    cell, gap, left, top = 15, 2, 190, 18
    width = left + len(rows) * (cell + gap) + 8
    height = top + len(OBJECTS) * (cell + gap) + 6
    parts = [
        f'<svg class="tl" viewBox="0 0 {width} {height}" role="img" '
        f'aria-label="Milestones of every object by update" preserveAspectRatio="xMinYMin meet">'
    ]
    for number in range(0, len(rows), 5):
        x = left + number * (cell + gap) + cell / 2
        parts.append(f'<text class="tl-x" x="{x:.1f}" y="11" text-anchor="middle">{number}</text>')
    for r, obj in enumerate(OBJECTS):
        y = top + r * (cell + gap)
        parts.append(f'<text class="tl-y" x="{left - 8}" y="{y + cell - 3}" text-anchor="end">'
                     f"{esc(obj.title)}</text>")
        previous = 0
        for c, row in enumerate(rows):
            have = sum(1 for label in row["milestones"] if object_of_label(label) == obj.key)
            x = left + c * (cell + gap)
            share = have / totals[obj.key] if totals[obj.key] else 0.0
            step = " step" if have > previous else ""
            previous = have
            tip = (f"Update {row['number']}: {have} of {totals[obj.key]} milestones of "
                   f"{obj.title}")
            style = f"fill-opacity:{0.12 + 0.88 * share:.2f}" if have else ""
            parts.append(
                f'<rect class="tl-c{" on" if have else ""}{step}" x="{x}" y="{y}" '
                f'width="{cell}" height="{cell}" rx="3" style="{style}">'
                f"<title>{esc(tip)}</title></rect>"
            )
    parts.append("</svg>")
    return "".join(parts)


def ladder_html() -> str:
    from progress_report import esc

    rungs = (
        (
            "2",
            "the wild part of ∂M",
            "ShishikuraDimension.dimH_wildPart_eq_two (Lean, from Shishikura's theorem)",
            "also of dimension 2: the interior of M (it has area) and the plane",
        ),
        (
            "1",
            "the skeleton: the boundaries of the hyperbolic components, countably many analytic "
            "curves (cusps at the roots of primitive components)",
            "dimH_iUnion_range_le_one (Lean)",
            "also of dimension 1: the circle of external angles and the interval of a Peano "
            "parametrization; a parametrization of ∂M by an interval is at best 1/2-Hölder "
            "(Lean: ShishikuraDimension.holder_exponent_le_half)",
        ),
        (
            "0",
            "parabolic parameters, Misiurewicz parameters and centres: countable sets",
            "Set.Countable.dimH_zero (Mathlib)",
            "also of dimension 0: the finite sets",
        ),
    )
    items = "".join(
        f'<div class="rung"><div class="rung-dim"><b>{esc(dim)}</b></div>'
        f'<div class="rung-body"><div><b>{esc(boundary)}</b><small>{esc(lean)}</small></div>'
        f'<div class="rung-other">{esc(other)}</div></div></div>'
        for dim, boundary, lean, other in rungs
    )
    return f'<div class="ladder"><div class="ladder-axis">Hausdorff dimension</div>{items}</div>'


def types_cards_html(repo_root: Path, rows: list[dict[str, object]], lean_text: str,
                     milestones, resolved: str,
                     usage: dict[str, set[str]] | None = None) -> str:
    """The cards of the page, to follow the table of the updates."""
    from progress_report import html_rich

    statuses = lemma_statuses(lean_text)
    summary = html_rich(
        f"The programme has {len(statuses)} statements. A statement is proved when a Lean "
        "theorem proves it, reduced when a Lean theorem derives it from a geometric statement "
        "about the level sets (which is itself open), literature-motivated when a theorem of "
        "the literature suggests it and the development takes it as a hypothesis, and open "
        "otherwise. The dictionary (which parameter has which class and tower) is a parameter "
        "of every statement, so a literature-motivated statement is a hypothesis about the "
        "dictionary; the bridge from the published theorem to this formal statement is not "
        "formalized."
    )
    if usage is None:
        usage_note = (
            "The dependency data is unavailable in this build, so no class is marked."
        )
    else:
        usage_note = (
            "A dot marks that the object holds a declaration on which a statement of the class, "
            "or the Lean theorem that reduces it, depends (computed from the dependency graph "
            "of the Lean declarations). An object without a dot lies downstream of the "
            "statements (it uses their conclusions, as the Yoccoz criterion does) or is a "
            "result on its own."
        )
    return (
        '<section class="p-card p-types"><h2>Types of parameters · how M and its boundary are '
        "assembled</h2>"
        f'<p class="p-foot ty-lead">{summary} The colour of a leaf is the weakest status in '
        "the chain of statements that its class needs; a class is closed when all of them are "
        "proved. A chip links to the statement in the proof spine.</p>"
        + overall_html(statuses)
        + tree_html(statuses, resolved, census(10))
        + '<p class="p-foot">The skeleton and the wild part split the boundary by dimension, '
        "and the classes split it by the renormalization of the parameter; the two splittings "
        "cross (the parabolic parameters belong to the class of the finitely renormalizable "
        "parameters, and the irrationally indifferent parameters form the class neutral). "
        "For every dictionary some class has dimension 2: a statement about the finite "
        "partition, true even for a dictionary that labels the whole boundary neutral. For the "
        "intended dictionary the class neutral lies in the skeleton, of dimension at most 1, so "
        "other classes carry the dimension, and the formalization does not say which.</p>"
        "</section>"
        '<section class="p-card p-frag"><h2>Characteristic fragments of M · the existing '
        "typing</h2>"
        '<p class="p-foot ty-lead">The names are informal and local. Each fragment is placed in '
        "the hierarchy and in one of the three regimes of the survey (§3, after Question 3.1) "
        "at the scale of its window, and the statements below it are those that its type "
        "needs. The matching is a reading of the survey. Numerical renderings: an "
        "illustration that the Lean proof does not use.</p>"
        + regimes_html()
        + fragments_html(statuses)
        + "</section>"
        '<section class="p-card p-objects"><h2>New objects · what the formalization adds</h2>'
        '<p class="p-foot ty-lead">The types above are local; the objects below act across '
        f"scales. {usage_note} Beneath the table, each row of the timeline is an object and "
        "each column an update; a filled square counts the milestones that the object has "
        "reached by then, and a dark outline marks an update that added one.</p>"
        + objects_html(repo_root, rows, milestones, usage)
        + '<div class="tl-wrap">'
        + timeline_html(rows, milestones)
        + "</div></section>"
        '<section class="p-card p-ladder"><h2>Dimension ladder</h2>'
        '<p class="p-foot ty-lead">The loops with which the moduli are measured have dimension at '
        "most 1, and the boundary of M has dimension 2. The extra dimension lies in the wild "
        "part, which no countable family of smooth curves removes. The grid bounds the area of "
        "the boundary and does not change the set.</p>" + ladder_html() + "</section>"
    )


# ---------------------------------------------------------------------------------------------
# TeX.
# ---------------------------------------------------------------------------------------------


def types_tex(lean_text: str) -> str:
    """The rows of the table of the classes: the chain with the status of every statement."""
    from progress_report import tex_escape

    statuses = lemma_statuses(lean_text)
    letter = {"proved": "P", "reduced": "R", "published": "L", "open": "O"}
    lines = []
    for key, title, chain in CLASSES:
        codes = ", ".join(f"{lemma_code(name)}\\,({letter[statuses[name]]})" for name in chain)
        counts = [sum(1 for name in chain if statuses[name] == status) for status in STATUSES]
        lines.append(
            " & ".join(
                [tex_escape(title), codes.replace("′", "$'$")] + [str(n) for n in counts]
            )
            + r" \\"
        )
    return "\n".join(lines) + "\n"


def types_table_tex(lean_text: str) -> str:
    """The whole `tabularx` environment of the table of the classes: the rows are not read
    when an `\\input` stands inside the environment (LaTeX reports a misplaced `\\noalign`)."""
    return (
        r"\begin{tabularx}{\linewidth}{@{}>{\raggedright\arraybackslash}p{38mm}"
        r">{\raggedright\arraybackslash}Xcccc@{}}" "\n"
        r"\toprule" "\n"
        r"Class & Chain of statements & P & R & L & O \\" "\n"
        r"\midrule" "\n"
        + types_tex(lean_text)
        + r"\bottomrule" "\n"
        r"\end{tabularx}" "\n"
    )
