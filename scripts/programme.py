"""The programme of Dudko's Problems 4.3 and 4.4 as a tree of lemmas.

`Mlc/ProgrammeRoot.lean` states the lemmas as the fields of one structure,
`MLC.Research.ProgrammeInput`, and proves in Lean that they imply `RootInput`. This
module is the catalogue of the lemmas for the dependency graph and the progress report:
the parameter classes, the lemmas that each class needs, their sources and their status.
A lemma is proved when the theorem named in `proof` exists in the Lean sources; until then
it is open, a field of the structure.

The classes and the weights are research-management priors, frozen between progress
baselines. The weights are equal: no class is claimed to be larger than another. A class
is certified by the proofs of all its lemmas; the proof of one lemma already reduces the
uncertainty of every class that needs it, by its share of the class.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

PROGRAMME_ROOT = "MLC.mlc_of_programme"
STRUCTURE = "structure Research.ProgrammeInput"
GEOMETRY = "MLC.Research.Geometry"


@dataclass(frozen=True)
class Lemma:
    key: str  # the field of ProgrammeInput
    lean: str  # the Lean definition that states the lemma
    title: str
    sub: str
    kind: str  # shared | published | problem43 | problem44
    source: str
    text: str
    proof: str = ""  # the theorem that proves the lemma, once there is one


LEMMAS: tuple[Lemma, ...] = (
    Lemma(
        "transfer",
        f"{GEOMETRY}.Transfer",
        "Lemma T · transfer",
        "a priori bounds ⇒ parameter nest",
        "shared",
        "Kahn–Lyubich quasi-additivity law; Lyubich, phase–parameter relation (§3.9, §4.1–§4.3)",
        "A bound on the degeneration of the levels of the tower of c gives a connected "
        "parameter nest with the separation estimate of the canonical return budget, so "
        "that the pieces shrink to c. This is the step from a priori bounds to local "
        "connectivity; the classes with a tower share it.",
    ),
    Lemma(
        "yoccoz",
        f"{GEOMETRY}.Yoccoz",
        "Lemma Y · finite renormalization",
        "Yoccoz, Hubbard",
        "published",
        "Yoccoz; Hubbard; Milnor (reduction (2.1) of §2)",
        "At the parameters that are not infinitely quadratic-like renormalizable, M is "
        "locally connected. Published; not formalized.",
    ),
    Lemma(
        "boundedType",
        f"{GEOMETRY}.BoundedTypeInputs",
        "Lemma B · bounded type",
        "Theorem 4.1 inputs",
        "published",
        "Theorem 4.1 (Dudko–Lyubich, MLC at Feigenbaum points; Kahn for the primitive "
        "levels); (4.1), (4.6)",
        "For bounded relative periods the Teichmüller contraction and the dichotomy (4.6) "
        "hold; the a priori bounds follow (WidthTower.aPrioriBounds_of_bounded). "
        "Published; not formalized.",
    ),
    Lemma(
        "antiMolecule",
        f"{GEOMETRY}.AntiMoleculeInputs",
        "Lemma A · anti-Molecule",
        "amplification (4.3), (4.5)",
        "published",
        "Kahn–Lyubich: Covering Lemma and Quasi-Additivity Law (§4.1–§4.2)",
        "The amplification W(f) ⪰ p W(f_n) − O(1) holds for the tower of a parameter whose "
        "primitive levels are far from the Molecule. Published; not formalized.",
    ),
    Lemma(
        "neutral",
        f"{GEOMETRY}.Neutral",
        "Lemma N · neutral",
        "Theorem 4.2",
        "published",
        "Theorem 4.2 (Dudko–Lyubich, uniform a priori bounds for neutral renormalization) "
        "and the sectorial bounds of §3.4",
        "At the neutral parameters M is locally connected. Published as pseudo-Siegel a "
        "priori bounds; not formalized.",
    ),
    Lemma(
        "unboundedGrowth",
        f"{GEOMETRY}.UnboundedGrowth",
        "Lemma G · uniform growth",
        "Problem 4.3",
        "problem43",
        "§4.3 (Teichmüller contraction) and §4.4 (pseudo-Siegel disks); proposed reading",
        "At a parameter of unbounded satellite type the degeneration grows by at most a "
        "fixed factor from a level to the next, however large the relative period of the "
        "satellite level is. The proof of Theorem 4.1 uses a factor that grows "
        "exponentially with the period.",
    ),
    Lemma(
        "unboundedDichotomy",
        f"{GEOMETRY}.UnboundedDichotomy",
        "Lemma D · uniform dichotomy",
        "Problem 4.3",
        "problem43",
        "§4.2–§4.3, the additive error O_p(1); proposed reading",
        "At a parameter of unbounded satellite type the dichotomy (4.6) holds with an "
        "additive error that does not depend on the period: the amplification holds, or "
        "the degeneration jumps by C_δ.",
    ),
    Lemma(
        "virtualJulia",
        f"{GEOMETRY}.VirtualJulia",
        "Lemma VJ · virtual Julia set",
        "Problem 4.4",
        "problem44",
        "§4.5, partially invariant virtual Julia sets (Dudko–Kahn–Lyubich)",
        "A parameter of the virtual Molecule has a connected hull of the Cantor small Julia "
        "sets inside J_c that contains the critical orbit up to a finite number of first "
        "returns and is partially invariant.",
    ),
    Lemma(
        "virtualTeichmuller",
        f"{GEOMETRY}.VirtualTeichmuller",
        "Lemma VT1 · virtual Teichmüller",
        "virtual bounded type",
        "problem44",
        "§4.5 with §4.3; proposed reading",
        "The Teichmüller contraction holds for the virtual levels of bounded relative "
        "periods.",
    ),
    Lemma(
        "virtualDichotomy",
        f"{GEOMETRY}.VirtualDichotomy",
        "Lemma VD1 · virtual dichotomy",
        "virtual bounded type",
        "problem44",
        "§4.5 with §4.3; proposed reading",
        "The dichotomy (4.6) holds for the virtual levels of bounded relative periods.",
    ),
    Lemma(
        "virtualGrowth",
        f"{GEOMETRY}.VirtualGrowth",
        "Lemma VG2 · virtual growth",
        "virtual near-neutral",
        "problem44",
        "§4.5 with §4.4; proposed reading",
        "The degeneration of the virtual levels of the near-neutral subcase grows by at "
        "most a fixed factor from a level to the next.",
    ),
    Lemma(
        "virtualUniformDichotomy",
        f"{GEOMETRY}.VirtualUniformDichotomy",
        "Lemma VD2 · virtual uniform dichotomy",
        "virtual near-neutral",
        "problem44",
        "§4.5 with §4.4; proposed reading",
        "The dichotomy (4.6) holds for the virtual levels of the near-neutral subcase with "
        "an additive error that does not depend on the period.",
    ),
    Lemma(
        "virtualTransfer",
        f"{GEOMETRY}.VirtualTransfer",
        "Lemma VT · virtual transfer",
        "Problem 4.4",
        "problem44",
        "§4.5, phase–parameter transfer for virtual hulls",
        "A bound on the degeneration of the virtual levels gives a connected parameter nest, "
        "a phase–parameter chart into the virtual hulls, and the dynamical separation "
        "estimate of the canonical budget.",
    ),
)

# The classes of boundary parameters and the lemmas that each needs; the weights are equal.
CLASSES: tuple[tuple[str, str, tuple[str, ...]], ...] = (
    ("finite", "Not infinitely renormalizable", ("yoccoz",)),
    ("neutral", "Neutral", ("neutral",)),
    ("boundedType", "Bounded type", ("boundedType", "transfer")),
    ("antiMolecule", "Anti-Molecule", ("antiMolecule", "transfer")),
    ("unboundedSatellite", "Unbounded satellite (Problem 4.3)",
     ("unboundedGrowth", "unboundedDichotomy", "transfer")),
    ("virtualBounded", "Virtual bounded type (Problem 4.4)",
     ("virtualJulia", "virtualTeichmuller", "virtualDichotomy", "virtualTransfer")),
    ("virtualNearNeutral", "Virtual near-neutral (Problem 4.4)",
     ("virtualJulia", "virtualGrowth", "virtualUniformDichotomy", "virtualTransfer")),
)

LEMMA = {lemma.key: lemma for lemma in LEMMAS}

# The sub-steps through which Lemmas G and D are expected to be proved: not formalized.
PSEUDO_SIEGEL = (
    (
        "ps1",
        "PS1 · pseudo-Siegel disks",
        "satellite levels of large period",
        "Nested pseudo-Siegel disks Z^[m], almost invariant up to q^[m+1] iterations, with "
        "Z^(-1), Z^0 uniformly quasiconformal, exist at the satellite levels of large "
        "relative period (the satellite analogue of (4.7); Theorem 4.2 is the neutral case). "
        "Proposed; not formalized.",
    ),
    (
        "ps2",
        "PS2 · non-invariance error",
        "geometric series",
        "The non-invariance error of Z^[m] is bounded by a geometric series, because the "
        "antirenormalization relative to β is contracting (Dudko §4.4, right loop of "
        "Figure 14). Proposed; not formalized.",
    ),
    (
        "ps3",
        "PS3 · fjord and dam",
        "regularization of Z^0",
        "Z^(-1) is obtained from Z^0 by adding a parabolic fjord bounded by a dam inside an "
        "invariant rectangle (Figure 14, left loop). Proposed; not formalized.",
    ),
    (
        "ps4",
        "PS4 · invariant degeneration",
        "W(G \\ G′) ≥ C_δ W(G)",
        "The degeneration along combinatorially invariant rectangles is absorbed by the "
        "pseudo-Siegel disks (Figure 13 and (4.6)); together with the Wave Lemma it gives "
        "Lemmas G and D. Proposed; not formalized.",
    ),
)

_FIELD = re.compile(r"^\s{2}(\w+)\s*:\s*G\.\w+\s*$", re.MULTILINE)


def open_lemmas(lean_text: str) -> list[str]:
    """The lemmas that are still fields of `ProgrammeInput`, in the order of the source."""
    start = lean_text.find(STRUCTURE)
    if start < 0:
        return []
    block = lean_text[start:]
    end = block.find("\nnamespace")
    block = block[: end if end > 0 else len(block)]
    return [name for name in _FIELD.findall(block) if name in LEMMA]


def proved_lemmas(lean_text: str) -> set[str]:
    """The lemmas whose proving theorem exists in the sources."""
    return {
        lemma.key
        for lemma in LEMMAS
        if lemma.proof
        and re.search(rf"^\s*theorem\s+{re.escape(lemma.proof)}\b", lean_text, re.MULTILINE)
    }


def class_shares(proved: set[str]) -> dict[str, float]:
    """For every class, the share of its lemmas that are proved."""
    return {
        key: sum(1 for lemma in lemmas if lemma in proved) / len(lemmas)
        for key, _, lemmas in CLASSES
    }


def classes_share(lean_text: str) -> float:
    """The weight of the classes with a Lean certificate, with partial credit for a class
    whose lemmas are partly proved. Zero until the programme exists in the sources."""
    if STRUCTURE not in lean_text:
        return 0.0
    shares = class_shares(proved_lemmas(lean_text))
    return sum(shares.values()) / len(CLASSES)


def check_catalogue(lean_text: str) -> list[str]:
    """Problems of the catalogue against the sources: a lemma is a field or is proved."""
    fields = open_lemmas(lean_text)
    proved = proved_lemmas(lean_text)
    issues = []
    for lemma in LEMMAS:
        if lemma.key in proved and lemma.key in fields:
            issues.append(f"{lemma.key} is proved but is still a field of ProgrammeInput")
        if lemma.key not in proved and lemma.key not in fields:
            issues.append(f"{lemma.key} is neither a field of ProgrammeInput nor proved")
    for name in fields:
        if name not in LEMMA:
            issues.append(f"field {name} of ProgrammeInput is not in the catalogue")
    return issues
