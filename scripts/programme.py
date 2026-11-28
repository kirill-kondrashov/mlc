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
SHARPNESS_ROOT = "MLC.Research.WidthTower.uniformities_necessary"
GROTZSCH_ROOT = "MLC.Research.extWidth_ge_of_series"
PARALLEL_ROOT = "MLC.Research.extWidth_parallel_finset"
PULLBACK_ROOT = "MLC.Research.extWidth_pullback_le"
# The results of Mlc/Research/TailInvariance.lean that no other result uses.
TAIL_ROOTS = (
    "MLC.Research.WidthTower.lemmas_shift_iff",
    "MLC.Research.WidthTower.aPrioriBounds_of_shift_tails",
    "MLC.Research.WidthTower.shift_shift",
)
# The results of Mlc/Research/AnnulusModulus.lean that no other result uses.
ANNULUS_ROOTS = (
    "MLC.Research.extLength_radialFamily_mul_circleFamily",
    "MLC.Research.extLength_circleFamily_eq_extWidth_radialFamily",
    "MLC.Research.extLength_radialFamily_add_le",
)
# The results of Mlc/Research/RectangleModulus.lean that no other result uses.
RECTANGLE_ROOTS = (
    "MLC.Research.extWidth_horizFamily",
)
# The results of Mlc/Research/NestModulus.lean, PhaseParameter.lean and DivergentNest.lean
# that no other result uses.
NEST_ROOTS = (
    "MLC.Research.Geometry.transfer_iff_phaseParameter",
    "MLC.Research.nonempty_parameterRealization_concentric",
    "MLC.Research.ConnectedNest.sum_extWidth_loops_le_coarse",
    "MLC.Research.extWidth_loopFamily_round",
)
# The results of Mlc/Research/AreaMultiplicity.lean that no other result uses.
MULTIPLICITY_ROOTS = (
    "MLC.Research.extWidth_le_pow_two_mul_fc_iterate_of_loops",
)
# The results of Mlc/Research/VirtualShrinking.lean that no other result uses.
VIRTUAL_SHRINKING_ROOTS = (
    "MLC.Research.Geometry.virtualTransfer_hulls_shrink",
)
# The results of Mlc/Research/QuasiInvariance.lean that no other result uses.
QUASI_INVARIANCE_ROOTS = (
    "MLC.Research.ConnectedNest.DivergentModuli.map",
    "MLC.Research.QcEmbedding.of_holomorphic",
)
# The results of Mlc/Research/Collar.lean that no other result uses.
COLLAR_ROOTS = (
    "MLC.Research.ConnectedNest.divergentModuli_of_collars",
    "MLC.Research.ConnectedNest.closure_piece_subset_closedBall_of_collars",
)
# The results of Mlc/Research/LevelTower.lean that no other result uses.
LEVEL_JUMP_ROOTS = (
    "MLC.Research.LevelTower.aPrioriBounds_of_collars",
    "MLC.Research.LevelTower.width_eq_of_round",
)
LEVEL_TRANSFER_ROOTS = (
    "MLC.Research.Geometry.transfer_of_comparison",
)
# The results of Mlc/Research/Dimension.lean that no other result uses.
DIMENSION_ROOTS = (
    "MLC.Research.ShishikuraDimension.holder_exponent_le_half",
    "MLC.Research.ShishikuraDimension.not_subset_iUnion_range",
    "MLC.Research.ShishikuraDimension.two_le_dimH_of_image",
    "MLC.Research.ConnectedNest.dimH_kernel_eq_zero_of_divergent",
    "MLC.Research.ConnectedNest.sum_extWidth_loops_bounded_of_dimH_kernel_pos",
)
# The results of Mlc/Research/PeanoObject.lean that no other result uses.
PEANO_ROOTS = (
    "MLC.Research.mlc_iff_lamination",
    "MLC.Research.ShishikuraDimension.holder_exponent_le_half_of_epi",
)
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
        "teichmuller",
        f"{GEOMETRY}.TeichmullerContraction",
        "Lemma TC · Teichmüller contraction",
        "§4.3 · bounded type",
        "published",
        "§4.3, 'Alternative (ii) is prevented by the Teichmüller contraction'; "
        "Dudko–Lyubich, arXiv:2309.02107, Proposition 2.7 (W(Y_n ∖ X_n) = O(Δ_P^n))",
        "For the tower of a parameter of bounded type, the degeneration grows from a level to "
        "the next by at most a factor Δ_P that depends on the bound P of the relative period "
        "of the level. It excludes a jump by C_δ. The sources state it for towers of "
        "relative periods bounded by P. Published; not formalized.",
    ),
    Lemma(
        "boundedType",
        f"{GEOMETRY}.BoundedTypeInputs",
        "Lemma B · bounded type",
        "Theorem 4.1 · dichotomy (4.6)",
        "published",
        "Theorem 4.1 (Dudko–Lyubich, MLC at Feigenbaum points; Kahn for the primitive "
        "levels); (4.1), (4.6)",
        "At a parameter of bounded type the dichotomy (4.6) holds with an error that depends "
        "on the period; with the Teichmüller contraction the a priori bounds follow "
        "(WidthTower.aPrioriBounds_of_bounded). Published; not formalized.",
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
        "quadraticGrowth",
        f"{GEOMETRY}.QuadraticGrowth",
        "Lemma QG · quadratic growth",
        "Cheraghi–Shishikura · Theorem D",
        "published",
        "Cheraghi–Shishikura, Satellite renormalization of quadratic polynomials, "
        "arXiv:1509.07843, Theorem D (a preprint of 2015); Levin proves rigidity under a "
        "faster growth of the denominators",
        "At the parameters of satellite type whose type sequence is in the class QG_N "
        "(b₁,₁ ≥ N, b_{i,j+1} ≥ b_{i,j}², b_{i+1,1} ≥ q_i²; for example p_i = ±1, q_1 ≥ N, "
        "q_{i+1} ≥ q_i²) the pieces M(⟨p_i/q_i⟩_{i ≤ n}) have diameter at most Cλⁿ and M is "
        "locally connected. The proof uses near-parabolic renormalization; these parameters "
        "lack quadratic-like a priori bounds. Published; not formalized.",
    ),
    Lemma(
        "unboundedTeichmuller",
        f"{GEOMETRY}.UnboundedTeichmuller",
        "Lemma TC′ · pseudo-Siegel contraction",
        "Problem 4.3",
        "problem43",
        "§4.3 with §4.4; proposed reading",
        "At a parameter of unbounded satellite type outside the quadratic growth class, the "
        "pseudo-Siegel degeneration of the levels grows from a level to the next by at most "
        "a factor Δ_P that depends on the bound P of the relative period of the level: "
        "Lemma TC for the pseudo-Siegel degeneration. At the levels whose rotation number "
        "is away from 0 there is no regularization, so the published contraction applies "
        "there.",
    ),
    Lemma(
        "unboundedJumpCap",
        f"{GEOMETRY}.UnboundedJumpCap",
        "Lemma G · jump cap",
        "Problem 4.3",
        "problem43",
        "§4.3 (alternative (ii)) and §4.4 (pseudo-Siegel disks consume the invariant "
        "degeneration); proposed reading",
        "At a parameter of unbounded satellite type, a jump of the pseudo-Siegel "
        "degeneration by a fixed factor C₀ at a level of large relative period lands below "
        "a fixed ceiling B₀: the invariant degeneration that alternative (ii) amplifies is "
        "absorbed by the pseudo-Siegel disks. The quadratic-like degeneration itself is "
        "unbounded in some of these classes (Sørensen; Cheraghi–Shishikura). With a linear "
        "dichotomy the cap is equivalent to the a priori bounds "
        "(WidthTower.aPrioriBounds_iff_jumpCap), and it is weaker than a uniform growth "
        "bound.",
    ),
    Lemma(
        "unboundedDichotomy",
        f"{GEOMETRY}.UnboundedDichotomy",
        "Lemma D · linear dichotomy",
        "Problem 4.3",
        "problem43",
        "§4.2–§4.3, the additive error O_p(1); Kahn–Lyubich, arXiv:2601.21905, Theorem 3.9 "
        "(linear topological error); proposed reading",
        "At a parameter of unbounded satellite type the dichotomy (4.6) holds for the "
        "pseudo-Siegel degeneration with an additive error at most linear in the period: "
        "the amplification holds, or the degeneration jumps by C_δ. The published constants "
        "depend on the period implicitly, without a rate; a decomposition with a linear "
        "topological error is known, but it is not the dynamical dichotomy.",
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
        "both virtual subcases",
        "problem44",
        "§4.5 with §4.3; proposed reading",
        "The Teichmüller contraction holds for the virtual levels.",
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
        "virtualJumpCap",
        f"{GEOMETRY}.VirtualJumpCap",
        "Lemma VG2 · virtual jump cap",
        "virtual near-neutral",
        "problem44",
        "§4.5 with §4.4; proposed reading",
        "At the virtual levels of the near-neutral subcase, a jump of the degeneration by a "
        "fixed factor at a level of large relative period lands below a fixed ceiling: the "
        "virtual version of Lemma G.",
    ),
    Lemma(
        "virtualLinearDichotomy",
        f"{GEOMETRY}.VirtualLinearDichotomy",
        "Lemma VD2 · virtual linear dichotomy",
        "virtual near-neutral",
        "problem44",
        "§4.5 with §4.4; proposed reading",
        "The dichotomy (4.6) holds for the virtual levels of the near-neutral subcase with "
        "an additive error at most linear in the period.",
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
    ("boundedType", "Bounded type", ("teichmuller", "boundedType", "transfer")),
    ("antiMolecule", "Anti-Molecule", ("antiMolecule", "transfer")),
    ("quadraticGrowth", "Quadratic growth (Cheraghi–Shishikura)", ("quadraticGrowth",)),
    ("unboundedSatellite", "Unbounded satellite (Problem 4.3)",
     ("unboundedTeichmuller", "unboundedJumpCap", "unboundedDichotomy", "transfer")),
    ("virtualBounded", "Virtual bounded type (Problem 4.4)",
     ("virtualJulia", "virtualTeichmuller", "virtualDichotomy", "virtualTransfer")),
    ("virtualNearNeutral", "Virtual near-neutral (Problem 4.4)",
     ("virtualJulia", "virtualTeichmuller", "virtualJumpCap", "virtualLinearDichotomy",
      "virtualTransfer")),
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
        "relative period (the satellite analogue of (4.7); Theorem 4.2 is the neutral case, "
        "the model situation). Proposed; not formalized.",
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
        "The degeneration along combinatorially invariant rectangles, which alternative (ii) "
        "amplifies at deeper levels (Figure 13 and (4.6)), is absorbed by the pseudo-Siegel "
        "disks: in a jump the deeper degeneration is bounded by their uniform "
        "quasiconformal geometry. This gives Lemma G, and with the Wave Lemma Lemma D. "
        "The estimate W(G \\ G′) ≥ δ⁻¹ W(G) itself, from the series law, is proved in Lean "
        "(extWidth_ge_of_series), and so is the passage from the quasiconformal geometry to "
        "the cap: collars of bounded dilatation and definite modulus at the levels that "
        "follow a jump cap the jumps (LevelTower.jumpCap_of_collars). That the pseudo-Siegel "
        "disks give such collars is the proposed content; not formalized.",
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
