# A sound replacement for the Green-intersection axiom

**The existing axiom cannot be discharged: its proposition is false.** The
mathematically correct revision is to retire that axiom, not to find a new
proof of it. This proposal gives a replacement parameter-neighborhood
interface, complete proofs of its topological reductions, and Lean
implementations of those reductions. It explicitly identifies the new
mathematical input that is still needed; it does **not** claim an unconditional
proof of Mandelbrot local connectedness.

Reviewed against commit `adacab1f4f5a8fd6d2ee5fce79684b864abbdfd6`, with the
repository's Lean 4.28.0 / Mathlib v4.28.0 toolchain, on 2026-09-11.
This is a proposal: no existing Lean declaration has been changed.

## 1. What the counterexample actually rules out

Write

\[
A_n(c)=\{p\in\mathbb C:G_c(p-c)<2^{-n}\},\qquad
T_n(c)=A_n(c)\cap M.
\]

The declaration in
[`ParaPuzzleConnectivity.lean`](../Mlc/ParaPuzzleConnectivity.lean#L201)
asserts

\[
\forall c\in M\;\forall n,\qquad
A_n(c)\not\subseteq M\ \Longrightarrow\ \operatorname{IsConnected}(T_n(c)).
\tag{GI}
\]

This is the exact content of
`GreenSublevelIntersectionCategoricalData`, not an informal interpretation.
The existing theorem `greenSublevelIntersectionCategoricalData_iff` proves
the equivalence without using the axiom. The over-category pullback has image
exactly \(A_n(c)\cap M\).

### 1.1 The supplied counterexample applies unchanged

The [counterexample document](green_sublevel_intersection_categorical_counterexample.md)
uses \(c=i\), \(n=16\), and \(b=45/64\). Its argument establishes

\[
i\in M,\qquad
0,i\in T_{16}(i),\qquad
2i\in A_{16}(i)\setminus M,
\]

and

\[
p\in M,\quad \operatorname{Im}p=b
\quad\Longrightarrow\quad G_i(p-i)>2^{-16}.
\tag{1}
\]

The orbit identities, the translation \(p-i\), and the normalization
\(2^{-m}\log\max(1,|f_i^m(z)|)\) agree with the code.
In particular, \(2i\), rather than a hypothetical exterior point, supplies
the non-factorization witness required by the axiom.

The numerical ingredient proves a statement about **every real point** of
the line segment, not a sampled picture. For each \(x\in[-2,2]\), with
\(p=x+bi\), it certifies either

\[
\exists\,1\le k\le16:\ |f_p^k(0)|>2,
\quad\text{or}\quad
\exists\,1\le k\le15:\ |f_i^k(p-i)|>4.
\tag{2}
\]

The first alternative is impossible for \(p\in M\). The second implies
\(G_i(p-i)>2^{-(k+1)}\ge2^{-16}\), by the Green functional equation and
the strict lower bound \(G_i(w)>1/2\) for \(|w|>4\).
The 298 adjacent closed interval enclosures cover the entire relevant
segment, including all endpoints. Integer division by the positive scale
implements the outward floor rounding used in the prose proof.

Equation (1) separates \(T_{16}(i)\) into its nonempty intersections with
the two open half-planes \(\operatorname{Im}p<b\) and
\(\operatorname{Im}p>b\). This disproves connectedness itself; no
path-connectedness assumption is being made.

**Formalization status matters.** The arithmetic block in Appendix A and
the two analytic/topological helpers in Appendix B of the counterexample
elaborate with the current toolchain. The arithmetic certificate has no
axioms; those helpers use only the standard Lean foundations. The complete
Lean theorem `¬ GreenSublevelIntersectionCategoricalData` still requires
the interval-soundness and assembly work described in that document.
The distinction is between a complete mathematical counterexample and its
not-yet-complete Lean formalization, not between a counterexample and an
unexplained numerical conjecture.

### 1.2 Passing to deeper levels does not repair the statement

In fact, the same counterexample works for **every \(n\ge16\)**:
\(A_n(i)\subseteq A_{16}(i)\), so the separating line is still absent;
the Green-zero orbit witnesses put \(0,i\) in \(T_n(i)\) and \(2i\) in
\(A_n(i)\setminus M\) at every level.

Thus neither "for all sufficiently large \(n\)" nor "along a cofinal
subsequence of depths" repairs (GI) with the present sets.

Nor can the existing categorical alternatives repair it. The
finite-etale \(K_0\) restriction/excision conditions in
[`EfimovCategoricalBridge.lean`](../Mlc/EfimovCategoricalBridge.lean)
are proved equivalent to (GI), hence are also false as universal assertions.
A continuous surjection from connected \(A_{16}(i)\) onto disconnected
\(T_{16}(i)\) cannot exist. Consequently the universal
Douady--Hubbard/Yoccoz carving datum, and its stronger holomorphic version,
cannot be instantiated for these definitions.

These observations do not refute any classical parameter-puzzle theorem:
the frozen translated full Green sublevels are different sets.

## 2. Coupled defects in the present root interface

Changing only the connectedness statement would leave two independent
obstructions in the shrink-based root assembly.

### 2.1 The frozen tower never shrinks to its center on \(M\)

The proved identity is

\[
\bigcap_n A_n(c)=c+K_c.
\]

There is always a nonzero point of \(K_c\) when \(c\in M\).
If \(c\ne0\), the point \(c=f_c(0)\) has a bounded orbit because its orbit
is a tail of the critical orbit. If \(c=0\), the point \(1\) is fixed.
Therefore

\[
c\in M\quad\Longrightarrow\quad
\bigcap_n A_n(c)\ne\{c\}.
\tag{3}
\]

Since `paraPuzzlePieceAt_eq_green_translate` identifies the current
`ParaPuzzlePieceAt` with \(A_n(c)\) for \(c\in M\), (3) also proves

\[
\bigcap_n\operatorname{ParaPuzzlePieceAt}(c,n)\ne\{c\}.
\]

Appendix B contains Lean proofs of these stronger, universal
non-shrinking statements. Accordingly, the two shrink-based branches in
[`CategoricalRoot.lean`](../Mlc/CategoricalRoot.lean#L61)
use hypotheses that cannot hold on \(M\) with these pieces. The conditional
shrink lemmas can be formally correct while their proposed geometric
interpretation is unusable.

Even replacing \(T_n(c)\) by its component containing \(c\), without any
spatial localization, does not fix shrinking. At \(c=0\), the real segment
\(J=[0,1/4]\) lies in \(M\cap K_0\). Indeed, for a real parameter
\(t\in[0,1/4]\), the interval \([0,1/2]\) is forward invariant under
\(x\mapsto x^2+t\), so the critical orbit is bounded. Also
\(t\in K_0\), since repeated squaring stays in \([0,1]\).
Thus \(J\subseteq T_n(0)\) at every level. Being connected and containing
zero, \(J\) lies in the component of \(T_n(0)\) containing zero.
Those components have diameter at least \(1/4\).

### 2.2 The imported "modulus" is not conformal modulus

The pinned dependency
`.lake/packages/yoccoz-theorem/Yoccoz/Quadratic/Complex/Groetzsch.lean`
defines

\[
\operatorname{modulus}(E)=\int_E e^{-|z|^2}\,dA(z).
\tag{4}
\]

This is Gaussian weighted area. For any decreasing measurable sequence
\(P_n\), the differences \(P_n\setminus P_{n+1}\) are pairwise disjoint,
and therefore

\[
0\le
\sum_{n<N}\operatorname{modulus}(P_n\setminus P_{n+1})
\le \int_{\mathbb C}e^{-|z|^2}\,dA(z)<\infty.
\]

The nonnegative series always converges. Applied to the actual puzzle
pieces, this gives

\[
\forall c\in\mathbb C,\qquad
\operatorname{Summable}
  \bigl(n\mapsto\operatorname{modulus}(\operatorname{PuzzleAnnulus}(c,n))\bigr).
\tag{5}
\]

Appendix B also gives a Lean proof of (5). In the present definitions,
`FinitelyRenormalizable` is an abbreviation for the negation of this
summability statement. It is consequently false for every parameter. A uniform
positive lower bound for the Gaussian areas of infinitely many disjoint
principal-nest annuli is likewise impossible.

This does not contradict genuine conformal-modulus estimates. It shows
that those estimates cannot be supplied to fields whose `modulus` is (4).
Renaming the proxy, or citing a classical theorem against the present
types, does not repair this mismatch.

**A misleading dependency-only shortcut must be avoided.** One can eliminate
uses of the false intersection axiom in shrink-based branches by deriving
`False` from their impossible shrink hypotheses. That is not a proof of
(GI), nor a repair of the intended parameter-dynamics argument.

## 3. The sound connectedness replacement

Work in the ordinary subspace \(S=M\), with its inherited metric. For
\(c\in S\), define

\[
C_n(c)=\operatorname{Comp}_{B_S(c,2^{-n})}(c),
\tag{6}
\]

where \(\operatorname{Comp}\) means **connected component**, not path
component. Equivalently, its image in the plane is the component of
\(M\cap B_{\mathbb C}(c,2^{-n})\) containing \(c\).

The following hold for every metric space \(S\), without any local
connectedness assumption:

| Property | Reason |
| --- | --- |
| \(c\in C_n(c)\) | \(2^{-n}>0\), so the center belongs to its ball. |
| \(C_n(c)\) is connected | A component containing its specified point is nonempty and preconnected. |
| \(C_{n+1}(c)\subseteq C_n(c)\) | Monotonicity of connected components under inclusion of the balls. |
| \(C_n(c)\subseteq B_S(c,2^{-n})\) | A component is a subset of its defining set. |
| \(\bigcap_n C_n(c)=\{c\}\) | A point in every component has distance from \(c\) less than every \(2^{-n}\), hence distance zero. |
| \(\operatorname{diam}C_n(c)\le2\cdot2^{-n}\) | The triangle inequality and containment in the radius-\(2^{-n}\) ball. |

Thus connectedness and shrinking are genuinely provable for this
replacement. Its categorical presentation is

\[
\operatorname{ofSet}\bigl(\iota(C_n(c))\bigr),
\qquad \iota:S\hookrightarrow\mathbb C,
\]

and its `ImageConnected` theorem follows by continuity of the subtype
inclusion. No straddling hypothesis is appropriate here. The new component
already lies in \(M\); retaining a non-factorization premise would make the
statement vacuous.

### 3.1 The indispensable additional condition

The missing property is

\[
\forall c\in S\;\forall n,\qquad C_n(c)\in\mathcal N_S(c).
\tag{CN}
\]

Merely containing \(c\), being connected, and having arbitrarily small
diameter do not imply this neighborhood property.
For example, in
\(S=\{0\}\cup\{1/(k+1):k\in\mathbb N\}\subseteq\mathbb R\),
the components at zero are singletons. They shrink, but \(\{0\}\) is not a
neighborhood of zero.

In fact,

\[
\operatorname{LocallyConnectedSpace}(S)
\quad\Longleftrightarrow\quad\text{(CN)}.
\tag{7}
\]

**Proof.** In a locally connected space, the component of a neighborhood
containing its center is itself a neighborhood. This gives the forward
implication. Conversely, given \(U\in\mathcal N_S(c)\), choose \(n\) with
\(B_S(c,2^{-n})\subseteq U\). Then \(C_n(c)\) is a connected neighborhood
of \(c\) contained in \(U\), which is the neighborhood characterization of
local connectedness. Appendix A implements both directions in Lean.

For \(S=M\), (CN) is therefore exactly MLC, not an innocuous new axiom.
In particular, one must not apply `IsOpen.connectedComponentIn` in the
subtype \(M\) without its required `LocallyConnectedSpace M` instance.
Local connectedness of the ambient plane does not provide that instance.

## 4. A concrete sufficient input using finite orbit observations

Instead of postulating (CN), the next analytic goal can be stated using the
existing, correctly defined finite outer approximants. This gives a precise
replacement research target, with a complete reduction to MLC.

### 4.1 Reuse the actual outer system

Let

\[
O_N=\left\{p:\ |p|\le2\ \land\
  \forall k\le N,\ |f_p^k(0)|\le2\right\}.
\]

The namespace `MLC.Categorical.Mandelbrot` in
[`CategoricalMandelbrot.lean`](../Mlc/CategoricalMandelbrot.lean)
already provides:

| Required fact | Existing declaration |
| --- | --- |
| Definition of \(O_N\) | `outerOrbitSet` |
| \(O_{N+1}\subseteq O_N\) | `outerOrbitSet_antitone` |
| Compactness of \(O_N\) | `isCompact_outerOrbitSet` |
| \(M\subseteq O_N\) | `set_subset_outerOrbitSet` |
| \(\bigcap_N O_N=M\) | `iInter_outerOrbitSet_eq_set` |

Unlike `innerOrbitSet N`, whose condition quantifies over the **entire**
orbit, \(O_N\) is genuinely a finite-observation set.

For \(c\in M\), \(r>0\), set

\[
E_N(c,r)=O_N\cap\overline B(c,r),\qquad
Q_N(c,r)=\operatorname{Comp}_{E_N(c,r)}(c).
\tag{8}
\]

Each \(Q_N(c,r)\) is nonempty, compact, and connected. To see compactness,
use that the connected component is closed in the compact subspace
\(E_N(c,r)\), then apply its continuous inclusion into the plane.
Component monotonicity makes the sequence \(Q_N(c,r)\) decreasing.

### 4.2 The component-limit lemma

For a decreasing sequence of compact subsets \(E_N\) of a metric space,
all containing \(c\),

\[
\operatorname{Comp}_{\bigcap_N E_N}(c)
=\bigcap_N\operatorname{Comp}_{E_N}(c).
\tag{9}
\]

**Proof.** The component on the left is a connected subset of every
\(E_N\) containing \(c\), so it lies in every component on the right.
Conversely, the right side is a decreasing intersection of compact
connected sets containing the common point \(c\). It is connected, contains
\(c\), and lies in \(\bigcap_N E_N\). Maximality of the connected component
gives the other inclusion.

This argument needs compactness; it is not a claim that arbitrary
intersections of connected sets are connected. Appendix A implements
(9) using `MLC.Quadratic.isPreconnected_iInter_of_sequence`.
For (8), it gives

\[
\bigcap_N Q_N(c,r)
=\operatorname{Comp}_{M\cap\overline B(c,r)}(c).
\tag{10}
\]

### 4.3 The uniform-buffer condition

The proposed finite-observation input is:

\[
\boxed{
\begin{gathered}
\forall c\in M\;\forall\varepsilon>0,\
\exists r,\delta\quad 0<\delta<r<\varepsilon,\\
\forall N\;\exists L\ge N,\qquad
O_L\cap\overline B(c,\delta)\subseteq Q_N(c,r).
\end{gathered}}
\tag{UB}
\]

The radii \(r,\delta\) are chosen **before** \(N\) and work at all outer
depths. Only \(L\) may depend on \(N\). Replacing this by radii
\(\delta_N>0\) at each finite stage is insufficient: those radii could
converge to zero.

### 4.4 Complete proof that (UB) implies MLC

Fix \(c\in M\) and a subspace neighborhood \(U\) of \(c\).
Choose \(\varepsilon>0\) with \(M\cap B(c,\varepsilon)\subseteq U\).
Take \(r,\delta\) from (UB), and put

\[
D=\bigcap_N Q_N(c,r).
\]

By (9), \(D\) is connected and contains \(c\). Since \(M\subseteq O_L\)
for every \(L\), the inclusion in (UB) gives, for every \(N\),

\[
M\cap\overline B(c,\delta)\subseteq Q_N(c,r).
\]

Consequently

\[
M\cap B(c,\delta)\subseteq D
\subseteq M\cap\overline B(c,r)
\subseteq M\cap B(c,\varepsilon)\subseteq U.
\tag{11}
\]

The first inclusion makes \(D\) a neighborhood of \(c\) in \(M\);
the middle inclusions make it small enough; and it is connected.
Applying `locallyConnectedSpace_iff_connected_subsets` finishes the proof.
This works in any metric space with a decreasing compact outer
approximation, not just for \(M\).

Appendix A contains the complete Lean implementation, including its
instantiation with the repository's `outerOrbitSet`.

### 4.5 What remains to be proved, without concealing it in an interface

**This proposal does not prove (UB) for all Mandelbrot parameters.**
Because (UB) implies MLC, establishing it globally is at least an
MLC-strength task. The reduction is rigorous; the universal input is still
missing.

At a fixed \(c,r,\delta,N\), a sufficient certificate for the required
inclusion consists of \(L\ge N\) and a connected set \(H_N\) such that

\[
c\in H_N,\qquad
O_L\cap\overline B(c,\delta)\subseteq H_N
\subseteq O_N\cap\overline B(c,r).
\tag{12}
\]

Maximality of the component gives \(H_N\subseteq Q_N(c,r)\).
A parameter-puzzle construction could supply such certificates, but it
must prove the actual containments and the uniform choice of radii.

For fixed depths the orbit constraints defining \(O_L\) and \(E_N\) are
finite real polynomial inequalities. Connectedness of a proposed bridge
\(H_N\) remains a genuine additional obligation, not something certified by
sampling. There is no assertion here that polygonal bridges always exist,
or that a uniform family of certificates is currently available.

This formulation does not infer membership in \(M\) from finite
non-escape. It uses the safe direction \(M\subseteq O_L\) and uses
membership in every \(O_N\) only through the proved intersection identity.
Neither connectedness of individual \(O_N\), compactness alone, nor the
mere existence of a categorical limit establishes (UB).

## 5. Proposed source revision

The implementation should change the **specification and its consumers**,
not silently substitute new sets into old theorem names.

| Surface | Required revision |
| --- | --- |
| `Mlc/ParaPuzzleConnectivity.lean` | Remove `green_sublevel_intersection_categorical` from the supported theory. Preserve the valid dynamical connectedness, translation, subset-stratum, and limit lemmas. Retain old implications only with their hypotheses explicit, not as unconditional connectedness theorems. |
| A new counterexample module | Keep the old proposition as a definition and prove its negation. Separate axiom-free definitions from any legacy assumption before importing them here. |
| A new parameter-component module | Add (6), its connectedness theorem, and the categorical image presentation. Keep the neighborhood property separate from connectedness and shrinking. |
| A new outer-buffer module | Add (8), (9), (UB), and `mandelbrot_locallyConnected_of_uniformOuterBuffer` from Appendix A. Take the buffer as an explicit theorem argument until it has an independent proof. |
| `Mlc/CategoricalRoot.lean` and `Mlc/Core.lean` | Replace the current assembly by explicitly conditional root theorems using the new parameter-neighborhood input. The `TopCat` target itself can remain unchanged. Do not preserve an unconditional root declaration by inventing an inhabitant of (UB). |
| Renormalization and shrink interfaces | Replace frozen pieces by faithful parameter pieces before supplying classical shrinkage results. Replace Gaussian weighted area by genuine conformal modulus before supplying conformal a priori bounds; retain the old area theory under an accurate name if still useful. |
| `Mlc/EfimovCategoricalBridge.lean` | Preserve valid abstract connected-image and component-probe lemmas. Mark the target-specific universal Green carving/excision claims as refuted, rather than open realization obligations. Any new bridge must imply the new, explicitly stated neighborhood input. |
| `check_axioms.lean`, README, and root documentation | Stop requiring the false axiom in the expected frontier. Report theorem hypotheses as well as axiom dependencies. A foundation-only audit of `UB → MLC` is not an unconditional proof of MLC. |

Changes to the definition of modulus in a dependency belong in that
dependency's source and a reviewed revision update, not an untracked edit
to `.lake/packages`.

### 5.1 Finishing the original negative theorem

The remaining Lean work for the counterexample has a finite, explicit
scope:

1. Interpret integer intervals in the reals. An implementation-friendly
   invariant is \(l\le D x\le u\), equivalent to \(x\in[l/D,u/D]\)
   because \(D>0\).
2. Prove outward rounding from Euclidean division
   \(a=qD+r\), \(0\le r<D\), then prove the enclosure properties of
   addition, subtraction, multiplication, and squaring.
3. Prove `step` and `iterateBox` sound for a fixed enclosed parameter.
   Prove the strict squared-norm escape implication used by `checkCell`.
4. Interpret the adjacent-cell coverage certificate for every real
   \(x\in[-2,2]\), including endpoints, obtaining (2).
5. Assemble the finite orbit witnesses, the Green lower bound, and the
   horizontal separation. Use the categorical/set equivalence to obtain
   `¬ MLC.GreenSublevelIntersectionCategoricalData`.

These steps prove a negation, not an affirmative replacement for (GI).
The positive axiom must not remain in the supported theory alongside that
negation.

### 5.2 Completion criteria for the revised theory

The old universal proposition should have a foundation-only proof of its
negation. The component connectedness and conditional buffer reduction
should also have foundation-only proofs. The root signature must continue
to expose the unproved buffer input until a genuine parameter-dynamical
argument supplies it.

The non-shrinking and Gaussian-summability theorems below should be retained
as model-regression facts: they prevent the present proxies from being
mistaken for a shrinking Yoccoz tower or a divergent conformal-modulus
sequence again.

## Appendix A. Lean implementation of the replacement reduction

This block is a complete Lean file for the current repository, with no
`sorry`, `native_decide`, or project-axiom dependency in its theorem proofs.
The actual Mandelbrot theorem has the explicit hypothesis
`MandelbrotUniformOuterBuffer`; no inhabitant of that proposition is
constructed here.

The current `CategoricalMandelbrot` import transitively imports the old
axiom declaration. None of the proof terms below uses it. The proposed
source migration must nevertheless remove the declaration itself, not
merely hide its occurrence from an axiom report.

```lean
import Mlc.FilledJuliaConnected
import Mlc.LocalConnectivity
import Mlc.CategoricalTopologicalApproximation
import Mlc.CategoricalMandelbrot

open Set Filter Topology Metric

namespace GreenComponentRepair

noncomputable section

variable {X : Type*} [MetricSpace X]

def dyadicComponent (x : X) (n : Nat) : Set X :=
  connectedComponentIn (ball x ((1 / 2 : Real) ^ n)) x

theorem dyadicComponent_connected (x : X) (n : Nat) :
    IsConnected (dyadicComponent x n) :=
  isConnected_connectedComponentIn_iff.mpr (mem_ball_self (by positivity))

theorem locallyConnectedSpace_iff_dyadicComponent_mem_nhds :
    LocallyConnectedSpace X ↔
      ∀ (x : X) (n : Nat), dyadicComponent x n ∈ nhds x := by
  constructor
  · intro h
    letI : LocallyConnectedSpace X := h
    intro x n
    exact connectedComponentIn_mem_nhds (ball_mem_nhds x (by positivity))
  · intro h
    rw [locallyConnectedSpace_iff_connected_subsets]
    intro x U hU
    obtain ⟨n, _, hn⟩ :=
      (nhds_basis_ball_pow (by norm_num : (0 : Real) < 1 / 2)
        (by norm_num : (1 / 2 : Real) < 1)).mem_iff.mp hU
    exact ⟨dyadicComponent x n, h x n,
      isPreconnected_connectedComponentIn,
      (connectedComponentIn_subset _ _).trans hn⟩

theorem isCompact_component {F : Set X} (hF : IsCompact F) {x : X}
    (hx : x ∈ F) : IsCompact (connectedComponentIn F x) := by
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

theorem component_iInter_eq
    (F : Nat → Set X) (hanti : Antitone F)
    (hcompact : ∀ n, IsCompact (F n)) (x : X) (hx : ∀ n, x ∈ F n) :
    connectedComponentIn (⋂ n, F n) x =
      ⋂ n, connectedComponentIn (F n) x := by
  apply Subset.antisymm
  · intro y hy
    exact mem_iInter.mpr fun n =>
      connectedComponentIn_mono x (iInter_subset F n) hy
  · have hpre :
        IsPreconnected (⋂ n, connectedComponentIn (F n) x) := by
      apply MLC.Quadratic.isPreconnected_iInter_of_sequence
      · intro n m hnm
        exact connectedComponentIn_mono x (hanti hnm)
      · intro n
        exact isCompact_component (hcompact n) (hx n)
      · intro n
        exact isPreconnected_connectedComponentIn
    apply hpre.subset_connectedComponentIn
    · exact mem_iInter.mpr fun n => mem_connectedComponentIn (hx n)
    · intro y hy
      exact mem_iInter.mpr fun n =>
        connectedComponentIn_subset (F n) x (mem_iInter.mp hy n)

def outerComponent (O : Nat → Set X) (x : X) (r : Real) (N : Nat) : Set X :=
  connectedComponentIn (O N ∩ closedBall x r) x

def UniformOuterBuffer (S : Set X) (O : Nat → Set X) : Prop :=
  ∀ x ∈ S, ∀ ε > (0 : Real), ∃ r, 0 < r ∧ r < ε ∧
    ∃ δ, 0 < δ ∧ δ < r ∧
      ∀ N, ∃ L, N ≤ L ∧
        O L ∩ closedBall x δ ⊆ outerComponent O x r N

theorem locallyConnectedSpace_of_uniformOuterBuffer
    (S : Set X) (O : Nat → Set X) (hanti : Antitone O)
    (hcompact : ∀ N, IsCompact (O N)) (hlim : (⋂ N, O N) = S)
    (hbuffer : UniformOuterBuffer S O) :
    LocallyConnectedSpace S := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r, hr, hrε, δ, hδ, _, hcert⟩ := hbuffer x x.property ε hε
  have hSO : ∀ N, S ⊆ O N := by
    intro N
    rw [← hlim]
    exact iInter_subset O N
  let F : Nat → Set X := fun N => O N ∩ closedBall (x : X) r
  let D : Set X := ⋂ N, outerComponent O (x : X) r N
  have hxF : ∀ N, (x : X) ∈ F N := by
    intro N
    exact ⟨hSO N x.property, mem_closedBall_self (le_of_lt hr)⟩
  have hD_eq : D = connectedComponentIn (⋂ N, F N) (x : X) :=
    (component_iInter_eq F
      (fun _ _ h => inter_subset_inter_left _ (hanti h))
      (fun N => (hcompact N).inter_right isClosed_closedBall)
      (x : X) hxF).symm
  have hDconn : IsConnected D := by
    rw [hD_eq]
    exact isConnected_connectedComponentIn_iff.mpr (mem_iInter.mpr hxF)
  have hDS : D ⊆ S := by
    rw [← hlim]
    intro y hy
    exact mem_iInter.mpr fun N =>
      (connectedComponentIn_subset (F N) (x : X) (mem_iInter.mp hy N)).1
  have hDr : D ⊆ closedBall (x : X) r := by
    intro y hy
    exact (connectedComponentIn_subset (F 0) (x : X) (mem_iInter.mp hy 0)).2
  let V : Set S := Subtype.val ⁻¹' D
  have hVimage : (Subtype.val : S → X) '' V = D :=
    image_preimage_eq_of_subset (fun y hy => ⟨⟨y, hDS hy⟩, rfl⟩)
  refine ⟨V, ?_, ?_, ?_⟩
  · apply Filter.mem_of_superset (ball_mem_nhds x hδ)
    intro y hy
    apply mem_iInter.mpr
    intro N
    obtain ⟨L, _, hL⟩ := hcert N
    exact hL ⟨hSO L y.property, mem_closedBall.mpr (le_of_lt (mem_ball.mp hy))⟩
  · have hVconn : IsConnected V := by
      rw [← MLC.isConnected_subtype_val_image V, hVimage]
      exact hDconn
    exact hVconn.isPreconnected
  · intro y hy
    apply hεU
    exact lt_of_le_of_lt (hDr hy) hrε

theorem categorical_dyadicComponent_connected (S : Set Complex) (x : S) (n : Nat) :
    MLC.Categorical.ImageConnected
      (MLC.Categorical.ofSet
        ((Subtype.val : S → Complex) '' dyadicComponent x n)) := by
  change IsConnected (MLC.Categorical.image _)
  rw [MLC.Categorical.image_ofSet]
  exact (dyadicComponent_connected x n).image Subtype.val continuous_subtype_val.continuousOn

def MandelbrotUniformOuterBuffer : Prop :=
  UniformOuterBuffer MLC.Quadratic.MandelbrotSet
    MLC.Categorical.Mandelbrot.outerOrbitSet

theorem mandelbrot_locallyConnected_of_uniformOuterBuffer
    (hbuffer : MandelbrotUniformOuterBuffer) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet :=
  locallyConnectedSpace_of_uniformOuterBuffer
    MLC.Quadratic.MandelbrotSet MLC.Categorical.Mandelbrot.outerOrbitSet
    (fun _ _ h => MLC.Categorical.Mandelbrot.outerOrbitSet_antitone h)
    MLC.Categorical.Mandelbrot.isCompact_outerOrbitSet
    MLC.Categorical.Mandelbrot.iInter_outerOrbitSet_eq_set hbuffer

#print axioms dyadicComponent_connected
#print axioms locallyConnectedSpace_iff_dyadicComponent_mem_nhds
#print axioms component_iInter_eq
#print axioms locallyConnectedSpace_of_uniformOuterBuffer
#print axioms categorical_dyadicComponent_connected
#print axioms mandelbrot_locallyConnected_of_uniformOuterBuffer

end

end GreenComponentRepair
```

## Appendix B. Lean proofs of the two model obstructions

This is a second complete Lean file. These theorems do not use the
intersection axiom or the residual Molecule axiom.

```lean
import Mlc.Quadratic.Complex.YoccozConformal
import Mlc.Quadratic.Complex.ConformalGroetzsch
import Mlc.ParaPuzzleConnectivity

open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace GreenModelSanity

open MLC.Quadratic

theorem weighted_puzzleAnnuli_summable (c : Complex) :
    Summable (fun n => modulus (PuzzleAnnulus c n)) := by
  apply summable_of_sum_range_le
    (c := modulus Set.univ) (fun n => modulus_nonneg _)
  intro N
  have hmeas : ∀ n, MeasurableSet (PuzzleAnnulus c n) := by
    intro n
    exact (isOpen_dynamicalPuzzlePiece_conformal c n).measurableSet.diff
      (isOpen_dynamicalPuzzlePiece_conformal c (n + 1)).measurableSet
  have hdisj : Set.PairwiseDisjoint (Finset.range N) (PuzzleAnnulus c) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hzi.2
        (subset_of_le_nested (P := fun n => DynamicalPuzzlePiece c n 0)
          (dynamical_puzzle_piece_nested c)
          (Nat.succ_le_of_lt hlt) hzj.1)
    · exact hzj.2
        (subset_of_le_nested (P := fun n => DynamicalPuzzlePiece c n 0)
          (dynamical_puzzle_piece_nested c)
          (Nat.succ_le_of_lt hgt) hzi.1)
  rw [← modulus_finset_sum hdisj (fun n _ => hmeas n)]
  unfold modulus
  apply integral_mono_measure (Measure.restrict_mono (Set.subset_univ _) le_rfl)
  · exact ae_restrict_of_ae (ae_of_all _ (fun z => le_of_lt (Real.exp_pos _)))
  · exact weight_integrable.integrableOn

theorem exists_nonzero_filledJulia (c : Complex) (hc : c ∈ MandelbrotSet) :
    ∃ z ∈ K c, z ≠ 0 := by
  by_cases hc0 : c = 0
  · subst c
    refine ⟨1, ?_, one_ne_zero⟩
    change boundedOrbit 0 1
    refine ⟨1, fun n => ?_⟩
    have hfixed : orbit 0 1 n = 1 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [orbit_succ, fc, ih]
    rw [hfixed]
    norm_num
  · refine ⟨c, ?_, hc0⟩
    apply (green_function_eq_zero_iff_mem_K c c).mp
    have hz := (green_function_eq_zero_iff_mem_K c 0).mpr hc
    simpa [fc, hz] using green_function_functional_eq c 0

theorem frozen_tower_ne_singleton (c : Complex) (hc : c ∈ MandelbrotSet) :
    (⋂ n, {p | green_function c (p - c) < (1 / 2 : Real) ^ n}) ≠ {c} := by
  rw [MLC.iInter_green_sublevel_translate_eq_translate_filledJulia]
  intro h
  obtain ⟨z, hz, hzne⟩ := exists_nonzero_filledJulia c hc
  have hmem : z + c ∈ (fun w => w + c) '' K c := ⟨z, hz, rfl⟩
  rw [h] at hmem
  have heq : z + c = 0 + c := by
    simpa only [zero_add] using (mem_singleton_iff.mp hmem)
  exact hzne (add_right_cancel heq)

theorem paraPuzzle_tower_ne_singleton (c : Complex) (hc : c ∈ MandelbrotSet) :
    (⋂ n, ParaPuzzlePieceAt c n) ≠ {c} := by
  simpa only [MLC.paraPuzzlePieceAt_eq_green_translate hc] using
    frozen_tower_ne_singleton c hc

#print axioms weighted_puzzleAnnuli_summable
#print axioms frozen_tower_ne_singleton
#print axioms paraPuzzle_tower_ne_singleton

end GreenModelSanity
```
