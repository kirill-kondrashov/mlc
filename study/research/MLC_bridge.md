# M1: returns with growing losses

8 November 2026. [Root README](../../README.md),
[programme](../programme.pdf), [Lean](../../Mlc/Research/Programme.lean).
The numerical and topological reductions are checked. Dynamical admissibility,
analytic realization, and novelty of a concrete class remain open.

## 1. Checked numerical part

For induced returns, record positive degrees $d_j$, distortions $K_j\ge1$,
collar contributions $\beta_j>0$, and lower bounds $m_j$.
`ReturnBudget` uses the recurrence

$$
m_0\ge0,\qquad
m_{j+1}\ge a_jm_j+u_j,\qquad
a_j\ge0,\quad u_j\ge\beta_j/d_j.
$$

Define loss $L_j=d_jK_j$, weight $w_j=\beta_j/L_j$,
and parameter budget $q_j=m_{j+1}/K_j$.
[ReturnBudget.lean](../../Mlc/Research/ReturnBudget.lean) proves
$m_j\ge0$, $q_j\ge w_j>0$, and the partial-sum comparisons.
If some $\eta,C>0$ satisfy

$$
\beta_j\ge\eta,\qquad L_j\le C(j+1),
$$

then $q_j\ge(\eta/C)/(j+1)$ and $\sum_jq_j=\infty$.
The proof uses harmonic-series divergence. Losses $L_j$ may be unbounded.
The index $j$ counts induced blocks. All losses along omitted steps must
enter $d_jK_j$; merely choosing a subsequence does not ensure this.

[Exact numerical example in Lean](../../Mlc/Research/Examples.lean):
$d_j=j+1$, $K_j=\beta_j=1$, $a_j=0$, $m_n=1/n$,
with Lean's convention $1/0=0$.
Budget divergence and $m_n\to0$ are proved.
This is a model of real inequalities, not a quadratic parameter.

## 2. Checked geometric reduction

`ConnectedNest M c` consists of open nested sets $D_n\ni c$ with compact
closures and connected $D_n\cap M$. Shrinking is not a field.
`SeparationEstimate` states:

$$
\forall\varepsilon>0\ \exists B\in\mathbb R\ \forall n\ \forall z\in\overline{D_n},
\quad \varepsilon\le |z-c|\ \Longrightarrow\
\sum_{j<n}q_j\le B.
$$

An unbounded budget forces some $D_n$ into every prescribed ball about $c$.
Hence $\bigcap_n\overline{D_n}=\{c\}$.
Compactness and nesting give a neighborhood basis; connectedness of
$D_n\cap M$ gives local connectivity at $c$.
All these steps are proved in
[ParameterGeometry.lean](../../Mlc/Research/ParameterGeometry.lean).
The numerical symbol $m_j$ is not identified with conformal modulus
without an analytic realization.

## 3. Exact candidate and open input

A `CandidateSystem` supplies a predicate $A(c,b)$ for admissible genuine
quadratic returns with numerical data $b$ from §1. Define

$$
\mathcal C_A=\{c:\exists b,\ A(c,b)\ \land\ b\text{ satisfies the loss control in §1}\}.
$$

**M1 realization:** for $c\in M\cap\mathcal C_A$, construct a
`ParameterRealization`: a genuine `ConnectedNest M c` with the §2 estimate
for the corresponding budget. Lean already derives MLC at $c$ from this.

The predicate $A$ must still be specified geometrically. Its data should
encode puzzle pieces, first returns, degrees, and collars; admissibility
must be checkable independently of MLC.
M1 is currently an exact research statement scheme.
This version exhibits no new class of quadratic parameters.

The first analytic question is a lower bound for parameter separation
in terms of collars and the product of local degree with distortion
for selected induced returns. Compare with the
[Kahn–Lyubich Covering Lemma](https://annals.math.princeton.edu/wp-content/uploads/annals-v169-n2-p05.pdf),
p. 564, §3.1.3: its coefficient already uses local degree, while its
threshold depends on total degree. Account for existing bounded-degree
blocks and the exact hypotheses of each application.

## 4. Root and first-paper goal

The new `RootInput` contains a system $A$ and two separate statements:

- `Realization`: M1 for admissible controlled data.
- `Coverage`: every $c\in M$ lies in the interior of $M$ or in $\mathcal C_A$.

Interior points are handled without analytic hypotheses.
The assembly theorems give
`MLC.mlc_conjecture : RootInput → LocallyConnectedSpace M`.
`RootInput` is not an axiom and has no constructed instance.
Global coverage does not follow from M1 and is not the first-paper goal.
[Examples.lean](../../Mlc/Research/Examples.lean) checks an empty class:
its `Realization` holds but `Coverage` fails, since $-2$ belongs to $M$
and is outside its interior.

**Range-extension requirement:** specify the exact published class $P$
and construct $c\in(M\cap\mathcal C_A)\setminus P$.
`StrictExtension` and its conditional pointwise consequence are defined in Lean.
Neither $P$ nor a new witness has yet been formalized.
Numerical nonemptiness in §1 does not replace this result.

## 5. Comparison with remaining problems

[Dudko's survey](https://arxiv.org/html/2512.24171v1) distinguishes
Problem 4.3 on unbounded satellite cases and Interpolation Problem 4.4
in §4.5 on the virtual Molecule. M1 assumes neither solution.
Class intersections can be determined after defining $A$;
coverage of the entire satellite or molecule regime is not claimed.

[Blokh–Levin–Oversteegen–Timorin](https://arxiv.org/abs/2205.03157)
give an obstruction to uniform a priori bounds for unbounded satellite
periods. Distinguish degeneration of individual renormalization moduli
from a divergent budget of parameter separation.
Also compare with [Kahn–Kapiamba–Lyubich](https://arxiv.org/abs/2606.27272)
when choosing primitive returns with parabolic tails.
Novelty of M1 would lie in a proved realization for a new class;
the numerical and topological schemes are working reductions.
