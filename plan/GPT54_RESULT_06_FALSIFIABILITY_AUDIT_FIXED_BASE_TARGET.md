# GPT54 Result 06 — Falsifiability audit of the frozen-base target

## 1. Executive verdict

**Recommendation: 4. Inconclusive.**

Current repository evidence does **not** rigorously falsify Option A, but it also does **not** justify the earlier informal claim that the frozen-base target is numerically benign. I found **no existing runnable repository program** implementing this audit, and the earlier “>99% one large component / residual specks are pixel noise” statement in `plan/PLAN_00_frontier_overview.md` is not backed there by code, parameters, or stored output.

I therefore ran a new **read-only** numerical experiment under `/tmp` only. Its results show:
- many apparent extra components are single pixels or tiny clusters and are highly resolution/window sensitive;
- for `c = 0`, `c = 0.25`, and the sampled satellite-neck point, no robust multi-component large-scale breakup appeared;
- for **rabbit** and **basilica** in some larger windows and low levels `n = 1,2`, a **second moderately sized pixel component** persists across the two tested resolutions and two iteration cutoffs;
- however, this persistence is still only a grid experiment using approximate Green values and finite non-escape iteration, so it does **not** certify a genuine disconnection of `S(c,n) ∩ M`.

So Option A is **numerically suspect enough to deserve one bounded certification task**, but not yet false.

**Plan recommendation:** before committing to Option A or switching fully to Option B, run **one bounded certification task first** on the strongest numerical candidate (rabbit, large window, `n = 1` and `n = 2`).

---

## 2. Inventory of existing programs / evidence

### 2.1 Repository search outcome

I searched scripts, notebooks, plans, drafts, and refs for code or notebook cells implementing experiments about:
- `green_sublevel_translate_inter_mandelbrot_connected`;
- straddling cases;
- connected components of translated Green sublevels intersected with `M`;
- the “program previously used by Opus 4.8”;
- claims that residual components are pixel noise.

### 2.2 Exact findings

#### A. Existing numerical claim found

The only direct numerical claim I found is in:
- `plan/PLAN_00_frontier_overview.md` (around lines 188–194)

It says, in substance:

> Axiom 4 shows no soundness red flag: numerically the translated sublevel `∩ M`
> is one large connected component (>99% of sampled points; residual 1–2-pixel
> specks are fractal-boundary grid noise).

**Audit status:** this claim is **unsourced inside the repository**. I found no accompanying script, notebook, stored output, parameter list, resolution, escape cutoff, adjacency convention, or experiment log supporting it.

#### B. No runnable repo program located

I searched:
- `scripts/*.py`
- `notebooks/*.ipynb`
- `notebooks/**/*.ipynb`
- `draft/*.md`
- `plan/*.md`
- `refs/*.txt`
- `README.md`

and found **no repository program** implementing Mandelbrot component labeling for the frozen-base target.

The Python files present are utility/document-generation scripts only:
- `notebooks/render_notebooks.py`
- `scripts/generate_dependency_graph_site.py`
- `scripts/generate_text_docs.py`
- `scripts/generate_tex.py`
- `scripts/serve_graph_site.py`

No file among these computes Green sublevels, Mandelbrot membership grids, or connected components for the target set.

#### C. Related parameter references located

- `plan/PLAN_00_frontier_overview.md` mentions the rabbit parameter
  `-0.1226 + 0.7449i` in prior radial-proxy falsification work.
- `plan/GPT54_REVIEW_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md` explicitly recommends a serious falsifiability audit before selecting Option A.

### 2.3 Existing evidence limitations

**Checked from code search:** there is no reproducible in-repo experiment for this target.

**Elementary inference:** the earlier blanket numerical reassurance is therefore not reproducible from repository contents.

**Unverified intuition:** the earlier “residual specks are grid noise” may still be correct for many sampled cases, but the repository currently does not justify it.

---

## 3. Structural analysis of Option A plausibility

I analyze the target

```text
S(c,n) ∩ M,
S(c,n) = {c' | G_c(c' - c) < 2^{-n}}.
```

### 3.1 What is formally / mathematically clear

1. **`S(c,n)` is open.**  
   **Tag:** elementary inference from definitions plus checked continuity infrastructure.  
   Reason: `S(c,n)` is a strict sublevel set of the continuous function
   `c' ↦ green_function c (c' - c)`.

2. **`S(c,n)` is connected for `c ∈ M`.**  
   **Tag:** checked from code.  
   This is exactly the theorem `green_sublevel_translate_connected` already used in the repository.

3. **`S(c,n)` forms a nested family in `n`.**  
   **Tag:** elementary inference.  
   Since `2^{-(n+1)} < 2^{-n}`, one has `S(c,n+1) ⊆ S(c,n)`.

4. **`c ∈ S(c,n)` for `c ∈ M`.**  
   **Tag:** elementary inference using repository Green-zero facts.  
   At `c' = c`, the translated argument is `0`, and the Green function vanishes there.

5. **Connectedness of `S(c,n)` and connectedness of `M` separately do not imply connectedness of `S(c,n) ∩ M`.**  
   **Tag:** elementary topology.  
   Intersections of connected sets can be disconnected.

### 3.2 What is *not* forced

1. **No checked property found implying `S(c,n)` is convex.**  
   **Tag:** checked absence / elementary inference.  
   I found no theorem in the repository implying convexity, and there is no reason from the definition to expect it.

2. **No checked property found implying `S(c,n)` is a topological disk.**  
   **Tag:** checked absence.  
   The current repository proves connectedness of the translated Green sublevel, not disk-likeness or simple connectivity.

3. **No checked property found forcing `S(c,n) ∩ M` to be connected merely because `S(c,n)` is full or simply connected.**  
   **Tag:** checked absence / elementary topology.  
   Even strong ambient topology of `S(c,n)` would not automatically control intersections with a complicated continuum.

4. **No checked property found that `S(c,n)` is a neighborhood basis of canonical parameter pieces in the classical finite-level wake sense.**  
   **Tag:** checked from code / plan audit.  
   The repository currently treats this as a frozen-base translated Green object, not as an independently defined moving parameter parapuzzle piece.

### 3.3 Why disconnection is structurally plausible

1. **Satellite limbs and narrow necks can create apparent separated pieces in `S(c,n) ∩ M`.**  
   **Tag:** elementary geometric intuition, not repository theorem.  
   Since `M` has thin necks and fine limb structure, an open neighborhood intersected with `M` can easily look disconnected numerically if the neck width is below pixel scale.

2. **Holes in the complement do not by themselves prevent connected intersection.**  
   **Tag:** elementary topology.  
   But they make naive grid-based component counting fragile.

3. **Because the target is frozen-base rather than an independently moving parameter piece, there is no current checked geometric theorem tying `S(c,n) ∩ M` to a canonically connected parameter object.**  
   **Tag:** checked from prior audits and PLAN 04.

### 3.4 Overall structural judgment

- **Checked from code:** nothing in the current repository structurally forces Option A to be true.
- **Elementary inference:** nothing in the bare definition makes connectedness absurd either.
- **Unverified dynamical intuition:** thin-neck phenomena make numerical false positives plausible, especially in straddling low-level windows.

So structural analysis alone supports neither “obviously true” nor “obviously false.”

---

## 4. Experiment method and complete summarized results

### 4.1 Why I ran a new experiment

No suitable repository program existed. The task allowed temporary numerical output under `/tmp`, so I ran a **read-only ad hoc Python experiment** without editing the repository.

### 4.2 Experiment design

For each sample parameter `c`, level `n`, window, resolution, and iteration cutoff, I approximated:

- the translated Green-sublevel predicate via escape-time Green estimate on the orbit of `z0 = c' - c` under `z ↦ z^2 + c`;
- Mandelbrot membership of the parameter `c'` by finite non-escape iteration of `0` under `z ↦ z^2 + c'`;
- connectivity of the pixel mask approximating `S(c,n) ∩ M` using **8-neighbor adjacency**.

### 4.3 Important limitations

1. **Finite non-escape iteration does not certify Mandelbrot membership.**  
   A non-escaping point up to 300 or 800 iterations may still escape later.

2. **Escape-time Green is approximate.**  
   I used `log |z_N| / 2^N` once the orbit passed a large escape radius `R = 1e12`; this is heuristic, not interval-certified.

3. **Pixel connectivity is not topological connectivity.**  
   A 1–10 pixel cluster may be pure discretization noise.

4. **No interval/error bounds were used.**

Accordingly these experiments are **screening only**, not proof.

### 4.4 Parameters sampled

Required sample families included:
- `c = 0`
- `c = -1`
- main-cardioid boundary point `c = 0.25`
- satellite-near-neck sample `c = -0.75 + 0.1i`
- rabbit parameter `c = -0.122561 + 0.744862i`

Levels:
- `n = 1, 2, 3`

Resolutions:
- `160 × 160`
- `320 × 320`

Iteration cutoffs:
- `300`
- `800`

Adjacency convention:
- **8-neighbor**

Bulky output file:
- `/tmp/mlc_task06_audit.json`

### 4.5 Windows used

For each case I used two windows, centered either at `c` or a nearby larger context region:

- `origin`: `[-1.6,1.6]×[-1.4,1.4]`, `[-0.55,1.05]×[-0.7,0.7]`
- `basilica`: `[-1.8,-0.2]×[-0.8,0.8]`, `[-1.25,-0.25]×[-0.5,0.5]`
- `cardioid_boundary`: `[-0.25,0.75]×[-0.5,0.5]`, `[-0.95,1.45]×[-1.0,1.0]`
- `rabbit`: `[-0.822561,0.577439]×[0.044862,1.444862]`, `[-0.7,0.3]×[0.2,1.2]`
- `satellite_neck`: `[-1.25,-0.25]×[-0.4,0.6]`, `[-1.0,-0.5]×[-0.25,0.25]`

### 4.6 Summary of strongest observed component counts

The raw worst-case component counts were often dominated by isolated pixels. For example:
- basilica: max 31 components, largest sizes `[66246,1,1,1,1]`
- cardioid boundary: max 15, largest `[61406,1,1,1,1]`
- origin: max 21, largest `[50354,2,2,1,1]`
- rabbit: max 20, largest `[42046,12,2,2,1]`
- satellite neck: max 67, largest `[89702,2,2,2,2]`

This strongly suggests that **raw component count is not the right diagnostic**.

### 4.7 Robustness summary using size thresholds

I therefore re-summarized by counting how many components had size larger than thresholds `1,2,4,8,16,32`.

#### A. Cases that looked numerically benign

1. **Cardioid boundary (`c = 0.25`)**
   - For all tested `n = 1,2,3`, all windows, both resolutions, both iteration cutoffs:
   - exactly **one** component larger than size 1, 2, 4, 8, 16, 32.
   - Interpretation: no sign of robust breakup in these samples.

2. **Origin (`c = 0`)**
   - For all tested `n = 1,2,3`:
   - exactly one component larger than size 2 and above.
   - Extra components were only singleton or size-2 artifacts.

3. **Satellite-neck sample (`c = -0.75 + 0.1i`)**
   - For all tested `n = 1,2,3`:
   - exactly one component larger than size 2 and above.
   - Despite large raw component counts, they were all tiny specks.

#### B. Cases producing stronger candidates

1. **Rabbit (`c = -0.122561 + 0.744862i`)**
   - In the larger window `[-0.822561,0.577439] × [0.044862,1.444862]`:
     - at `n = 1`, the number of components of size `>16` was consistently **2** across all tested `(resolution, iteration)` pairs;
     - top sizes were approximately
       - `160/300`: `[7839, 89, 1]`
       - `160/800`: `[7799, 87, 1]`
       - `320/300`: `[31362, 331, 7]`
       - `320/800`: `[31184, 325, 7]`
     - at `n = 2`, again consistently **2** components of size `>16`:
       - `[7839,46,1]`, `[7799,44,1]`, `[31362,174,7]`, `[31184,168,7]`
     - at `n = 3`, this dropped to **1** component of size `>16`.
   - In the smaller window `[-0.7,0.3] × [0.2,1.2]`, the second component disappeared above threshold 16.

2. **Basilica (`c = -1`)**
   - In the larger window `[-1.8,-0.2] × [-0.8,0.8]`:
     - at `n = 1`, there were **3–4** components of size `>16` depending on resolution/cutoff;
       sizes roughly `[7824,27,27]`, `[7774,26,26]`, `[31384,93,93]`, `[31186,88,88]`
     - at `n = 2`, again **1–4** components of size `>16`, with top extras around `39,39` or `36,36` at higher resolution;
     - at `n = 3`, this weakened to **1–2** such components, with the second around size `20` at higher resolution only.
   - In the smaller window `[-1.25,-0.25] × [-0.5,0.5]`, the extra components disappeared above threshold 16.

### 4.8 Interpretation of the numerical results

**Checked from the `/tmp` experiment:**
- many apparent disconnections are obvious pixel specks;
- some low-level large-window rabbit and basilica experiments show a second or several secondary clusters that survive both resolutions and both iteration cutoffs.

**Elementary inference:**
- persistence across both tested cutoffs makes “late escape only” a less likely explanation for those specific clusters;
- persistence across both tested resolutions makes pure isolated-pixel noise less likely.

**But still not certified:**
- the clusters could still be artifacts of the approximate Green cutoff, window truncation, coarse sampling across narrow necks, or finite-time membership approximation.

---

## 5. Strongest candidate and robustness checks

### 5.1 Strongest candidate

The strongest candidate is:

- **base parameter:** rabbit `c = -0.122561 + 0.744862i`
- **window:** `[-0.822561,0.577439] × [0.044862,1.444862]`
- **levels:** `n = 1` and `n = 2`

Reason:
- a **second component larger than size 16** persisted in all four tested runs:
  - `160 × 160`, 300 iterations
  - `160 × 160`, 800 iterations
  - `320 × 320`, 300 iterations
  - `320 × 320`, 800 iterations
- its size also scaled upward with resolution (roughly `89 → 331` at `n=1`, `46 → 174` at `n=2`), which is more interesting than isolated noise.

### 5.2 Secondary candidate

- **basilica**, larger window, `n = 1` and `n = 2`
- but this case is less stable because the number of secondary components varies more across runs.

### 5.3 Why these are still not counterexamples

The experiment only gives **pixel masks** for an approximate predicate. It does **not** certify:
- that the secondary cluster lies in the true set `S(c,n) ∩ M`;
- that it is separated from the main cluster in the true topology;
- that any apparent gap is not bridged by points missed at current resolution.

So the strongest honest conclusion is: **numerically suspicious, not certified.**

---

## 6. Rigorous-certification gap

To turn the rabbit candidate into a real counterexample, one would need at least:

1. **Certified inclusion of two compact subsets in `M ∩ S(c,n)`.**  
   For example, two small boxes or disks each proved entirely contained in the target.

2. **A certified separating open set or crosscut in the complement of `M ∩ S(c,n)`.**  
   One needs an actual topological separator, not a pixel gap.

3. **Certified error bounds for the Green inequality.**  
   The predicate `G_c(c' - c) < 2^{-n}` would need interval or enclosure control; finite escape-time approximation alone is not enough.

4. **Certified non-membership / membership information for the Mandelbrot side.**  
   - escape certifies **non-membership**;
   - finite non-escape does **not** certify membership.
   One would need hyperbolic-component certification, interval arithmetic, or some other analytic enclosure method for the suspected clusters.

5. **A proof that the separator avoids the target everywhere, not merely on sampled pixels.**

Without these ingredients, no numerical candidate should be called a counterexample.

---

## 7. Decision recommendation

**Exact recommendation:** **4. Inconclusive** — the precise missing ingredient is a bounded certification computation for the strongest rabbit candidate.

### Practical next-step recommendation

Do **not** yet declare Option A plausible, and do **not** yet abandon it as false.

Instead:
- run **one bounded certification task first**;
- target the rabbit case with the larger window and `n = 1,2`;
- require interval/error control for both the Green inequality and membership/non-membership claims.

If that bounded certification fails to support the candidate, Option A may remain plausible enough to pursue. If it succeeds, PLAN 04 should switch away from Option A toward Option B or another independently defined parameter object.

---

## 8. Exact commands and failures

### Commands used

Repository search:

```bash
rg / grep / glob over:
- plan/*.md
- draft/*.md
- refs/*.txt
- scripts/*.py
- notebooks/*.ipynb
- notebooks/**/*.ipynb
- README.md
```

Specific direct inspections:

```bash
view plan/GPT54_TASK_06_FALSIFIABILITY_AUDIT_FIXED_BASE_TARGET.md
view plan/PLAN_04_parameter_connectivity.md
view plan/PLAN_00_frontier_overview.md
view plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md
view plan/GPT54_REVIEW_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md
```

Read-only numerical experiment:

```bash
python - <<'PY'
# ad hoc script written inline; output stored at /tmp/mlc_task06_audit.json
PY
```

Follow-up summary commands:

```bash
python - <<'PY'
# summarize component-threshold persistence from /tmp/mlc_task06_audit.json
PY
```

### Command failures

No command failures occurred during this task.

---

## 9. Complete `git status --short`

```text
M Mlc/ParaPuzzleCarvingReduction.lean
 M Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
 M plan/PLAN_04_parameter_connectivity.md
?? plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_RESULT_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_RESULT_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_RESULT_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
?? plan/GPT54_RESULT_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md
?? plan/GPT54_REVIEW_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_REVIEW_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_REVIEW_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_REVIEW_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
?? plan/GPT54_REVIEW_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md
?? plan/GPT54_TASK_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_TASK_02_FORMALIZE_CARVING_NOGO.md
?? plan/GPT54_TASK_03_PARAPUZZLE_INTERFACE_AUDIT.md
?? plan/GPT54_TASK_04_PROVE_MOTION_IMAGE_EQUIVALENCE.md
?? plan/GPT54_TASK_05_REVISE_PLAN_AND_RETIRE_DEAD_ROUTES.md
?? plan/GPT54_TASK_06_FALSIFIABILITY_AUDIT_FIXED_BASE_TARGET.md
```

---

## 10. Change-safety confirmation

- No repository source file was edited.
- No plan or documentation file was edited.
- The only repository write for this task is this result file.
- No `axiom`, `sorry`, or `admit` was introduced.
- No commit was created.
- Temporary numerical output was stored only under `/tmp` as required.
