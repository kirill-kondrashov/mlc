import Mlc.GridCertificate

/-!
# Taylor-model certificates for the grid

The model `TBall` of `Mlc.GridDefs` encloses the critical iterate to first order
in the parameter: for `c` in the parameter disk with center `c₀ = fx ca cb` and
radius `rc / 2^48`,

`‖z_n(c) - (m + d (c - c₀))‖ ≤ e / 2^48`.

The model follows the phases of the derivative, so it stays sharp where a disk
enclosure grows by large factors. Two certificates use it: the model after `n`
steps lies outside the disk of radius two (the square is outside `M`), or a
moving disk centered at the model returns into itself after `p` steps (every
parameter of the square has a bounded critical orbit, so the square is inside
`M`). A stream of hints, found by a search program, selects the certificates;
the kernel verifies them.
-/

namespace MLC.Certified

open Complex MLC.Quadratic MeasureTheory ComplexConjugate

/-- The first-order model of the critical iterate as a function of the parameter. -/
noncomputable def tmodel (ca cb : ℤ) (t : TBall) (c : ℂ) : ℂ :=
  fx t.mx t.my + fx t.dx t.dy * (c - fx ca cb)

lemma nat_le_ceil (x : ℕ) : (x : ℝ) ≤ SN * (((x + (SN - 1)) / SN : ℕ) : ℝ) := by
  have hpos : 0 < SN := by unfold SN; norm_num
  have h1 := Nat.div_add_mod (x + (SN - 1)) SN
  have h2 := Nat.mod_lt (x + (SN - 1)) hpos
  have h3 : x ≤ SN * ((x + (SN - 1)) / SN) := by omega
  exact_mod_cast h3

lemma div_le_ceil_div (x : ℕ) :
    (x : ℝ) / SN ≤ (((x + (SN - 1)) / SN : ℕ) : ℝ) := by
  have hS := SN_pos
  rw [div_le_iff₀ hS]
  have := nat_le_ceil x
  linarith

lemma round_dstep (a b c d : ℤ) :
    ‖fx ((2 * (a * c - b * d)) / (SN : ℤ) + SN) ((2 * (a * d + b * c)) / (SN : ℤ))
        - (2 * (fx a b * fx c d) + 1)‖ ≤ 2 / SN := by
  have hS := SN_pos
  have hSz : (0 : ℤ) < SN := by unfold SN; norm_num
  have h1 := Int.mul_ediv_add_emod (2 * (a * c - b * d)) (SN : ℤ)
  have h2 := Int.mul_ediv_add_emod (2 * (a * d + b * c)) (SN : ℤ)
  have e1 := Int.emod_nonneg (2 * (a * c - b * d)) hSz.ne'
  have e1' := Int.emod_lt_of_pos (2 * (a * c - b * d)) hSz
  have e2 := Int.emod_nonneg (2 * (a * d + b * c)) hSz.ne'
  have e2' := Int.emod_lt_of_pos (2 * (a * d + b * c)) hSz
  generalize (2 * (a * c - b * d)) / (SN : ℤ) = q1 at *
  generalize (2 * (a * c - b * d)) % (SN : ℤ) = r1 at *
  generalize (2 * (a * d + b * c)) / (SN : ℤ) = q2 at *
  generalize (2 * (a * d + b * c)) % (SN : ℤ) = r2 at *
  have h1r : (SN : ℝ) * (q1 : ℝ) + (r1 : ℝ) = 2 * ((a : ℝ) * c - (b : ℝ) * d) := by
    exact_mod_cast h1
  have h2r : (SN : ℝ) * (q2 : ℝ) + (r2 : ℝ) = 2 * ((a : ℝ) * d + (b : ℝ) * c) := by
    exact_mod_cast h2
  have e1r : (0 : ℝ) ≤ r1 := by exact_mod_cast e1
  have e1r' : (r1 : ℝ) < SN := by exact_mod_cast e1'
  have e2r : (0 : ℝ) ≤ r2 := by exact_mod_cast e2
  have e2r' : (r2 : ℝ) < SN := by exact_mod_cast e2'
  have hre : (fx (q1 + SN) q2 - (2 * (fx a b * fx c d) + 1)).re
      = -((r1 : ℝ) / (SN : ℝ) ^ 2) := by
    simp only [fx, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    field_simp
    linear_combination h1r
  have him : (fx (q1 + SN) q2 - (2 * (fx a b * fx c d) + 1)).im
      = -((r2 : ℝ) / (SN : ℝ) ^ 2) := by
    simp only [fx, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    linear_combination h2r
  have hb : ∀ r : ℝ, 0 ≤ r → r < SN → |-(r / (SN : ℝ) ^ 2)| ≤ 1 / SN := by
    intro r hr hr'
    rw [abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hS]
    nlinarith
  calc _ ≤ |(fx (q1 + SN) q2 - (2 * (fx a b * fx c d) + 1)).re| +
        |(fx (q1 + SN) q2 - (2 * (fx a b * fx c d) + 1)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / SN + 1 / SN := by
        rw [hre, him]
        exact add_le_add (hb _ e1r e1r') (hb _ e2r e2r')
    _ = 2 / SN := by ring

lemma tm_alg (z c c0 M D δ w m' d' : ℂ) (hz : z = M + D * δ + w) (hc : c = c0 + δ) :
    (z ^ 2 + c) - (m' + d' * δ) =
      ((D * δ + w) ^ 2 + 2 * M * w) - (m' - (M ^ 2 + c0)) - (d' - (2 * (M * D) + 1)) * δ := by
  subst hz; subst hc; ring

lemma tm_step_enclosure {ca cb : ℤ} {rc : ℕ} {t : TBall} {c z : ℂ}
    (hc : ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN)
    (hz : ‖z - tmodel ca cb t c‖ ≤ (t.e : ℝ) / SN) :
    ‖(z ^ 2 + c) - tmodel ca cb (tmStep ca cb rc t) c‖ ≤
      ((tmStep ca cb rc t).e : ℝ) / SN := by
  have hS := SN_pos
  have hMn := fx_norm_le (normUB_sq t.mx t.my)
  have hDn := fx_norm_le (normUB_sq t.dx t.dy)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℂ, δ = c - fx ca cb := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = z - tmodel ca cb t c := ⟨_, rfl⟩
  have hδn : ‖δ‖ ≤ (rc : ℝ) / SN := by rw [hδ]; exact hc
  have hwn : ‖w‖ ≤ (t.e : ℝ) / SN := by rw [hw]; exact hz
  have hz2 : z = fx t.mx t.my + fx t.dx t.dy * δ + w := by
    rw [hw, hδ]; simp only [tmodel]; ring
  have hc2 : c = fx ca cb + δ := by rw [hδ]; ring
  have hDδ : ‖fx t.dx t.dy * δ‖ ≤
      (((normUB t.dx t.dy * rc + (SN - 1)) / SN : ℕ) : ℝ) / SN := by
    rw [norm_mul]
    calc ‖fx t.dx t.dy‖ * ‖δ‖
        ≤ ((normUB t.dx t.dy : ℕ) : ℝ) / SN * ((rc : ℝ) / SN) :=
          mul_le_mul hDn hδn (norm_nonneg _) (by positivity)
      _ = ((normUB t.dx t.dy * rc : ℕ) : ℝ) / SN / SN := by push_cast; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (div_le_ceil_div _) hS.le
  have hρ : ‖fx t.dx t.dy * δ + w‖ ≤ ((t.rho rc : ℕ) : ℝ) / SN := by
    calc ‖fx t.dx t.dy * δ + w‖ ≤ ‖fx t.dx t.dy * δ‖ + ‖w‖ := norm_add_le _ _
      _ ≤ (((normUB t.dx t.dy * rc + (SN - 1)) / SN : ℕ) : ℝ) / SN + (t.e : ℝ) / SN :=
          add_le_add hDδ hwn
      _ = ((t.rho rc : ℕ) : ℝ) / SN := by
          simp only [TBall.rho]; push_cast; ring
  have hrem : ‖(fx t.dx t.dy * δ + w) ^ 2 + 2 * fx t.mx t.my * w‖ ≤
      ((t.rho rc : ℕ) : ℝ) / SN * (((t.rho rc : ℕ) : ℝ) / SN) +
        2 * (((normUB t.mx t.my : ℕ) : ℝ) / SN) * ((t.e : ℝ) / SN) := by
    calc ‖(fx t.dx t.dy * δ + w) ^ 2 + 2 * fx t.mx t.my * w‖
        ≤ ‖(fx t.dx t.dy * δ + w) ^ 2‖ + ‖2 * fx t.mx t.my * w‖ := norm_add_le _ _
      _ ≤ ((t.rho rc : ℕ) : ℝ) / SN * (((t.rho rc : ℕ) : ℝ) / SN) +
          2 * (((normUB t.mx t.my : ℕ) : ℝ) / SN) * ((t.e : ℝ) / SN) := by
        refine add_le_add ?_ ?_
        · rw [norm_pow, pow_two]
          exact mul_le_mul hρ hρ (norm_nonneg _) ((norm_nonneg _).trans hρ)
        · rw [norm_mul, norm_mul]
          have h2 : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h2]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hMn (by norm_num)) hwn
            (norm_nonneg _) (by positivity)
  have hceil : ((t.rho rc : ℕ) : ℝ) / SN * (((t.rho rc : ℕ) : ℝ) / SN) +
      2 * (((normUB t.mx t.my : ℕ) : ℝ) / SN) * ((t.e : ℝ) / SN) ≤
      (((t.rho rc * t.rho rc + 2 * normUB t.mx t.my * t.e + (SN - 1)) / SN : ℕ) : ℝ) / SN := by
    have h := div_le_ceil_div (t.rho rc * t.rho rc + 2 * normUB t.mx t.my * t.e)
    have e1 : ((t.rho rc : ℕ) : ℝ) / SN * (((t.rho rc : ℕ) : ℝ) / SN) +
        2 * (((normUB t.mx t.my : ℕ) : ℝ) / SN) * ((t.e : ℝ) / SN) =
        (((t.rho rc * t.rho rc + 2 * normUB t.mx t.my * t.e : ℕ) : ℝ) / SN) / SN := by
      push_cast; field_simp
    rw [e1]
    exact div_le_div_of_nonneg_right h hS.le
  have hηm := round_step t.mx t.my ca cb
  have hηd := round_dstep t.mx t.my t.dx t.dy
  have hηdδ : ‖(fx (tmStep ca cb rc t).dx (tmStep ca cb rc t).dy -
        (2 * (fx t.mx t.my * fx t.dx t.dy) + 1)) * δ‖ ≤
      (((2 * rc + (SN - 1)) / SN : ℕ) : ℝ) / SN := by
    rw [norm_mul]
    have h1 : ‖fx (tmStep ca cb rc t).dx (tmStep ca cb rc t).dy -
        (2 * (fx t.mx t.my * fx t.dx t.dy) + 1)‖ ≤ 2 / SN := hηd
    calc _ ≤ 2 / (SN : ℝ) * ((rc : ℝ) / SN) :=
          mul_le_mul h1 hδn (norm_nonneg _) (by positivity)
      _ = ((2 * rc : ℕ) : ℝ) / SN / SN := by push_cast; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (div_le_ceil_div _) hS.le
  have key := tm_alg z c (fx ca cb) (fx t.mx t.my) (fx t.dx t.dy) δ w
    (fx (tmStep ca cb rc t).mx (tmStep ca cb rc t).my)
    (fx (tmStep ca cb rc t).dx (tmStep ca cb rc t).dy) hz2 hc2
  have hgoal : (z ^ 2 + c) - tmodel ca cb (tmStep ca cb rc t) c =
      ((fx t.dx t.dy * δ + w) ^ 2 + 2 * fx t.mx t.my * w) -
        (fx (tmStep ca cb rc t).mx (tmStep ca cb rc t).my -
          (fx t.mx t.my ^ 2 + fx ca cb)) -
        (fx (tmStep ca cb rc t).dx (tmStep ca cb rc t).dy -
          (2 * (fx t.mx t.my * fx t.dx t.dy) + 1)) * δ := by
    rw [← key]
    simp only [tmodel]
    rw [← hδ]
  rw [hgoal]
  calc _ ≤ ‖(fx t.dx t.dy * δ + w) ^ 2 + 2 * fx t.mx t.my * w‖ +
        ‖fx (tmStep ca cb rc t).mx (tmStep ca cb rc t).my -
          (fx t.mx t.my ^ 2 + fx ca cb)‖ +
        ‖(fx (tmStep ca cb rc t).dx (tmStep ca cb rc t).dy -
          (2 * (fx t.mx t.my * fx t.dx t.dy) + 1)) * δ‖ := by
        refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (((t.rho rc * t.rho rc + 2 * normUB t.mx t.my * t.e + (SN - 1)) / SN : ℕ) : ℝ) / SN +
        2 / SN + (((2 * rc + (SN - 1)) / SN : ℕ) : ℝ) / SN := by
        refine add_le_add (add_le_add (hrem.trans hceil) hηm) hηdδ
    _ = ((tmStep ca cb rc t).e : ℝ) / SN := by
        simp only [tmStep]
        push_cast
        ring

lemma norm_le_of_tmodel {ca cb : ℤ} {rc : ℕ} {t : TBall} {c z : ℂ}
    (hc : ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN) (hz : ‖z - tmodel ca cb t c‖ ≤ (t.e : ℝ) / SN) :
    ‖z - fx t.mx t.my‖ ≤ ((t.rho rc : ℕ) : ℝ) / SN := by
  have hS := SN_pos
  have hDn := fx_norm_le (normUB_sq t.dx t.dy)
  have hDδ : ‖fx t.dx t.dy * (c - fx ca cb)‖ ≤
      (((normUB t.dx t.dy * rc + (SN - 1)) / SN : ℕ) : ℝ) / SN := by
    rw [norm_mul]
    calc ‖fx t.dx t.dy‖ * ‖c - fx ca cb‖
        ≤ ((normUB t.dx t.dy : ℕ) : ℝ) / SN * ((rc : ℝ) / SN) :=
          mul_le_mul hDn hc (norm_nonneg _) (by positivity)
      _ = ((normUB t.dx t.dy * rc : ℕ) : ℝ) / SN / SN := by push_cast; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (div_le_ceil_div _) hS.le
  calc ‖z - fx t.mx t.my‖
      = ‖(z - tmodel ca cb t c) + fx t.dx t.dy * (c - fx ca cb)‖ := by
        congr 1; simp only [tmodel]; ring
    _ ≤ ‖z - tmodel ca cb t c‖ + ‖fx t.dx t.dy * (c - fx ca cb)‖ := norm_add_le _ _
    _ ≤ (t.e : ℝ) / SN + (((normUB t.dx t.dy * rc + (SN - 1)) / SN : ℕ) : ℝ) / SN :=
        add_le_add hz hDδ
    _ = ((t.rho rc : ℕ) : ℝ) / SN := by
        simp only [TBall.rho]; push_cast; ring

lemma norm_le_of_tmodel' {ca cb : ℤ} {rc : ℕ} {t : TBall} {c z : ℂ}
    (hc : ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN) (hz : ‖z - tmodel ca cb t c‖ ≤ (t.e : ℝ) / SN) :
    ‖z‖ ≤ (((normUB t.mx t.my : ℕ) : ℝ) + ((t.rho rc : ℕ) : ℝ)) / SN := by
  have h1 := norm_le_of_tmodel hc hz
  have h2 := fx_norm_le (normUB_sq t.mx t.my)
  calc ‖z‖ = ‖(z - fx t.mx t.my) + fx t.mx t.my‖ := by congr 1; ring
    _ ≤ ‖z - fx t.mx t.my‖ + ‖fx t.mx t.my‖ := norm_add_le _ _
    _ ≤ _ := by
        rw [add_div]
        linarith

lemma tm_iter_enclosure {ca cb : ℤ} {rc : ℕ} {c : ℂ}
    (hc : ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN) :
    ∀ (n : ℕ) (t : TBall), ∃ B : ℝ, 0 ≤ B ∧
      ∀ z : ℂ, ‖z - tmodel ca cb t c‖ ≤ (t.e : ℝ) / SN →
        ‖(fc c)^[n] z - tmodel ca cb (tmIter ca cb rc n t) c‖ ≤
            ((tmIter ca cb rc n t).e : ℝ) / SN ∧
          ∀ k, k ≤ n → ‖(fc c)^[k] z‖ ≤ B := by
  have hS := SN_pos
  intro n
  induction n with
  | zero =>
      intro t
      refine ⟨(((normUB t.mx t.my : ℕ) : ℝ) + ((t.rho rc : ℕ) : ℝ)) / SN, by positivity, ?_⟩
      intro z hz
      refine ⟨by simpa [tmIter] using hz, ?_⟩
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      simpa using norm_le_of_tmodel' hc hz
  | succ n ih =>
      intro t
      obtain ⟨B', hB', h'⟩ := ih (tmStep ca cb rc t)
      refine ⟨(((normUB t.mx t.my : ℕ) : ℝ) + ((t.rho rc : ℕ) : ℝ)) / SN + B',
        by positivity, ?_⟩
      intro z hz
      have hz' : ‖(fc c z) - tmodel ca cb (tmStep ca cb rc t) c‖ ≤
          ((tmStep ca cb rc t).e : ℝ) / SN := tm_step_enclosure hc hz
      obtain ⟨h1, h2⟩ := h' (fc c z) hz'
      refine ⟨by simpa [tmIter, Function.iterate_succ_apply] using h1, ?_⟩
      intro k hk
      have hB0 : 0 ≤ (((normUB t.mx t.my : ℕ) : ℝ) + ((t.rho rc : ℕ) : ℝ)) / SN := by positivity
      rcases k with _ | j
      · have := norm_le_of_tmodel' hc hz
        simp only [Function.iterate_zero, id_eq]
        linarith
      · have := h2 j (by omega)
        rw [Function.iterate_succ_apply]
        linarith

/-- The model of the `k`-th iterate over the parameter disk. -/
def TEncl (ca cb : ℤ) (rc : ℕ) (k : ℕ) (t : TBall) : Prop :=
  ∀ c : ℂ, ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN →
    ‖orbit c 0 k - tmodel ca cb t c‖ ≤ (t.e : ℝ) / SN

lemma tEncl_zero (ca cb : ℤ) (rc : ℕ) : TEncl ca cb rc 0 TBall.zero := by
  intro c _
  simp [tmodel, TBall.zero, fx_zero]

lemma tEncl_iter {ca cb : ℤ} {rc : ℕ} : ∀ (n k : ℕ) (t : TBall),
    TEncl ca cb rc k t → TEncl ca cb rc (k + n) (tmIter ca cb rc n t) := by
  intro n
  induction n with
  | zero => intro k t h; simpa [tmIter] using h
  | succ n ih =>
      intro k t h
      have h1 : TEncl ca cb rc (k + 1) (tmStep ca cb rc t) := by
        intro c hc
        have horbit : orbit c 0 (k + 1) = (orbit c 0 k) ^ 2 + c := by
          rw [orbit_succ]; rfl
        rw [horbit]
        exact tm_step_enclosure hc (h c hc)
      have := ih (k + 1) _ h1
      rw [show k + (n + 1) = k + 1 + n by omega]
      simpa [tmIter] using this

lemma tEncl_to_encl {ca cb : ℤ} {rc k : ℕ} {t : TBall} (h : TEncl ca cb rc k t) :
    Encl (fx ca cb) ((rc : ℝ) / SN) k (t.toBall rc) := by
  intro c hc
  exact norm_le_of_tmodel hc (h c hc)

lemma Sq.checkOut_sound {q : Sq} {n : ℕ} (h : q.checkOut n = true) :
    q.set ∩ MandelbrotSet = ∅ := by
  simp only [Sq.checkOut, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, hesc⟩ := h
  have hE : TEncl q.ca q.cb q.rc (0 + n) (tmIter q.ca q.cb q.rc n TBall.zero) :=
    tEncl_iter n 0 _ (tEncl_zero _ _ _)
  rw [zero_add] at hE
  have hEncl := tEncl_to_encl hE
  ext c
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hc hM
  have h2 := escaped_sound hEncl hesc (Sq.set_subset_disk q hk hc)
  rw [MLC.Quadratic.mandelbrot_eq_inter] at hM
  have := Set.mem_iInter.mp hM n
  simp only [Set.mem_setOf_eq] at this
  linarith

lemma closes_sound {ca cb : ℤ} {rc : ℕ} {t : TBall} {p e' : ℕ}
    (h : closes ca cb rc t p e' = true) {c : ℂ} (hc : ‖c - fx ca cb‖ ≤ (rc : ℝ) / SN) :
    ∃ B : ℝ, ∀ z : ℂ, ‖z - tmodel ca cb t c‖ ≤ (e' : ℝ) / SN →
      ‖(fc c)^[p] z - tmodel ca cb t c‖ ≤ (e' : ℝ) / SN ∧
        ∀ k, k ≤ p → ‖(fc c)^[k] z‖ ≤ B := by
  have hS := SN_pos
  obtain ⟨B, hB0, hB⟩ := tm_iter_enclosure hc p { t with e := e' }
  refine ⟨B, fun z hz => ?_⟩
  have hz' : ‖z - tmodel ca cb { t with e := e' } c‖ ≤
      (({ t with e := e' } : TBall).e : ℝ) / SN := by
    simpa [tmodel] using hz
  obtain ⟨h1, h2⟩ := hB z hz'
  refine ⟨?_, h2⟩
  simp only [closes, decide_eq_true_eq] at h
  set tp : TBall := tmIter ca cb rc p { t with e := e' } with htp
  have hΔ : tmodel ca cb tp c - tmodel ca cb t c =
      fx (tp.mx - t.mx) (tp.my - t.my) +
        fx (tp.dx - t.dx) (tp.dy - t.dy) * (c - fx ca cb) := by
    rw [← fx_sub, ← fx_sub]
    simp only [tmodel]
    ring
  have hm := fx_norm_le (normUB_sq (tp.mx - t.mx) (tp.my - t.my))
  have hd := fx_norm_le (normUB_sq (tp.dx - t.dx) (tp.dy - t.dy))
  have hdδ : ‖fx (tp.dx - t.dx) (tp.dy - t.dy) * (c - fx ca cb)‖ ≤
      (((normUB (tp.dx - t.dx) (tp.dy - t.dy) * rc + (SN - 1)) / SN : ℕ) : ℝ) / SN := by
    rw [norm_mul]
    calc ‖fx (tp.dx - t.dx) (tp.dy - t.dy)‖ * ‖c - fx ca cb‖
        ≤ ((normUB (tp.dx - t.dx) (tp.dy - t.dy) : ℕ) : ℝ) / SN * ((rc : ℝ) / SN) :=
          mul_le_mul hd hc (norm_nonneg _) (by positivity)
      _ = ((normUB (tp.dx - t.dx) (tp.dy - t.dy) * rc : ℕ) : ℝ) / SN / SN := by
          push_cast; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (div_le_ceil_div _) hS.le
  have hhr : ((normUB (tp.mx - t.mx) (tp.my - t.my) : ℕ) : ℝ) +
      (((normUB (tp.dx - t.dx) (tp.dy - t.dy) * rc + (SN - 1)) / SN : ℕ) : ℝ) +
        (tp.e : ℝ) ≤ (e' : ℝ) := by exact_mod_cast h
  calc ‖(fc c)^[p] z - tmodel ca cb t c‖
      = ‖((fc c)^[p] z - tmodel ca cb tp c) + (tmodel ca cb tp c - tmodel ca cb t c)‖ := by
        congr 1; ring
    _ ≤ ‖(fc c)^[p] z - tmodel ca cb tp c‖ + ‖tmodel ca cb tp c - tmodel ca cb t c‖ :=
        norm_add_le _ _
    _ ≤ (tp.e : ℝ) / SN + (((normUB (tp.mx - t.mx) (tp.my - t.my) : ℕ) : ℝ) / SN +
        (((normUB (tp.dx - t.dx) (tp.dy - t.dy) * rc + (SN - 1)) / SN : ℕ) : ℝ) / SN) := by
        refine add_le_add h1 ?_
        rw [hΔ]
        exact (norm_add_le _ _).trans (add_le_add hm hdδ)
    _ ≤ (e' : ℝ) / SN := by
        rw [← add_div, ← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hS.le

lemma mem_mandelbrot_of_invariant {c : ℂ} {J p : ℕ} {D : Set ℂ} {B : ℝ} (hp : 1 ≤ p)
    (hD : ∀ z ∈ D, (fc c)^[p] z ∈ D) (hB : ∀ z ∈ D, ∀ k, k ≤ p → ‖(fc c)^[k] z‖ ≤ B)
    (hz : orbit c 0 J ∈ D) : c ∈ MandelbrotSet := by
  have hbd := iterate_bounded_of_trap (f := fc c) (D := D) hp hD hB hz
  refine ⟨max B (∑ k ∈ Finset.range J, ‖orbit c 0 k‖), ?_⟩
  intro k
  by_cases hk : k < J
  · refine le_trans ?_ (le_max_right _ _)
    exact Finset.single_le_sum (f := fun k => ‖orbit c 0 k‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr hk)
  · refine le_trans ?_ (le_max_left _ _)
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hk)
    have : orbit c 0 (J + k') = (fc c)^[k'] (orbit c 0 J) := by
      show (fc c)^[J + k'] 0 = (fc c)^[k'] ((fc c)^[J] 0)
      rw [add_comm, Function.iterate_add_apply]
    rw [this]
    exact hbd k'

lemma Sq.checkIn_sound {q : Sq} {n p j : ℕ} (h : q.checkIn n p j = true) :
    q.set ⊆ MandelbrotSet := by
  simp only [Sq.checkIn, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, hcl⟩ := h
  intro c hc
  have hcd := Sq.set_subset_disk q hk hc
  set t : TBall := tmIter q.ca q.cb q.rc n TBall.zero with ht
  have hE : TEncl q.ca q.cb q.rc (0 + n) t := tEncl_iter n 0 _ (tEncl_zero _ _ _)
  rw [zero_add] at hE
  obtain ⟨B, hB⟩ := closes_sound hcl hcd
  have hee : (t.e : ℝ) ≤ ((t.e + (q.rc / 4 + 1) * 2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right _ _
  have hz : orbit c 0 n ∈ {z : ℂ | ‖z - tmodel q.ca q.cb t c‖ ≤
      ((t.e + (q.rc / 4 + 1) * 2 ^ j : ℕ) : ℝ) / SN} := by
    simp only [Set.mem_setOf_eq]
    exact (hE c hcd).trans (div_le_div_of_nonneg_right hee SN_pos.le)
  exact mem_mandelbrot_of_invariant (J := n) (p := p + 1) (by omega)
    (fun z hz => (hB z hz).1) (fun z hz k hk => (hB z hz).2 k hk) hz

lemma Sq.certify_sound {q : Sq} {h : ℕ} :
    (q.certify h = 1 → q.set ∩ MandelbrotSet = ∅) ∧ (q.certify h = 2 → q.set ⊆ MandelbrotSet) := by
  unfold Sq.certify
  by_cases hmod : h % 2 = 0
  · rw [if_pos hmod]
    by_cases hout : q.checkOut (h / 2 - 1) = true
    · rw [if_pos hout]
      exact ⟨fun _ => Sq.checkOut_sound hout, fun h2 => absurd h2 (by norm_num)⟩
    · rw [if_neg hout]
      exact ⟨fun h1 => absurd h1 (by norm_num), fun h2 => absurd h2 (by norm_num)⟩
  · rw [if_neg hmod]
    by_cases hin : q.checkIn ((h / 2 - 1) / ladderLen / periodLen)
        ((h / 2 - 1) / ladderLen % periodLen) ((h / 2 - 1) % ladderLen) = true
    · rw [if_pos hin]
      exact ⟨fun h1 => absurd h1 (by norm_num), fun _ => Sq.checkIn_sound hin⟩
    · rw [if_neg hin]
      exact ⟨fun h1 => absurd h1 (by norm_num), fun h2 => absurd h2 (by norm_num)⟩

lemma Sq.certify_cases (q : Sq) (h : ℕ) :
    q.certify h = 0 ∨ q.certify h = 1 ∨ q.certify h = 2 := by
  unfold Sq.certify
  split_ifs <;> simp

lemma Sq.unresolved_null_of {q : Sq}
    (h : q.set ∩ MandelbrotSet = ∅ ∨ q.set ⊆ MandelbrotSet) :
    volume (q.set ∩ Unresolved) = 0 := by
  rcases h with hout | hM
  · have hsub : q.set ∩ Unresolved = ∅ := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hc hU
      have : c ∈ q.set ∩ MandelbrotSet := ⟨hc, hU.1⟩
      rw [hout] at this
      exact this
    rw [hsub]; simp
  · have hopen : q.openSet ⊆ interior MandelbrotSet :=
      interior_maximal (q.openSet_subset.trans hM) q.isOpen_openSet
    have hsub : q.set ∩ Unresolved ⊆ q.set \ q.openSet := by
      intro c ⟨hc, hU⟩
      exact ⟨hc, fun ho => hU.2 (hopen ho)⟩
    exact measure_mono_null hsub q.volume_boundary

lemma Sq.unresolved_null_certify {q : Sq} {h : ℕ} (hc : q.certify h ≠ 0) :
    volume (q.set ∩ Unresolved) = 0 := by
  have hs := Sq.certify_sound (q := q) (h := h)
  rcases Sq.certify_cases q h with h0 | h1 | h2
  · exact absurd h0 hc
  · exact Sq.unresolved_null_of (Or.inl (hs.1 h1))
  · exact Sq.unresolved_null_of (Or.inr (hs.2 h2))

lemma leaf_bound (q : Sq) (f m : ℕ) (hm : 4 ^ f ≤ m) :
    volume (q.set ∩ Unresolved) ≤ ENNReal.ofReal ((m : ℝ) / 4 ^ (q.k + f)) := by
  calc volume (q.set ∩ Unresolved) ≤ volume q.set := measure_mono Set.inter_subset_left
    _ = ENNReal.ofReal (1 / 4 ^ q.k) := q.volume_set
    _ ≤ ENNReal.ofReal ((m : ℝ) / 4 ^ (q.k + f)) := by
        apply ENNReal.ofReal_le_ofReal
        have : (1 : ℝ) / 4 ^ q.k = (4 ^ f : ℝ) / 4 ^ (q.k + f) := by
          rw [pow_add]; field_simp
        rw [this]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hm

theorem verifyTree_sound : ∀ (f : ℕ) (q : Sq) (hs : List ℕ),
    volume (q.set ∩ Unresolved) ≤
      ENNReal.ofReal (((verifyTree f q hs).1 : ℝ) / 4 ^ (q.k + f)) := by
  intro f
  induction f with
  | zero =>
      intro q hs
      cases hs with
      | nil => exact leaf_bound q 0 _ (by simp [verifyTree])
      | cons h hs =>
          by_cases h0 : h = 0
          · subst h0; exact leaf_bound q 0 _ (by simp [verifyTree])
          · by_cases h1 : h = 1
            · subst h1; exact leaf_bound q 0 _ (by simp [verifyTree])
            · by_cases hc : q.certify h = 0
              · exact leaf_bound q 0 _ (by simp [verifyTree, h0, h1, hc])
              · have : (verifyTree 0 q (h :: hs)).1 = 0 := by simp [verifyTree, h0, h1, hc]
                rw [this]
                simp [Sq.unresolved_null_certify hc]
  | succ f ih =>
      intro q hs
      cases hs with
      | nil => exact leaf_bound q (f + 1) _ (by simp [verifyTree])
      | cons h hs =>
          by_cases h0 : h = 0
          · subst h0; exact leaf_bound q (f + 1) _ (by simp [verifyTree])
          · by_cases h1 : h = 1
            · subst h1
              have hsub : q.set ∩ Unresolved ⊆
                  (q.c00.set ∩ Unresolved) ∪ (q.c10.set ∩ Unresolved) ∪
                    (q.c01.set ∩ Unresolved) ∪ (q.c11.set ∩ Unresolved) := by
                intro c ⟨hc, hM⟩
                have := Sq.subset_children q hc
                simp only [Set.mem_union] at this ⊢
                rcases this with ((h1 | h1) | h1) | h1
                · exact Or.inl (Or.inl (Or.inl ⟨h1, hM⟩))
                · exact Or.inl (Or.inl (Or.inr ⟨h1, hM⟩))
                · exact Or.inl (Or.inr ⟨h1, hM⟩)
                · exact Or.inr ⟨h1, hM⟩
              set r0 := verifyTree f q.c00 hs with hr0
              set r1 := verifyTree f q.c10 r0.2 with hr1
              set r2 := verifyTree f q.c01 r1.2 with hr2
              set r3 := verifyTree f q.c11 r2.2 with hr3
              have hcount : (verifyTree (f + 1) q (1 :: hs)).1 =
                  r0.1 + r1.1 + r2.1 + r3.1 := by simp [verifyTree, hr0, hr1, hr2, hr3]
              rw [hcount]
              calc volume (q.set ∩ Unresolved)
                  ≤ volume ((q.c00.set ∩ Unresolved) ∪ (q.c10.set ∩ Unresolved) ∪
                    (q.c01.set ∩ Unresolved) ∪ (q.c11.set ∩ Unresolved)) :=
                    measure_mono hsub
                _ ≤ volume (q.c00.set ∩ Unresolved) + volume (q.c10.set ∩ Unresolved) +
                    volume (q.c01.set ∩ Unresolved) + volume (q.c11.set ∩ Unresolved) := by
                    refine (measure_union_le _ _).trans ?_
                    refine add_le_add ((measure_union_le _ _).trans ?_) le_rfl
                    exact add_le_add ((measure_union_le _ _).trans le_rfl) le_rfl
                _ ≤ ENNReal.ofReal ((r0.1 : ℝ) / 4 ^ (q.c00.k + f)) +
                    ENNReal.ofReal ((r1.1 : ℝ) / 4 ^ (q.c10.k + f)) +
                    ENNReal.ofReal ((r2.1 : ℝ) / 4 ^ (q.c01.k + f)) +
                    ENNReal.ofReal ((r3.1 : ℝ) / 4 ^ (q.c11.k + f)) :=
                    add_le_add (add_le_add (add_le_add (ih _ _) (ih _ _)) (ih _ _)) (ih _ _)
                _ = ENNReal.ofReal (((r0.1 + r1.1 + r2.1 + r3.1 : ℕ) : ℝ) /
                      4 ^ (q.k + (f + 1))) := by
                    have hk : ∀ q' : Sq, q'.k = q.k + 1 → q'.k + f = q.k + (f + 1) := by
                      intro q' h; omega
                    rw [hk q.c00 rfl, hk q.c10 rfl, hk q.c01 rfl, hk q.c11 rfl,
                      ← ENNReal.ofReal_add (by positivity) (by positivity),
                      ← ENNReal.ofReal_add (by positivity) (by positivity),
                      ← ENNReal.ofReal_add (by positivity) (by positivity)]
                    congr 1
                    push_cast
                    ring
            · by_cases hc : q.certify h = 0
              · exact leaf_bound q (f + 1) _ (by simp [verifyTree, h0, h1, hc])
              · have : (verifyTree (f + 1) q (h :: hs)).1 = 0 := by
                  simp [verifyTree, h0, h1, hc]
                rw [this]
                simp [Sq.unresolved_null_certify hc]

lemma cellsH_sound (F : ℕ) (q : Sq) (hs : List ℕ) :
    volume (q.set ∩ Unresolved) ≤
      ENNReal.ofReal ((cellsH F q hs : ℝ) / 4 ^ (q.k + F)) :=
  verifyTree_sound F q hs

lemma coverWalk_sound : ∀ (f : ℕ) (r : Sq) (L L' : List Sq), coverWalk f r L = some L' →
    (∀ s ∈ L', s ∈ L) ∧ r.set ⊆ ⋃ s ∈ L, s.set := by
  intro f
  induction f with
  | zero =>
      intro r L L' h
      cases L with
      | nil => simp [coverWalk] at h
      | cons s L0 =>
          by_cases hs : s = r
          · simp only [coverWalk, hs, if_true, Option.some.injEq] at h
            subst h; subst hs
            refine ⟨fun x hx => List.mem_cons_of_mem _ hx, ?_⟩
            intro c hc
            simp only [Set.mem_iUnion, exists_prop]
            exact ⟨s, List.mem_cons_self, hc⟩
          · simp [coverWalk, hs] at h
  | succ f ih =>
      intro r L L' h
      cases L with
      | nil => simp [coverWalk] at h
      | cons s L0 =>
          by_cases hs : s = r
          · simp only [coverWalk, hs, if_true, Option.some.injEq] at h
            subst h; subst hs
            refine ⟨fun x hx => List.mem_cons_of_mem _ hx, ?_⟩
            intro c hc
            simp only [Set.mem_iUnion, exists_prop]
            exact ⟨s, List.mem_cons_self, hc⟩
          · simp only [coverWalk, hs, if_false] at h
            rcases h0 : coverWalk f r.c00 (s :: L0) with _ | L1
            · simp [h0] at h
            rcases h1 : coverWalk f r.c10 L1 with _ | L2
            · simp [h0, h1] at h
            rcases h2 : coverWalk f r.c01 L2 with _ | L3
            · simp [h0, h1, h2] at h
            simp only [h0, h1, h2] at h
            obtain ⟨m0, c0⟩ := ih _ _ _ h0
            obtain ⟨m1, c1⟩ := ih _ _ _ h1
            obtain ⟨m2, c2⟩ := ih _ _ _ h2
            obtain ⟨m3, c3⟩ := ih _ _ _ h
            have hL1 : ∀ x ∈ L1, x ∈ s :: L0 := m0
            have hL2 : ∀ x ∈ L2, x ∈ s :: L0 := fun x hx => hL1 x (m1 x hx)
            have hL3 : ∀ x ∈ L3, x ∈ s :: L0 := fun x hx => hL2 x (m2 x hx)
            have hsub : ∀ M : List Sq, (∀ x ∈ M, x ∈ s :: L0) →
                (⋃ t ∈ M, t.set) ⊆ ⋃ t ∈ s :: L0, t.set := by
              intro M hM c hc
              simp only [Set.mem_iUnion, exists_prop] at hc ⊢
              obtain ⟨t, ht, hct⟩ := hc
              exact ⟨t, hM t ht, hct⟩
            refine ⟨fun x hx => hL3 x (m3 x hx), ?_⟩
            intro c hc
            have := Sq.subset_children r hc
            simp only [Set.mem_union] at this
            rcases this with ((hc0 | hc1) | hc2) | hc3
            · exact c0 hc0
            · exact hsub L1 hL1 (c1 hc1)
            · exact hsub L2 hL2 (c2 hc2)
            · exact hsub L3 hL3 (c3 hc3)

lemma coverAll_sound (f : ℕ) : ∀ (rs L : List Sq), coverAll f rs L = true →
    ∀ r ∈ rs, r.set ⊆ ⋃ s ∈ L, s.set := by
  intro rs
  induction rs with
  | nil => intro L _ r hr; simp at hr
  | cons r0 rs ih =>
      intro L h r hr
      simp only [coverAll] at h
      rcases hw : coverWalk f r0 L with _ | L'
      · simp [hw] at h
      · simp only [hw] at h
        obtain ⟨hm, hc⟩ := coverWalk_sound f r0 L L' hw
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hc
        · intro c hcr
          have := ih L' h r hr hcr
          simp only [Set.mem_iUnion, exists_prop] at this ⊢
          obtain ⟨t, ht, hct⟩ := this
          exact ⟨t, hm t ht, hct⟩

lemma volume_list_le_G (D : ℕ) : ∀ L : List (Sq × List ℕ), (∀ p ∈ L, p.1.k ≤ D) →
    volume (Unresolved ∩ ⋃ p ∈ L, p.1.set) ≤
      ENNReal.ofReal (((L.map fun p => cellsH (D - p.1.k) p.1 p.2).sum : ℝ) / 4 ^ D) := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons p L ih =>
      intro hk
      have hq : p.1.k ≤ D := hk p (by simp)
      have hL : ∀ p' ∈ L, p'.1.k ≤ D := fun p' h => hk p' (by simp [h])
      have hsub : Unresolved ∩ ⋃ p' ∈ p :: L, p'.1.set ⊆
          (p.1.set ∩ Unresolved) ∪ (Unresolved ∩ ⋃ p' ∈ L, p'.1.set) := by
        intro c ⟨hM, hc⟩
        simp only [Set.mem_iUnion, exists_prop, List.mem_cons] at hc
        obtain ⟨p', hp', hcp⟩ := hc
        rcases hp' with rfl | hp'
        · exact Or.inl ⟨hcp, hM⟩
        · exact Or.inr ⟨hM, by simp only [Set.mem_iUnion, exists_prop]; exact ⟨p', hp', hcp⟩⟩
      have hexp : p.1.k + (D - p.1.k) = D := by omega
      calc volume (Unresolved ∩ ⋃ p' ∈ p :: L, p'.1.set)
          ≤ volume ((p.1.set ∩ Unresolved) ∪ (Unresolved ∩ ⋃ p' ∈ L, p'.1.set)) :=
            measure_mono hsub
        _ ≤ volume (p.1.set ∩ Unresolved) + volume (Unresolved ∩ ⋃ p' ∈ L, p'.1.set) :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal ((cellsH (D - p.1.k) p.1 p.2 : ℝ) / 4 ^ D) +
            ENNReal.ofReal (((L.map fun p => cellsH (D - p.1.k) p.1 p.2).sum : ℝ) / 4 ^ D) := by
            refine add_le_add ?_ (ih hL)
            have := cellsH_sound (D - p.1.k) p.1 p.2
            rwa [hexp] at this
        _ = ENNReal.ofReal ((((p :: L).map fun p => cellsH (D - p.1.k) p.1 p.2).sum : ℝ) /
              4 ^ D) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            simp only [List.map_cons, List.sum_cons]
            push_cast
            ring

/-- The weight of a module in terms of the count of its tiles; the generated aggregator
uses this lemma for every module and the equality of the module (see
`scripts/generate_grid_tiles.py`). -/
theorem moduleWeight_eq (S D : ℕ) (L : List (Sq × List ℕ)) :
    moduleWeight S (D, L) = (L.map fun p => cellsH (D - p.1.k) p.1 p.2).sum * 4 ^ (S - D) :=
  rfl

lemma volume_modules_le (S : ℕ) : ∀ ms : List TileModule,
    (∀ m ∈ ms, ∀ p ∈ m.2, p.1.k ≤ m.1) → (∀ m ∈ ms, m.1 ≤ S) →
    volume (Unresolved ∩ ⋃ p ∈ moduleTiles ms, p.1.set) ≤
      ENNReal.ofReal (((ms.map (moduleWeight S)).sum : ℝ) / 4 ^ S) := by
  intro ms
  induction ms with
  | nil => intro _ _; simp [moduleTiles]
  | cons m ms ih =>
      intro hk hS
      have hm : ∀ p ∈ m.2, p.1.k ≤ m.1 := hk m (by simp)
      have hmS : m.1 ≤ S := hS m (by simp)
      have hk' : ∀ m' ∈ ms, ∀ p ∈ m'.2, p.1.k ≤ m'.1 := fun m' h => hk m' (by simp [h])
      have hS' : ∀ m' ∈ ms, m'.1 ≤ S := fun m' h => hS m' (by simp [h])
      have hsub : Unresolved ∩ ⋃ p ∈ moduleTiles (m :: ms), p.1.set ⊆
          (Unresolved ∩ ⋃ p ∈ m.2, p.1.set) ∪ (Unresolved ∩ ⋃ p ∈ moduleTiles ms, p.1.set) := by
        intro c ⟨hU, hc⟩
        simp only [moduleTiles, List.flatMap_cons, List.mem_append, Set.mem_iUnion,
          exists_prop] at hc
        obtain ⟨p, hp, hcp⟩ := hc
        rcases hp with hp | hp
        · exact Or.inl ⟨hU, by simp only [Set.mem_iUnion, exists_prop]; exact ⟨p, hp, hcp⟩⟩
        · exact Or.inr ⟨hU, by
            simp only [moduleTiles, Set.mem_iUnion, exists_prop]; exact ⟨p, hp, hcp⟩⟩
      have hhead := volume_list_le_G m.1 m.2 hm
      have hexp : (4 : ℝ) ^ S = 4 ^ m.1 * 4 ^ (S - m.1) := by
        rw [← pow_add]; congr 1; omega
      have hw : (moduleWeight S m : ℝ) / 4 ^ S =
          ((m.2.map fun p => cellsH (m.1 - p.1.k) p.1 p.2).sum : ℝ) / 4 ^ m.1 := by
        unfold moduleWeight
        push_cast
        rw [hexp]
        field_simp
      calc volume (Unresolved ∩ ⋃ p ∈ moduleTiles (m :: ms), p.1.set)
          ≤ volume ((Unresolved ∩ ⋃ p ∈ m.2, p.1.set) ∪
              (Unresolved ∩ ⋃ p ∈ moduleTiles ms, p.1.set)) := measure_mono hsub
        _ ≤ volume (Unresolved ∩ ⋃ p ∈ m.2, p.1.set) +
              volume (Unresolved ∩ ⋃ p ∈ moduleTiles ms, p.1.set) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (((m.2.map fun p => cellsH (m.1 - p.1.k) p.1 p.2).sum : ℝ) / 4 ^ m.1) +
              ENNReal.ofReal (((ms.map (moduleWeight S)).sum : ℝ) / 4 ^ S) :=
            add_le_add hhead (ih hk' hS')
        _ = ENNReal.ofReal ((((m :: ms).map (moduleWeight S)).sum : ℝ) / 4 ^ S) := by
            rw [← hw, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            simp only [List.map_cons, List.sum_cons]
            push_cast
            ring

/-- The grid bound for a list of modules: the tiles (squares of level at most the depth
of their module, with hint streams) cover every root square, and the unresolved cells
of every module are counted at the depth of the module and weighed to the common side
`2 ^ (-S)`. Only the upper half-plane is classified, and the lower half is its mirror
image. -/
theorem unresolved_volume_le_symM (S f : ℕ) (ms : List TileModule)
    (hk : ∀ m ∈ ms, ∀ p ∈ m.2, p.1.k ≤ m.1) (hS : ∀ m ∈ ms, m.1 ≤ S)
    (hcov : coverAll f rootsUp ((moduleTiles ms).map Prod.fst) = true) :
    volume Unresolved ≤
      2 * ENNReal.ofReal (((ms.map (moduleWeight S)).sum : ℝ) / 4 ^ S) := by
  set L := moduleTiles ms with hL
  set A : Set ℂ := Unresolved ∩ ⋃ p ∈ L, p.1.set with hA
  have hAle : volume A ≤ ENNReal.ofReal (((ms.map (moduleWeight S)).sum : ℝ) / 4 ^ S) :=
    volume_modules_le S ms hk hS
  have hAm : MeasurableSet A := by
    refine measurableSet_unresolved.inter ?_
    refine MeasurableSet.biUnion (List.finite_toSet L).countable ?_
    intro p _
    exact p.1.measurableSet
  have hcover : (⋃ q ∈ rootsUp, q.set) ⊆ ⋃ p ∈ L, p.1.set := by
    intro c hc
    simp only [Set.mem_iUnion, exists_prop] at hc
    obtain ⟨r, hr, hcr⟩ := hc
    have h1 := coverAll_sound f rootsUp _ hcov r hr hcr
    simp only [Set.mem_iUnion, exists_prop, List.mem_map] at h1 ⊢
    obtain ⟨s, ⟨p, hp, rfl⟩, hcs⟩ := h1
    exact ⟨p, hp, hcs⟩
  have hsub : Unresolved ⊆ A ∪ conj ⁻¹' A := by
    intro c hc
    by_cases him : 0 ≤ c.im
    · exact Or.inl ⟨hc, hcover (unresolved_up_subset ⟨hc, him⟩)⟩
    · right
      have hc' : conj c ∈ Unresolved := by
        have : c ∈ conj ⁻¹' Unresolved := by rw [conj_preimage_unresolved]; exact hc
        exact this
      refine ⟨hc', hcover (unresolved_up_subset ⟨hc', ?_⟩)⟩
      simp only [Set.mem_setOf_eq, Complex.conj_im]
      linarith [not_le.mp him]
  calc volume Unresolved ≤ volume (A ∪ conj ⁻¹' A) := measure_mono hsub
    _ ≤ volume A + volume (conj ⁻¹' A) := measure_union_le _ _
    _ = volume A + volume A := by rw [volume_conj_preimage A hAm]
    _ ≤ ENNReal.ofReal (((ms.map (moduleWeight S)).sum : ℝ) / 4 ^ S) +
        ENNReal.ofReal (((ms.map (moduleWeight S)).sum : ℝ) / 4 ^ S) := add_le_add hAle hAle
    _ = 2 * ENNReal.ofReal (((ms.map (moduleWeight S)).sum : ℝ) / 4 ^ S) := by
        rw [two_mul]

end MLC.Certified
