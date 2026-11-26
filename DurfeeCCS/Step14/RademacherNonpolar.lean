module

public import DurfeeCCS.Step06.RademacherExactBounds
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The nonpolar term on the inverse line of an `α = 2` Ford arc. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step14

open Complex Filter MeasureTheory Set
open DurfeeCCS.Step06 DurfeeCCS.Step08
open scoped Topology

/-- The inverse-coordinate kernel after subtracting the constant coefficient
of the dual generating function. The real phase can be any cusp phase. -/
def fordNonpolarKernel (phase b : ℝ) (w : ℂ) : ℂ :=
  rademacherPolarKernel (Real.pi / 6) b w *
    (twoColourGenerating (exp ((phase : ℂ) * I - ((2 * Real.pi : ℝ) : ℂ) * w)) - 1)

private def fordNonpolarScale (b : ℝ) : ℝ := Real.exp (Real.pi + |b|) / 2

private theorem phase_sub_re (phase : ℝ) (w : ℂ) :
    ((phase : ℂ) * I - ((2 * Real.pi : ℝ) : ℂ) * w).re = -(2 * Real.pi * w.re) := by
  simp [Complex.mul_re]

private theorem norm_fordDualRemainder_le (phase : ℝ) {w : ℂ} (hw : 1 ≤ w.re) :
    ‖twoColourGenerating (exp ((phase : ℂ) * I - ((2 * Real.pi : ℝ) : ℂ) * w)) - 1‖ ≤
      Real.exp (Real.pi - 2 * Real.pi * w.re) / 2 := by
  let q := exp ((phase : ℂ) * I - ((2 * Real.pi : ℝ) : ℂ) * w)
  let r := Real.exp (-Real.pi)
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos)
  have hqn : ‖q‖ = Real.exp (-(2 * Real.pi * w.re)) := by
    rw [show q = exp ((phase : ℂ) * I - ((2 * Real.pi : ℝ) : ℂ) * w) from rfl,
      norm_exp, phase_sub_re]
  have hq : ‖q‖ ≤ r := by
    rw [hqn]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hw Real.pi_pos.le, Real.pi_pos]
  have hG : (twoColourGenerating (r : ℂ)).re - 1 ≤ 1 / 2 := by
    have ht := (norm_twoColourGenerating_small_disc
      (q := (r : ℂ)) (by rw [norm_real, Real.norm_eq_abs, abs_of_pos hr])).2
    exact (show _ ≤ ‖twoColourGenerating (r : ℂ) - 1‖ by
      simpa only [sub_re, one_re] using re_le_norm (twoColourGenerating (r : ℂ) - 1)).trans ht
  have hm := (norm_twoColourGenerating_sub_one_le hr hr₁ hq).trans
    (mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ ‖q‖ / r))
  have he : ‖q‖ / r = Real.exp (Real.pi - 2 * Real.pi * w.re) := by
    rw [hqn]
    dsimp only [r]
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he] at hm
  simpa only [q, div_eq_mul_inv, one_mul] using hm

/-- Uniform nonpolar decay in the inverse coordinate on the right of the Ford line. -/
theorem norm_fordNonpolarKernel_le (phase b : ℝ) {w : ℂ} (hw : 1 ≤ w.re) :
    ‖fordNonpolarKernel phase b w‖ ≤
      (Real.exp (Real.pi + |b|) / 2) * Real.exp (-(11 * Real.pi / 6) * w.re) / ‖w‖ ^ 3 := by
  have hn : 1 ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  have hRe : (((Real.pi / 6 : ℝ) : ℂ) * w + (b : ℂ) / w).re ≤
      (Real.pi / 6) * w.re + |b| := by
    rw [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    apply add_le_add_right
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_self (abs_nonneg _) hn
  unfold fordNonpolarKernel rademacherPolarKernel
  rw [norm_mul, norm_div, norm_pow, norm_exp]
  calc
    _ ≤ (Real.exp ((Real.pi / 6) * w.re + |b|) / ‖w‖ ^ 3) *
          (Real.exp (Real.pi - 2 * Real.pi * w.re) / 2) :=
      mul_le_mul (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hRe) (by positivity))
        (norm_fordDualRemainder_le phase hw) (norm_nonneg _) (by positivity)
    _ = (Real.exp ((Real.pi / 6) * w.re + |b|) *
          Real.exp (Real.pi - 2 * Real.pi * w.re)) / (2 * ‖w‖ ^ 3) := by ring
    _ = _ := by
      rw [← Real.exp_add, show (Real.pi / 6) * w.re + |b| +
          (Real.pi - 2 * Real.pi * w.re) =
          (Real.pi + |b|) + (-(11 * Real.pi / 6) * w.re) by ring, Real.exp_add]
      ring

private theorem fordNonpolar_differentiableAt (phase b : ℝ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (fordNonpolarKernel phase b) w := by
  let ζ (t : ℂ) := ((2 * Real.pi : ℝ) : ℂ) * t - (phase : ℂ) * I
  let τ (t : ℂ) := I * ζ t / (2 * Real.pi)
  have hζ : DifferentiableAt ℂ ζ w := by dsimp [ζ]; fun_prop
  have hτ : DifferentiableAt ℂ τ w :=
    ((differentiableAt_const _).mul hζ).div_const _
  have hw₀ : w ≠ 0 := by
    intro h
    simp [h] at hw
  have hτim : 0 < (τ w).im := by
    unfold τ ζ
    have h : I * (((2 * Real.pi : ℝ) : ℂ) * w - (phase : ℂ) * I) / (2 * Real.pi) =
        I * w + ((phase / (2 * Real.pi) : ℝ) : ℂ) := by
      push_cast
      field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]
      linear_combination -((phase : ℝ) : ℂ) * I_sq
    rw [h, add_im, I_mul_im, ofReal_im, add_zero]
    exact hw
  have hη := (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hτim).comp w hτ
  have hη₀ : ModularForm.eta (τ w) ≠ 0 := ModularForm.eta_ne_zero hτim
  have hg : DifferentiableAt ℂ
      (fun t : ℂ => twoColourGenerating
        (exp ((phase : ℂ) * I - ((2 * Real.pi : ℝ) : ℂ) * t))) w := by
    have he (t : ℂ) :
        twoColourGenerating (exp ((phase : ℂ) * I - ((2 * Real.pi : ℝ) : ℂ) * t)) =
        exp (-ζ t / 12) * (ModularForm.eta (τ t))⁻¹ ^ 2 := by
      rw [show (phase : ℂ) * I - ((2 * Real.pi : ℝ) : ℂ) * t = -ζ t by unfold ζ; ring]
      exact twoColourGenerating_exp_neg_eq_eta _
    simp_rw [he]
    exact (hζ.neg.div_const 12).cexp.mul ((hη.inv hη₀).pow 2)
  unfold fordNonpolarKernel rademacherPolarKernel
  have hid : DifferentiableAt ℂ (fun t : ℂ => t) w := differentiableAt_id
  have ha : DifferentiableAt ℂ (fun t : ℂ => ((Real.pi / 6 : ℝ) : ℂ) * t) w := by
    fun_prop
  have hb := (differentiableAt_const (b : ℂ)).div hid hw₀
  exact (((ha.add hb).cexp.div (hid.pow 3) (pow_ne_zero 3 hw₀)).mul
    (hg.sub (differentiableAt_const (1 : ℂ))))

private theorem norm_fordNonpolarKernel_vertical_le (phase b : ℝ) {c : ℝ} (hc : 1 ≤ c)
    (v : ℝ) :
    ‖fordNonpolarKernel phase b (verticalPoint c v)‖ ≤
      fordNonpolarScale b * Real.exp (-(11 * Real.pi / 6) * c) * (1 + v ^ 2)⁻¹ := by
  let w := verticalPoint c v
  have hw : 1 ≤ w.re := by simpa only [w, verticalPoint_re]
  have hn : 1 ≤ ‖w‖ := hw.trans (Complex.re_le_norm _)
  have hp : 1 + v ^ 2 ≤ ‖w‖ ^ 3 := calc
    _ ≤ c ^ 2 + v ^ 2 := by nlinarith
    _ = ‖w‖ ^ 2 := (norm_verticalPoint_sq c v).symm
    _ ≤ _ := by
      rw [pow_succ ‖w‖ 2]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (sq_nonneg ‖w‖)
  exact (norm_fordNonpolarKernel_le phase b hw).trans (by
    rw [show w.re = c from verticalPoint_re c v, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hp)
      (by positivity))

private theorem continuous_fordNonpolar_vertical (phase b : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    Continuous (fun v : ℝ => fordNonpolarKernel phase b (verticalPoint c v)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hF := (fordNonpolar_differentiableAt phase b
    (by simpa only [verticalPoint_re] using zero_lt_one.trans_le hc :
      0 < (verticalPoint c v).re)).continuousAt
  exact hF.comp (by unfold verticalPoint; fun_prop)

theorem integrable_fordNonpolar_vertical (phase b : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    Integrable (fun v : ℝ => fordNonpolarKernel phase b (verticalPoint c v)) := by
  have hB := (integrable_cauchy_density (u := 1) zero_lt_one).const_mul
    (fordNonpolarScale b * Real.exp (-(11 * Real.pi / 6) * c))
  simp only [one_pow] at hB
  exact hB.mono' (continuous_fordNonpolar_vertical phase b hc).aestronglyMeasurable
    (Eventually.of_forall (norm_fordNonpolarKernel_vertical_le phase b hc))

private theorem norm_integral_fordNonpolar_vertical_le (phase b : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    ‖∫ v : ℝ, fordNonpolarKernel phase b (verticalPoint c v)‖ ≤
      (fordNonpolarScale b * Real.pi) * Real.exp (-(11 * Real.pi / 6) * c) := by
  have hB := (integrable_cauchy_density (u := 1) zero_lt_one).const_mul
    (fordNonpolarScale b * Real.exp (-(11 * Real.pi / 6) * c))
  simp only [one_pow] at hB
  refine (norm_integral_le_of_norm_le hB
    (Eventually.of_forall (norm_fordNonpolarKernel_vertical_le phase b hc))).trans_eq ?_
  rw [integral_const_mul, show (∫ v : ℝ, (1 + v^2)⁻¹) = Real.pi by
    simpa only [one_pow, div_one] using integral_cauchy_density (u := 1) zero_lt_one]
  ring

private theorem norm_fordNonpolarKernel_le_uniform (phase b : ℝ) {w : ℂ} (hw : 1 ≤ w.re) :
    ‖fordNonpolarKernel phase b w‖ ≤ fordNonpolarScale b / ‖w‖ ^ 3 := by
  refine (norm_fordNonpolarKernel_le phase b hw).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have he : Real.exp (-(11 * Real.pi / 6) * w.re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by simp [mul_nonneg (show 0 ≤ 11 * Real.pi / 6 by positivity)
      (zero_le_one.trans hw)])
  simpa only [fordNonpolarScale, mul_one] using
    mul_le_mul_of_nonneg_left he (by unfold fordNonpolarScale; positivity : 0 ≤ fordNonpolarScale b)

private theorem tendsto_fordNonpolar_horizontal (phase b : ℝ) {c : ℝ} (hc : 1 ≤ c)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun R : ℝ => ∫ t in (1 : ℝ)..c, fordNonpolarKernel phase b (verticalPoint t (s * R)))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hMaj : Tendsto (fun R : ℝ => (fordNonpolarScale b * (c - 1)) * (R⁻¹) ^ 3)
      atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.pow 3).const_mul (fordNonpolarScale b * (c - 1))
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hMaj
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 : ℝ)) (b := c) (C := fordNonpolarScale b / R ^ 3)
      (f := fun t => fordNonpolarKernel phase b (verticalPoint t (s * R))) (by
        intro t ht
        rw [uIoc_of_le hc] at ht
        have hw : 1 ≤ (verticalPoint t (s * R)).re := by
          simpa only [verticalPoint_re] using ht.1.le
        have hn := Complex.abs_im_le_norm (verticalPoint t (s * R))
        rw [verticalPoint_im, abs_mul, hs, abs_of_pos hR, one_mul] at hn
        exact (norm_fordNonpolarKernel_le_uniform phase b hw).trans
          (div_le_div_of_nonneg_left (by unfold fordNonpolarScale; positivity)
            (pow_pos hR 3) (pow_le_pow_left₀ hR.le hn 3)))
  rw [abs_of_nonneg (sub_nonneg.mpr hc)] at h
  exact h.trans_eq (by rw [div_eq_mul_inv, ← inv_pow]; ring)

private theorem integral_fordNonpolar_vertical_shift (phase b : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    (∫ v : ℝ, fordNonpolarKernel phase b (verticalPoint c v)) =
      ∫ v : ℝ, fordNonpolarKernel phase b (verticalPoint 1 v) := by
  let f := fordNonpolarKernel phase b
  have hRct (R : ℝ) :
      ((∫ t in (1 : ℝ)..c, f (verticalPoint t (-R))) -
        (∫ t in (1 : ℝ)..c, f (verticalPoint t R))) +
      I * (∫ v in -R..R, f (verticalPoint c v)) -
        I * (∫ v in -R..R, f (verticalPoint 1 v)) = 0 := by
    let z := verticalPoint 1 (-R)
    let w := verticalPoint c R
    have hRect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z w (by
        intro q hq
        have hwq : 1 ≤ q.re := by
          simpa only [z, w, verticalPoint_re, min_eq_left hc] using
            (Complex.mem_reProdIm.mp hq).1.1
        exact (fordNonpolar_differentiableAt phase b (zero_lt_one.trans_le hwq)).continuousAt.continuousWithinAt)
      (by
        intro q hq
        have hwq : 1 < q.re := by
          simpa only [z, w, verticalPoint_re, min_eq_left hc] using
            (Complex.mem_reProdIm.mp hq).1.1
        exact (fordNonpolar_differentiableAt phase b (zero_lt_one.trans hwq)).differentiableWithinAt)
    dsimp only [z, w] at hRect
    simp only [verticalPoint_re, verticalPoint_im, smul_eq_mul] at hRect
    exact hRect
  have hBot : Tendsto (fun R : ℝ => ∫ t in (1 : ℝ)..c, f (verticalPoint t (-R))) atTop (𝓝 0) := by
    simpa using tendsto_fordNonpolar_horizontal phase b hc (-1) (by norm_num)
  have hTop : Tendsto (fun R : ℝ => ∫ t in (1 : ℝ)..c, f (verticalPoint t R)) atTop (𝓝 0) := by
    simpa using tendsto_fordNonpolar_horizontal phase b hc 1 (by norm_num)
  have hL := (intervalIntegral_tendsto_integral (integrable_fordNonpolar_vertical phase b le_rfl)
    tendsto_neg_atTop_atBot tendsto_id).const_mul I
  have hU := (intervalIntegral_tendsto_integral (integrable_fordNonpolar_vertical phase b hc)
    tendsto_neg_atTop_atBot tendsto_id).const_mul I
  have hLim := (((hBot.sub hTop).add hU).sub hL)
  have hLim0 : Tendsto (fun R : ℝ => ((∫ t in (1 : ℝ)..c, f (verticalPoint t (-R))) -
      (∫ t in (1 : ℝ)..c, f (verticalPoint t R))) +
      I * (∫ v in -R..R, f (verticalPoint c v)) -
      I * (∫ v in -R..R, f (verticalPoint 1 v))) atTop (𝓝 (0 : ℂ)) :=
    tendsto_const_nhds.congr fun R => (hRct R).symm
  have hEq := tendsto_nhds_unique hLim hLim0
  simp only [sub_self, zero_add, ← mul_sub] at hEq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hEq).resolve_left I_ne_zero)

/-- The full inverse vertical line has zero nonpolar contribution, by shifting
the integration line to the right. -/
theorem integral_fordNonpolarKernel_eq_zero (phase b : ℝ) :
    (∫ v : ℝ, fordNonpolarKernel phase b (verticalPoint 1 v)) = 0 := by
  let f (c : ℝ) := ∫ v : ℝ, fordNonpolarKernel phase b (verticalPoint c v)
  have hC : Tendsto (fun c : ℝ => f c) atTop (𝓝 (f 1)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop (1 : ℝ)).mono
      fun _ hc => (integral_fordNonpolar_vertical_shift phase b hc).symm)
  have hE : Tendsto (fun c : ℝ => Real.exp (-(11 * Real.pi / 6) * c)) atTop (𝓝 0) := by
    simpa only [neg_mul, Function.comp_def, id_eq] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (show 0 < 11 * Real.pi / 6 by positivity))
  have hT : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      ((eventually_ge_atTop (1 : ℝ)).mono fun c hc => norm_integral_fordNonpolar_vertical_le phase b hc)
    simpa using hE.const_mul (fordNonpolarScale b * Real.pi)
  exact tendsto_nhds_unique hC hT

private theorem integrableOn_cubic_tail {A : ℝ} (hA : 0 ≤ A) :
    IntegrableOn (fun v : ℝ => ((v + 1) ^ 3)⁻¹) (Ioi A) := by
  apply (integrableOn_add_rpow_Ioi_of_lt (a := -3) (m := 1)
    (by norm_num) (by linarith)).congr_fun _ measurableSet_Ioi
  intro v hv
  have hv' : 0 < v + 1 := by linarith [mem_Ioi.mp hv]
  change (v + 1) ^ (-(3 : ℝ)) = _
  rw [Real.rpow_neg hv'.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

private theorem integral_cubic_tail {A : ℝ} (hA : 0 ≤ A) :
    (∫ v in Ioi A, ((v + 1) ^ 3)⁻¹) = ((A + 1) ^ 2)⁻¹ / 2 := by
  have hD (v : ℝ) (hv : v ∈ Ici A) :
      HasDerivAt (fun t : ℝ => (-1 / 2) * ((t + 1) ^ 2)⁻¹) (((v + 1) ^ 3)⁻¹) v := by
    have hv' : v + 1 ≠ 0 := by linarith [mem_Ici.mp hv]
    have hs : HasDerivAt (fun t : ℝ => (t + 1) ^ 2) (2 * (v + 1)) v := by
      convert ((hasDerivAt_id v).add_const (1 : ℝ)).pow 2 using 1
      · funext t
        rfl
      · simp
    have hi : HasDerivAt (fun t : ℝ => ((t + 1) ^ 2)⁻¹)
        (-(2 * (v + 1)) / ((v + 1) ^ 2) ^ 2) v :=
      hs.inv (pow_ne_zero 2 hv')
    convert hi.const_mul (-1 / 2 : ℝ) using 1
    field_simp
  have hInv : Tendsto (fun v : ℝ => (v + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  have hLim : Tendsto (fun v : ℝ => (-1 / 2) * ((v + 1) ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa [inv_pow] using (hInv.pow 2).const_mul (-1 / 2 : ℝ)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hD (integrableOn_cubic_tail hA) hLim]
  ring

private theorem norm_fordNonpolarKernel_ray_le (phase b s : ℝ) (hs : |s| = 1)
    {v : ℝ} (hv : 0 ≤ v) :
    ‖fordNonpolarKernel phase b (verticalPoint 1 (s * v))‖ ≤
      (8 * fordNonpolarScale b) * ((v + 1) ^ 3)⁻¹ := by
  let w := verticalPoint 1 (s * v)
  have hw : 1 ≤ w.re := by simp [w]
  have hn₁ : 1 ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  have hn₂ : v ≤ ‖w‖ := by
    have him := Complex.abs_im_le_norm w
    simpa only [w, verticalPoint_im, abs_mul, hs, abs_of_nonneg hv, one_mul] using him
  have hp : (v + 1) ^ 3 ≤ 8 * ‖w‖ ^ 3 := by
    calc
      _ ≤ (2 * ‖w‖) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by ring
  have hV : 0 < (v + 1) ^ 3 := by positivity
  have hW : 0 < ‖w‖ ^ 3 := by positivity
  refine (norm_fordNonpolarKernel_le_uniform phase b hw).trans ?_
  rw [← div_eq_mul_inv, div_le_div_iff₀ hW hV]
  calc
    _ ≤ fordNonpolarScale b * (8 * ‖w‖ ^ 3) :=
      mul_le_mul_of_nonneg_left hp (by unfold fordNonpolarScale; positivity)
    _ = _ := by ring

/-- Either inverse-line tail has the quadratic cutoff bound used in summing
the nonpolar contributions over Ford arcs. -/
theorem norm_integral_fordNonpolar_tail_le (phase b s : ℝ) (hs : |s| = 1)
    {A : ℝ} (hA : 0 ≤ A) :
    ‖∫ v in Ioi A, fordNonpolarKernel phase b (verticalPoint 1 (s * v))‖ ≤
      4 * (Real.exp (Real.pi + |b|) / 2) * ((A + 1) ^ 2)⁻¹ := by
  have h := ae_restrict_mem (μ := volume) (s := Ioi A) measurableSet_Ioi
  have hMaj := (integrableOn_cubic_tail hA).const_mul (8 * fordNonpolarScale b)
  refine (norm_integral_le_of_norm_le hMaj
    (h.mono fun v hv => norm_fordNonpolarKernel_ray_le phase b s hs
      (hA.trans (mem_Ioi.mp hv).le))).trans_eq ?_
  rw [integral_const_mul, integral_cubic_tail hA]
  unfold fordNonpolarScale
  ring

/-- The finite inverse line segment is the negative of the two complementary tails. -/
theorem integral_fordNonpolar_segment_eq_neg_tails (phase b : ℝ)
    (A B : ℝ) :
    (∫ v in -A..B, fordNonpolarKernel phase b (verticalPoint 1 v)) =
      -(∫ v in Ioi A, fordNonpolarKernel phase b (verticalPoint 1 (-v))) -
        ∫ v in Ioi B, fordNonpolarKernel phase b (verticalPoint 1 v) := by
  let f (v : ℝ) := fordNonpolarKernel phase b (verticalPoint 1 v)
  have hf : Integrable f := integrable_fordNonpolar_vertical phase b le_rfl
  have hI := intervalIntegral.integral_Iic_sub_Iic (a := -A) (b := B)
    hf.integrableOn hf.integrableOn
  have hAB := intervalIntegral.integral_Iic_add_Ioi (b := B) hf.integrableOn hf.integrableOn
  have hF : (∫ v : ℝ, f v) = 0 := integral_fordNonpolarKernel_eq_zero phase b
  rw [hF] at hAB
  have hLeft : (∫ v in Ioi A, f (-v)) = ∫ v in Iic (-A), f v := by
    exact integral_comp_neg_Ioi A f
  change (∫ v in -A..B, f v) = -(∫ v in Ioi A, f (-v)) - ∫ v in Ioi B, f v
  rw [hLeft, ← hI]
  linear_combination hAB

/-- A two-sided bound on the truncated Ford segment in inverse coordinates. -/
theorem norm_integral_fordNonpolar_segment_le (phase b : ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ‖∫ v in -A..B, fordNonpolarKernel phase b (verticalPoint 1 v)‖ ≤
      4 * (Real.exp (Real.pi + |b|) / 2) * (((A + 1) ^ 2)⁻¹ + ((B + 1) ^ 2)⁻¹) := by
  rw [integral_fordNonpolar_segment_eq_neg_tails phase b A B]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  convert add_le_add
    (norm_integral_fordNonpolar_tail_le phase b (-1) (by norm_num) hA)
    (norm_integral_fordNonpolar_tail_le phase b 1 (by norm_num) hB) using 1
  · simp
  · ring

/-- The nonpolar contribution of one Ford arc. The two adjacent denominators
determine the cut heights in the inverse coordinate. -/
theorem norm_weighted_fordNonpolar_segment_le (phase b : ℝ) {ω : ℂ} (hω : ‖ω‖ ≤ 1)
    {N k l r : ℝ} (hN : 0 < N) (hk : 0 < k) (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hNl : N ≤ k + l) (hNr : N ≤ k + r) :
    ‖(ω / (k : ℂ) ^ 3) *
      (∫ v in -(l / k)..r / k, fordNonpolarKernel phase b (verticalPoint 1 v))‖ ≤
        4 * Real.exp (Real.pi + |b|) / (k * N ^ 2) := by
  have hcut (d : ℝ) (hNd : N ≤ k + d) :
      ((d / k + 1) ^ 2)⁻¹ ≤ (k / N) ^ 2 := by
    have h : N / k ≤ d / k + 1 := by
      rw [← div_self hk.ne' (a := k), ← add_div, div_le_div_iff_of_pos_right hk]
      linarith
    rw [← inv_pow, ← inv_div N k]
    exact pow_le_pow_left₀ (inv_nonneg.mpr ((div_pos hN hk).le.trans h))
      (inv_anti₀ (div_pos hN hk) h) 2
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  calc
    _ ≤ (1 / k ^ 3) * (4 * (Real.exp (Real.pi + |b|) / 2) *
        (((l / k + 1) ^ 2)⁻¹ + ((r / k + 1) ^ 2)⁻¹)) :=
      mul_le_mul (div_le_div_of_nonneg_right hω (by positivity))
        (norm_integral_fordNonpolar_segment_le phase b (div_nonneg hl hk.le) (div_nonneg hr hk.le))
        (norm_nonneg _) (by positivity)
    _ ≤ (1 / k ^ 3) * (4 * (Real.exp (Real.pi + |b|) / 2) *
        ((k / N) ^ 2 + (k / N) ^ 2)) := by
      gcongr
      · exact hcut l hNl
      · exact hcut r hNr
    _ = _ := by field_simp; norm_num

/-- The contribution to the coefficient integral after removing the polar
term, for the arc indexed by its three neighboring denominators. -/
def fordNonpolarArcTerm (k : ℕ) (phase b l r : ℝ) (ω : ℂ) : ℂ :=
  ω / (k : ℂ) ^ 3 *
    (∫ v in -(l / (k : ℝ))..r / (k : ℝ), fordNonpolarKernel phase b (verticalPoint 1 v))

/-- The total nonpolar error over an order-`N` Ford family. At most `k` arcs
have denominator `k`, and every neighboring denominator adds with `k`
to at least `N`. -/
theorem norm_sum_fordNonpolarArcTerm_le {N : ℕ} (hN : 0 < N) (B : ℝ)
    (s : ℕ → Finset ℕ) (phase b l r : ℕ → ℕ → ℝ) (ω : ℕ → ℕ → ℂ)
    (hcard : ∀ k, 1 ≤ k → k ≤ N → (s k).card ≤ k)
    (hdata : ∀ k h, 1 ≤ k → k ≤ N → h ∈ s k →
      ‖ω k h‖ ≤ 1 ∧ |b k h| ≤ B ∧ 0 ≤ l k h ∧ 0 ≤ r k h ∧
        (N : ℝ) ≤ (k : ℝ) + l k h ∧ (N : ℝ) ≤ (k : ℝ) + r k h) :
    ‖∑ j ∈ Finset.range N, ∑ h ∈ s (j + 1),
      fordNonpolarArcTerm (j + 1) (phase (j + 1) h) (b (j + 1) h)
        (l (j + 1) h) (r (j + 1) h) (ω (j + 1) h)‖ ≤
      4 * Real.exp (Real.pi + B) / (N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  let F (j h : ℕ) := fordNonpolarArcTerm (j + 1) (phase (j + 1) h) (b (j + 1) h)
    (l (j + 1) h) (r (j + 1) h) (ω (j + 1) h)
  change ‖∑ j ∈ Finset.range N, ∑ h ∈ s (j + 1), F j h‖ ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range N, ∑ h ∈ s (j + 1), ‖F j h‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _ ∈ Finset.range N, 4 * Real.exp (Real.pi + B) / (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      let k := j + 1
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hkN : k ≤ N := Finset.mem_range.mp hj
      have hkR : 0 < (k : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hk)
      have hc : ((s k).card : ℝ) ≤ k := by exact_mod_cast hcard k hk hkN
      change (∑ h ∈ s k, ‖F j h‖) ≤ _
      calc
        _ ≤ ∑ _ ∈ s k, 4 * Real.exp (Real.pi + B) / ((k : ℝ) * (N : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro h hh
          obtain ⟨hω, hb, hl, hr, hNl, hNr⟩ := hdata k h hk hkN hh
          refine (norm_weighted_fordNonpolar_segment_le (phase k h) (b k h)
            hω hNR hkR hl hr hNl hNr).trans ?_
          gcongr
        _ = ((s k).card : ℝ) * (4 * Real.exp (Real.pi + B) / ((k : ℝ) * (N : ℝ) ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (k : ℝ) * (4 * Real.exp (Real.pi + B) / ((k : ℝ) * (N : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by field_simp
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- An order-`N` family satisfying the uniform nonpolar bound vanishes. -/
theorem tendsto_fordNonpolar_error_zero (E : ℕ → ℂ) (B : ℝ)
    (hE : ∀ N : ℕ, 0 < N → ‖E N‖ ≤ 4 * Real.exp (Real.pi + B) / (N : ℝ)) :
    Tendsto E atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_gt_atTop (0 : ℕ)).mono hE)
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (4 * Real.exp (Real.pi + B))

end DurfeeCCS.Step14
