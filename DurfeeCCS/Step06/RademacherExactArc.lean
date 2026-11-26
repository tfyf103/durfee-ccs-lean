module

public import DurfeeCCS.Step06.RademacherExactPolar

import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Deforming the finite central arc to a vertical chord in the inverse cusp coordinate. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step06

open Complex Real Set MeasureTheory
open DurfeeCCS.Step08

/-- The cusp coordinate along the central integration segment. -/
def rademacherCuspPoint (ρ x : ℝ) : ℂ := (ρ : ℂ) - (x : ℂ) * I

/-- The polar part of the cusp integrand in the original coordinate. -/
def rademacherCentralKernel (ρ a b x : ℝ) : ℂ :=
  let z := rademacherCuspPoint ρ x
  z * Complex.exp ((a : ℂ) / z + (b : ℂ) * z)

/-- Real coordinate of the endpoints after inverting the central segment. -/
def rademacherPolarLine (ρ : ℝ) : ℝ := 1 / (1 + ρ)

/-- Upper imaginary endpoint after inverting the central segment. -/
def rademacherPolarHeight (ρ : ℝ) : ℝ := 1 / (Real.sqrt ρ * (1 + ρ))

@[simp] theorem rademacherCuspPoint_re (ρ x : ℝ) : (rademacherCuspPoint ρ x).re = ρ := by
  simp [rademacherCuspPoint, Complex.mul_re]

@[simp] theorem rademacherCuspPoint_im (ρ x : ℝ) : (rademacherCuspPoint ρ x).im = -x := by
  simp [rademacherCuspPoint, Complex.mul_im]

theorem rademacherCuspPoint_ne_zero {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    rademacherCuspPoint ρ x ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simpa using hρ.ne' (by simpa using he)

theorem rademacherCuspPoint_normSq (ρ x : ℝ) :
    Complex.normSq (rademacherCuspPoint ρ x) = ρ ^ 2 + x ^ 2 := by
  simp only [Complex.normSq_apply, rademacherCuspPoint_re, rademacherCuspPoint_im]
  ring

private theorem rademacherCuspPoint_inv_endpoint {ρ x : ℝ} (hρ : 0 < ρ)
    (hx : x ^ 2 = ρ) :
    (rademacherCuspPoint ρ x)⁻¹ =
      verticalPoint (rademacherPolarLine ρ) (x / (ρ ^ 2 + ρ)) := by
  apply Complex.ext
  · simp only [Complex.inv_re, rademacherCuspPoint_re, rademacherCuspPoint_normSq,
      hx, verticalPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero,
      rademacherPolarLine]
    field_simp [hρ.ne', (show 0 < 1 + ρ by positivity).ne']
    ring
  · simp only [Complex.inv_im, rademacherCuspPoint_im, neg_neg, rademacherCuspPoint_normSq,
      hx, verticalPoint, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

theorem rademacherCuspPoint_inv_right {ρ : ℝ} (hρ : 0 < ρ) :
    (rademacherCuspPoint ρ (Real.sqrt ρ))⁻¹ =
      verticalPoint (rademacherPolarLine ρ) (rademacherPolarHeight ρ) := by
  rw [rademacherCuspPoint_inv_endpoint hρ (Real.sq_sqrt hρ.le)]
  congr 1
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  unfold rademacherPolarHeight
  rw [show ρ ^ 2 + ρ = (Real.sqrt ρ) ^ 2 * (1 + ρ) by rw [Real.sq_sqrt hρ.le]; ring]
  field_simp [hs.ne', (show 0 < 1 + ρ by positivity).ne']

theorem rademacherCuspPoint_inv_left {ρ : ℝ} (hρ : 0 < ρ) :
    (rademacherCuspPoint ρ (-Real.sqrt ρ))⁻¹ =
      verticalPoint (rademacherPolarLine ρ) (-rademacherPolarHeight ρ) := by
  rw [rademacherCuspPoint_inv_endpoint hρ (by rw [neg_sq, Real.sq_sqrt hρ.le]), neg_div]
  congr 2
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  unfold rademacherPolarHeight
  rw [show ρ ^ 2 + ρ = (Real.sqrt ρ) ^ 2 * (1 + ρ) by rw [Real.sq_sqrt hρ.le]; ring]
  field_simp [hs.ne', (show 0 < 1 + ρ by positivity).ne']

private theorem inv_cusp_mem_ball {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    (rademacherCuspPoint ρ x)⁻¹ ∈ Metric.ball ((ρ⁻¹ : ℝ) : ℂ) ρ⁻¹ := by
  let z := rademacherCuspPoint ρ x
  let w := z⁻¹
  let R := ρ⁻¹
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : 0 < Complex.normSq z := Complex.normSq_pos.mpr (rademacherCuspPoint_ne_zero hρ _)
  have hw : Complex.normSq w = R * w.re := by
    dsimp only [w, R]
    rw [Complex.normSq_inv, Complex.inv_re, rademacherCuspPoint_re]
    field_simp [hρ.ne', hz.ne']
  have hs : Complex.normSq (w - (R : ℂ)) = Complex.normSq w - 2 * R * w.re + R ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero]
    ring
  have hwre : 0 < w.re := by
    dsimp only [w]
    rw [Complex.inv_re, rademacherCuspPoint_re]
    exact div_pos hρ hz
  change w ∈ Metric.ball (R : ℂ) R
  rw [Metric.mem_ball, dist_eq_norm]
  apply lt_of_pow_lt_pow_left₀ 2 hR.le
  rw [Complex.sq_norm, hs, hw]
  nlinarith only [mul_pos hR hwre]

private theorem cuspBall_nonzero {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ}
    (hw : w ∈ Metric.ball ((ρ⁻¹ : ℝ) : ℂ) ρ⁻¹) : w ≠ 0 := by
  intro h
  rw [h, Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)] at hw
  exact (lt_irrefl _ hw)

private theorem hasDerivAt_rademacherCuspPoint (ρ x : ℝ) :
    HasDerivAt (rademacherCuspPoint ρ) (-I) x := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const I
  change HasDerivAt (fun t : ℝ => (ρ : ℂ) - (t : ℂ) * I) (-I) x
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using h.const_sub (c := (ρ : ℂ))

private theorem hasDerivAt_verticalPoint (c v : ℝ) :
    HasDerivAt (verticalPoint c) I v := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const I
  change HasDerivAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * I) I v
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using h.const_add (c := (c : ℂ))

/-- The finite polar integral equals the kernel integral over the straight chord. -/
theorem integral_rademacherCentralKernel_eq_chord {ρ : ℝ} (hρ : 0 < ρ) (a b : ℝ) :
    (∫ x in -Real.sqrt ρ..Real.sqrt ρ, rademacherCentralKernel ρ a b x) =
      ∫ v in -rademacherPolarHeight ρ..rademacherPolarHeight ρ,
        rademacherPolarKernel a b (verticalPoint (rademacherPolarLine ρ) v) := by
  let U : Set ℂ := Metric.ball ((ρ⁻¹ : ℝ) : ℂ) ρ⁻¹
  let z := rademacherCuspPoint ρ
  let v := verticalPoint (rademacherPolarLine ρ)
  let M := Real.sqrt ρ
  let H := rademacherPolarHeight ρ
  let f := rademacherPolarKernel a b
  have hM : 0 < M := Real.sqrt_pos.mpr hρ
  have hH : 0 < H := by dsimp [H, rademacherPolarHeight]; positivity
  have hL : (z (-M))⁻¹ = v (-H) := rademacherCuspPoint_inv_left hρ
  have hR : (z M)⁻¹ = v H := rademacherCuspPoint_inv_right hρ
  have hU : ∀ x : ℝ, (z x)⁻¹ ∈ U := inv_cusp_mem_ball hρ
  have hvL : v (-H) ∈ U := hL ▸ hU _
  have hvR : v H ∈ U := hR ▸ hU _
  have hv : ∀ x ∈ uIcc (-H) H, v x ∈ U := by
    intro x hx
    rw [uIcc_of_le (by linarith only [hH])] at hx
    have hseg := (convex_ball ((ρ⁻¹ : ℝ) : ℂ) ρ⁻¹).segment_subset hvL hvR
    apply hseg
    refine ⟨(H - x) / (2 * H), (H + x) / (2 * H), div_nonneg (sub_nonneg.mpr hx.2) (by positivity),
      div_nonneg (by linarith only [hx.1]) (by positivity), ?_, ?_⟩
    · field_simp [hH.ne']
      ring
    · dsimp only [v, verticalPoint]
      simp only [Complex.real_smul]
      push_cast
      have hHc : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hH.ne'
      field_simp [hHc]
      ring
  obtain ⟨F, hF⟩ : Complex.IsExactOn f U := by
    apply DifferentiableOn.isExactOn_ball
    intro w hw
    have hw₀ := cuspBall_nonzero hρ hw
    unfold f rademacherPolarKernel
    fun_prop (disch := positivity)
  have hArc (x : ℝ) (_ : x ∈ uIcc (-M) M) :
      HasDerivAt (fun x : ℝ => F ((z x)⁻¹)) (I * rademacherCentralKernel ρ a b x) x := by
    have hz₀ : z x ≠ 0 := rademacherCuspPoint_ne_zero hρ x
    have hz₁ : HasDerivAt z (-I) x := hasDerivAt_rademacherCuspPoint ρ x
    have hz := hz₁.inv hz₀
    have hf := (hF (z x)⁻¹ (hU x)).scomp x hz
    have hd : -(-I) / z x ^ 2 * f ((z x)⁻¹) = I * rademacherCentralKernel ρ a b x := by
      change -(-I) / z x ^ 2 * (Complex.exp ((a : ℂ) * (z x)⁻¹ + (b : ℂ) / (z x)⁻¹) /
        ((z x)⁻¹) ^ 3) = I * (z x * Complex.exp ((a : ℂ) / z x + (b : ℂ) * z x))
      rw [div_inv_eq_mul, div_eq_mul_inv (a : ℂ), inv_pow]
      field_simp [hz₀]
    simpa only [Function.comp_def, Pi.inv_apply, smul_eq_mul, hd] using hf
  have hChord (x : ℝ) (hx : x ∈ uIcc (-H) H) :
      HasDerivAt (fun x : ℝ => F (v x)) (I * f (v x)) x := by
    simpa only [Function.comp_def, smul_eq_mul] using (hF (v x) (hv x hx)).scomp x
      (hasDerivAt_verticalPoint (rademacherPolarLine ρ) x)
  have hIA : IntervalIntegrable (fun x => I * rademacherCentralKernel ρ a b x) volume (-M) M := by
    have hz : Continuous z := continuous_iff_continuousAt.mpr
      (fun x => (hasDerivAt_rademacherCuspPoint ρ x).continuousAt)
    apply Continuous.intervalIntegrable
    change Continuous (fun x => I * (z x * Complex.exp ((a : ℂ) / z x + (b : ℂ) * z x)))
    exact continuous_const.mul (hz.mul (Complex.continuous_exp.comp
      ((continuous_const.div hz (rademacherCuspPoint_ne_zero hρ)).add (continuous_const.mul hz))))
  have hIB : IntervalIntegrable (fun x => I * f (v x)) volume (-H) H := by
    have hc : 0 < rademacherPolarLine ρ := by unfold rademacherPolarLine; positivity
    have hh : Continuous v := continuous_iff_continuousAt.mpr
      (fun x => (hasDerivAt_verticalPoint (rademacherPolarLine ρ) x).continuousAt)
    apply Continuous.intervalIntegrable
    change Continuous (fun x => I * (Complex.exp ((a : ℂ) * v x + (b : ℂ) / v x) / (v x) ^ 3))
    exact continuous_const.mul ((Complex.continuous_exp.comp ((continuous_const.mul hh).add
      (continuous_const.div hh (verticalPoint_ne_zero hc)))).div (hh.pow 3)
      (fun x => pow_ne_zero _ (verticalPoint_ne_zero hc x)))
  have hA := intervalIntegral.integral_eq_sub_of_hasDerivAt hArc hIA
  have hB := intervalIntegral.integral_eq_sub_of_hasDerivAt hChord hIB
  rw [hR, hL] at hA
  rw [intervalIntegral.integral_const_mul] at hA hB
  exact mul_left_cancel₀ Complex.I_ne_zero (hA.trans hB.symm)

private theorem verticalPoint_normSq (c v : ℝ) :
    Complex.normSq (verticalPoint c v) = c ^ 2 + v ^ 2 := by
  simp [Complex.normSq_apply, verticalPoint, Complex.mul_re, Complex.mul_im, pow_two]

private theorem rademacherPolarLine_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < rademacherPolarLine ρ := by unfold rademacherPolarLine; positivity

private theorem rademacherPolarHeight_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < rademacherPolarHeight ρ := by unfold rademacherPolarHeight; positivity

private theorem inv_verticalPoint_re_le {ρ v : ℝ} (hρ : 0 < ρ)
    (hv : rademacherPolarHeight ρ ≤ |v|) : (verticalPoint (rademacherPolarLine ρ) v)⁻¹.re ≤ ρ := by
  let c := rademacherPolarLine ρ
  let H := rademacherPolarHeight ρ
  have hc : 0 < c := rademacherPolarLine_pos hρ
  have hs : H ^ 2 ≤ v ^ 2 := by
    rw [← sq_abs v]
    exact pow_le_pow_left₀ (rademacherPolarHeight_pos hρ).le hv 2
  have hR : (verticalPoint c H)⁻¹ = rademacherCuspPoint ρ (Real.sqrt ρ) := by
    rw [← rademacherCuspPoint_inv_right hρ, inv_inv]
  have hEq : c / (c ^ 2 + H ^ 2) = ρ := by
    have he := congrArg Complex.re hR
    rw [Complex.inv_re, verticalPoint_normSq] at he
    simpa [verticalPoint, Complex.mul_re] using he
  change (verticalPoint c v)⁻¹.re ≤ ρ
  rw [Complex.inv_re, verticalPoint_normSq, ← hEq]
  have hcc : (verticalPoint c v).re = c := by simp [verticalPoint, Complex.mul_re]
  rw [hcc]
  exact div_le_div_of_nonneg_left hc.le (by positivity) (add_le_add_right hs _)

private theorem polarKernel_tail_pointwise {ρ a b v : ℝ} (hρ : 0 < ρ) (hb : 0 < b)
    (hv : rademacherPolarHeight ρ ≤ |v|) :
    ‖rademacherPolarKernel a b (verticalPoint (rademacherPolarLine ρ) v)‖ ≤
      Real.exp (a * rademacherPolarLine ρ + b * ρ) * |v| ^ (-3 : ℝ) := by
  let c := rademacherPolarLine ρ
  let w := verticalPoint c v
  have hv₀ : 0 < |v| := (rademacherPolarHeight_pos hρ).trans_le hv
  have hInv : w⁻¹.re ≤ ρ := inv_verticalPoint_re_le hρ hv
  have hwre : w.re = c := by simp [w, verticalPoint, Complex.mul_re]
  have him : w.im = v := by simp [w, verticalPoint, Complex.mul_im]
  have hNorm : |v| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm _
  change ‖rademacherPolarKernel a b w‖ ≤ Real.exp (a * c + b * ρ) * |v| ^ (-3 : ℝ)
  rw [rademacherPolarKernel, norm_div, norm_pow, Complex.norm_exp, div_eq_mul_inv (b : ℂ),
    Complex.add_re, Complex.mul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.ofReal_im, zero_mul, zero_mul, sub_zero, sub_zero, hwre,
    Real.rpow_neg (abs_nonneg v), ← div_eq_mul_inv]
  refine div_le_div₀ (by positivity) (Real.exp_le_exp.mpr ?_) (by positivity) ?_
  · exact add_le_add_right (mul_le_mul_of_nonneg_left hInv hb.le) _
  · rw [Real.rpow_ofNat]
    exact pow_le_pow_left₀ (abs_nonneg _) hNorm 3

private theorem norm_integral_polar_tail_le {ρ a b : ℝ} (hρ : 0 < ρ)
    {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi (rademacherPolarHeight ρ)))
    (hg₁ : ∀ v ∈ Ioi (rademacherPolarHeight ρ),
      ‖g v‖ ≤ Real.exp (a * rademacherPolarLine ρ + b * ρ) * v ^ (-3 : ℝ)) :
    ‖∫ v in Ioi (rademacherPolarHeight ρ), g v‖ ≤
      Real.exp (a * rademacherPolarLine ρ + b * ρ) / (2 * (rademacherPolarHeight ρ) ^ 2) := by
  let H := rademacherPolarHeight ρ
  let E := Real.exp (a * rademacherPolarLine ρ + b * ρ)
  have hH : 0 < H := rademacherPolarHeight_pos hρ
  have hDom : IntegrableOn (fun v : ℝ => E * v ^ (-3 : ℝ)) (Ioi H) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hH).const_mul E
  change ‖∫ v in Ioi H, g v‖ ≤ E / (2 * H ^ 2)
  calc
    _ ≤ ∫ v in Ioi H, ‖g v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioi H, E * v ^ (-3 : ℝ) := setIntegral_mono_on hg.norm hDom measurableSet_Ioi hg₁
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hH]
      rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hH.le, Real.rpow_two]
      field_simp [hH.ne']

/-- Replacing the central cusp segment with the full vertical polar integral costs only the two
explicit cubic tails. -/
theorem norm_integral_polar_arc_sub_vertical_le {ρ a b : ℝ}
    (hρ : 0 < ρ) (ha : 0 < a) (hb : 0 < b) :
    ‖(∫ x in -Real.sqrt ρ..Real.sqrt ρ, rademacherCentralKernel ρ a b x) -
      (∫ v : ℝ, rademacherPolarKernel a b (verticalPoint (rademacherPolarLine ρ) v))‖ ≤
      Real.exp (a * rademacherPolarLine ρ + b * ρ) / (rademacherPolarHeight ρ) ^ 2 := by
  let H := rademacherPolarHeight ρ
  let E := Real.exp (a * rademacherPolarLine ρ + b * ρ)
  let f := fun v => rademacherPolarKernel a b (verticalPoint (rademacherPolarLine ρ) v)
  have hH : 0 < H := rademacherPolarHeight_pos hρ
  have hF : Integrable f := (integral_rademacherPolarKernel (rademacherPolarLine_pos hρ) ha hb).1
  have hA : ‖∫ v in Ioi H, f v‖ ≤ E / (2 * H ^ 2) := by
    refine norm_integral_polar_tail_le hρ hF.integrableOn (fun v hv => ?_)
    have hv₀ : 0 < v := hH.trans hv
    simpa only [f, abs_of_pos hv₀] using
      (polarKernel_tail_pointwise (a := a) hρ hb (le_trans (le_of_lt hv) (le_abs_self v)))
  have hB : ‖∫ v in Iic (-H), f v‖ ≤ E / (2 * H ^ 2) := by
    rw [← integral_comp_neg_Ioi]
    have hF' : Integrable (fun v => f (-v)) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hF
    refine norm_integral_polar_tail_le hρ hF'.integrableOn (fun v hv => ?_)
    have hv₀ : 0 < v := hH.trans hv
    have hbv : H ≤ |-v| := by rw [abs_neg, abs_of_pos hv₀]; exact hv.le
    simpa only [f, abs_neg, abs_of_pos hv₀] using
      (polarKernel_tail_pointwise (a := a) hρ hb hbv)
  rw [integral_rademacherCentralKernel_eq_chord hρ]
  change ‖(∫ v in -H..H, f v) - ∫ v, f v‖ ≤ E / H ^ 2
  have hD := intervalIntegral.integral_interval_add_Ioi
    (a := -H) (b := H) hF.integrableOn hF.integrableOn
  have hE := intervalIntegral.integral_Iic_add_Ioi (b := -H) hF.integrableOn hF.integrableOn
  have hEq : (∫ v in -H..H, f v) - (∫ v, f v) =
      -((∫ v in Iic (-H), f v) + (∫ v in Ioi H, f v)) := by
    rw [← hE, ← hD]
    abel
  rw [hEq, norm_neg]
  exact (norm_add_le _ _).trans ((add_le_add hB hA).trans_eq (by ring))

/-- The truncated central arc approximates the exact modified Bessel term. -/
theorem norm_integral_polar_arc_sub_bessel_le {ρ a b : ℝ}
    (hρ : 0 < ρ) (ha : 0 < a) (hb : 0 < b) :
    ‖(∫ x in -Real.sqrt ρ..Real.sqrt ρ, rademacherCentralKernel ρ a b x) -
      (2 * (π : ℂ)) * (((a / b : ℝ) : ℂ) * besselI 2 ((2 * Real.sqrt (a * b) : ℝ) : ℂ))‖ ≤
      Real.exp (a * rademacherPolarLine ρ + b * ρ) / (rademacherPolarHeight ρ) ^ 2 := by
  have hf := (integral_rademacherPolarKernel (rademacherPolarLine_pos hρ) ha hb).2
  push_cast at hf ⊢
  have hc : 2 * (π : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr pi_pos.ne')
  rw [inv_mul_eq_div, div_eq_iff hc] at hf
  rw [← mul_comm (_ : ℂ) (2 * (π : ℂ)), ← hf]
  exact norm_integral_polar_arc_sub_vertical_le hρ ha hb

theorem inv_rademacherPolarHeight_sq {ρ : ℝ} (hρ : 0 < ρ) :
    ((rademacherPolarHeight ρ) ^ 2)⁻¹ = ρ * (1 + ρ) ^ 2 := by
  unfold rademacherPolarHeight
  rw [div_pow, one_pow, one_div, inv_inv, mul_pow, Real.sq_sqrt hρ.le]

end DurfeeCCS.Step06
