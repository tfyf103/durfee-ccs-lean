module

public import DurfeeCCS.Step08.AngularErrors
public import DurfeeCCS.Step08.NearOriginLaplace
public import DurfeeCCS.Step08.PhaseGapComponents
public import DurfeeCCS.Step08.PhaseGapParameters
public import DurfeeCCS.Step08.SaddleModelIntegral
public import DurfeeCCS.Step08.SaddleFourier
public import DurfeeCCS.Step08.SaddleNormalization
public import DurfeeCCS.Step08.VerticalTail

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The outer tail of the vertical Bessel contour in (40). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07

private theorem angularAverage_saddleG_div {r : ℝ} (hr : |r| ≤ 1) (z : ℂ) :
    angularAverage (fun θ => saddleG r θ / z) = 0 := by
  simp only [div_eq_mul_inv, mul_comm (saddleG r _) _, angularAverage_const_mul,
    angularAverage_saddleG r hr, mul_zero]

theorem re_saddleG_div_outer {r u v : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hu : 0 < u) (hv : 16 * u ≤ |v|) (θ : ℝ) :
    (saddleG r θ / verticalPoint u v).re ≤ 0.127 * ((saddleS r).re ^ 2 / u) := by
  let a := (saddleS r).re
  have hr' : |r| ≤ 1 := by rwa [abs_of_pos hr]
  have ha : r ≤ a ^ 2 := (firstSaddle_coordinates_bounds hr hr₁).1
  have hsq : r ^ 2 ≤ r := by nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr₁)]
  have hR θ : (saddleG r θ).re ≤ r ^ 2 / 2 := by
    have h := (saddleG_component_gaps hr hr₁ θ).1
    have hb := saddlePhaseSquare_re_le_sq_half hr
    rw [saddleS_sq] at h
    have hp : 0 ≤ r ^ 2 / (1 + r ^ 2) * Real.sin θ ^ 2 := by positivity
    linarith only [h,hb,hp]
  have hI θ : (saddleG r θ).im ≤ 2 * r := by
    have h := (saddleG_component_gaps hr hr₁ θ).2
    have hb := saddlePhaseSquare_im_le_twice hr
    rw [saddleS_sq] at h
    have hp : 0 ≤ 2 * r / (1 + r ^ 2) * (1 - Real.cos θ) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one θ))
    linarith only [h,hb,hp]
  have habs : |(saddleG r θ).im| ≤ 2 * r := by
    apply abs_le.mpr ⟨?_, hI θ⟩
    have h := hI (θ + Real.pi)
    rw [saddleG_add_pi hr', Complex.conj_im] at h
    linarith only [h]
  have hn : 0 < u ^ 2 + v ^ 2 := by positivity
  rw [Complex.div_re, Complex.normSq_apply, verticalPoint_re, verticalPoint_im,
    ← pow_two, ← pow_two, ← add_div]
  apply (div_le_iff₀ hn).mpr
  have hRterm : (saddleG r θ).re * u ≤ a ^ 2 / 2 * u :=
    mul_le_mul_of_nonneg_right ((hR θ).trans (by linarith only [hsq,ha])) hu.le
  have hIterm : (saddleG r θ).im * v ≤ 2 * a ^ 2 * |v| := by
    calc
      _ ≤ |(saddleG r θ).im * v| := le_abs_self _
      _ = |(saddleG r θ).im| * |v| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (habs.trans (by linarith only [ha])) (abs_nonneg v)
  have hratio : (0.5 : ℝ) * u ^ 2 + 2 * u * |v| ≤ 0.127 * (u ^ 2 + v ^ 2) := by
    nlinarith only [sq_abs v, sq_nonneg (|v| - 16 * u), sq_nonneg u,
      mul_nonneg hu.le (sub_nonneg.mpr hv)]
  have hscaled := mul_le_mul_of_nonneg_left hratio (show 0 ≤ a ^ 2 / u by positivity)
  change (saddleG r θ).re * u + (saddleG r θ).im * v ≤
    0.127 * (a ^ 2 / u) * (u ^ 2 + v ^ 2)
  calc
    _ ≤ a ^ 2 / 2 * u + 2 * a ^ 2 * |v| := add_le_add hRterm hIterm
    _ = (a ^ 2 / u) * (0.5 * u ^ 2 + 2 * u * |v|) := by field_simp; ring
    _ ≤ _ := by linarith only [hscaled]

theorem norm_saddleExponentialMean_outer {r u v : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hu : 0 < u) (hv : 16 * u ≤ |v|) :
    ‖saddleExponentialMean r u v‖ ≤
      1.085 * r ^ 2 * Real.exp (0.127 * ((saddleS r).re ^ 2 / u)) / (u ^ 2 + v ^ 2) := by
  have hr' : |r| ≤ 1 := by rwa [abs_of_pos hr]
  unfold saddleExponentialMean
  have h := norm_angularAverage_exp_sub_one_le ((continuous_saddleG hr').div_const
      (verticalPoint u v)) (angularAverage_saddleG_div hr' _)
      (W := 0.127 * ((saddleS r).re ^ 2 / u)) (by positivity)
      (fun θ _ => re_saddleG_div_outer hr hr₁ hu hv θ)
  rw [angularMean_norm_div_sq, norm_verticalPoint_sq] at h
  refine h.trans ?_
  have hmul := mul_le_mul_of_nonneg_left (angularMean_norm_sq_saddleG_le hr.le hr₁)
    (show 0 ≤ Real.exp (0.127 * ((saddleS r).re ^ 2 / u)) / 2 * (u ^ 2 + v ^ 2)⁻¹
      by positivity)
  calc
    _ = (Real.exp (0.127 * ((saddleS r).re ^ 2 / u)) / 2 *
        (u ^ 2 + v ^ 2)⁻¹) * angularMean (fun θ => ‖saddleG r θ‖ ^ 2) := by ring
    _ ≤ _ := hmul
    _ = _ := by ring

theorem integral_norm_saddleExponentialMean_outer {r u : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hu : 0 < u) :
    (∫ v in (Icc (-(16 * u)) (16 * u))ᶜ, ‖saddleExponentialMean r u v‖) ≤
      1.085 * r ^ 2 * Real.exp (0.127 * ((saddleS r).re ^ 2 / u)) * (2 / (16 * u)) := by
  let C := 1.085 * r ^ 2 * Real.exp (0.127 * ((saddleS r).re ^ 2 / u))
  let s := (Icc (-(16 * u)) (16 * u))ᶜ
  have hr' : |r| ≤ 1 := by rwa [abs_of_pos hr]
  have hi : IntegrableOn (fun v => ‖saddleExponentialMean r u v‖) s := by
    simpa using (integrable_saddleExponentialMean hr' hu 0).norm.integrableOn (s := s)
  have hbound := (integrable_cauchy_density hu).const_mul C
  calc
    _ ≤ ∫ v in s, C * (u ^ 2 + v ^ 2)⁻¹ := by
      apply setIntegral_mono_on hi hbound.integrableOn measurableSet_Icc.compl
      intro v hv
      apply norm_saddleExponentialMean_outer hr hr₁ hu
      exact (not_lt.mp (fun h => hv (abs_le.mp h.le)))
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_cauchy_density_tail_le hu (by positivity))
        (by dsimp [C]; positivity)

/-- The full Bessel tail in (40), bounded by the certified `L₁₆` expression. -/
theorem saddle_tail_error_le {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    let ω := saddleOmega n r
    let u := saddleU n r
    Real.exp ω / (2 * Real.pi) *
        (∫ v in (Icc (-(16 * u)) (16 * u))ᶜ, ‖saddleExponentialMean r u v‖) ≤
      saddleAmplitude n r * firstSaddleL16 ω := by
  dsimp only
  let ω := saddleOmega n r
  let u := saddleU n r
  have hu : 0 < u := saddleU_pos hn hr
  have hw : 0 < ω := saddleOmega_pos hn hr
  have ha : (saddleS r).re ^ 2 / u = ω := by
    rw [← saddleU_mul_omega hn r, mul_comm, mul_div_cancel_right₀ _ hu.ne']
  have h := integral_norm_saddleExponentialMean_outer hr hr₁ hu
  rw [ha] at h
  have hC : 0 ≤ (1.085 / 8 : ℝ) := by norm_num
  change Real.exp ω / (2 * Real.pi) * _ ≤ saddleAmplitude n r * firstSaddleL16 ω
  calc
    _ ≤ Real.exp ω / (2 * Real.pi) *
        (1.085 * r ^ 2 * Real.exp (0.127 * ω) * (2 / (16 * u))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = Real.exp ω / (2 * Real.pi) *
        ((1.085 / 8) * r ^ 2 / u * Real.exp (0.127 * ω)) := by ring
    _ ≤ saddleAmplitude n r * (3 * (1.085 / 8) / 4 * ω ^ 3 *
        Real.exp (-(1 - 0.127) * ω)) :=
      saddle_scale_weighted_error_le hn hr hr₁ hC
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (saddleAmplitude_pos hn hr).le
      unfold firstSaddleL16
      rw [show (-(1 - 0.127) : ℝ) = -0.873 by norm_num]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hw.le 3)) (Real.exp_nonneg _)

end DurfeeCCS.Step08
