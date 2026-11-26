module

public import DurfeeCCS.Step06.Saddle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The exact real and imaginary components of the saddle in (7). -/

@[expose] public section

namespace DurfeeCCS.Step06

open Complex MeasureTheory Set
open scoped Interval Real

private theorem negImag_mem_dilogCut (r : ℝ) : -(r : ℂ) * I ∈ dilogCut := by
  exact mem_dilogCut_iff.mpr (Or.inl (by simp))

private theorem negSquare_mem_dilogCut (r : ℝ) : -(r : ℂ)^2 ∈ dilogCut := by
  exact mem_dilogCut_iff.mpr (Or.inl (by rw [← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re]; nlinarith))

private theorem log_norm_negImag_segment (r t : ℝ) :
    Real.log ‖1 - (t : ℂ) * (-(r : ℂ) * I)‖ = Real.log (1 + t^2 * r^2) / 2 := by
  have hnorm : ‖1 - (t : ℂ) * (-(r : ℂ) * I)‖^2 = 1 + t^2 * r^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [← hnorm, Real.log_pow]
  ring

/-- The real component on the imaginary axis via the substitution u = t^2. -/
theorem principalDilog_negImag_re (r : ℝ) :
    (principalDilog (-(r : ℂ) * I)).re = (principalDilog (-(r : ℂ)^2)).re / 4 := by
  let g : ℝ → ℝ := fun t => (dilogKernel (-(r : ℂ)^2) t).re
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_dilogKernel (negSquare_mem_dilogCut r))
  have hgc : ContinuousOn g ((fun t : ℝ => t^2) '' uIcc 0 1) := by
    apply hg.mono
    rintro _ ⟨t, ht, rfl⟩
    rw [uIcc_of_le zero_le_one] at ht
    exact ⟨sq_nonneg _, pow_le_one₀ ht.1 ht.2⟩
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := 1) (g := g) (f := fun t => t^2) (f' := fun t => 2*t)
    (fun t _ => by
      have h : HasDerivAt (fun u : ℝ => u^2) _ t := (hasDerivAt_id t).pow 2
      simpa using h)
    (by fun_prop) hgc
  have hkernel (t : ℝ) (_ht : t ∈ uIcc (0 : ℝ) 1) :
      (dilogKernel (-(r : ℂ) * I) t).re = g (t^2) * (2*t) * (1/4) := by
    by_cases ht0 : t = 0
    · subst t
      simp [dilogKernel]
    have ht2 : t^2 ≠ 0 := pow_ne_zero _ ht0
    have he : 1 - ((t^2 : ℝ) : ℂ) * (-(r : ℂ)^2) = ((1 + t^2*r^2 : ℝ) : ℂ) := by
      push_cast
      ring
    simp only [g, dilogKernel, ite_eq_right ht0, ite_eq_right ht2, Complex.div_ofReal_re,
      Complex.neg_re]
    rw [Complex.log_re, log_norm_negImag_segment, he, Complex.log_ofReal_re]
    field_simp
    ring
  have h1 : (∫ t in (0 : ℝ)..1, (dilogKernel (-(r : ℂ) * I) t).re) =
      (principalDilog (-(r : ℂ) * I)).re :=
    Complex.reCLM.intervalIntegral_comp_comm (intervalIntegrable_dilogKernel (negImag_mem_dilogCut r))
  have h2 : (∫ t in (0 : ℝ)..1, g t) = (principalDilog (-(r : ℂ)^2)).re :=
    Complex.reCLM.intervalIntegral_comp_comm (intervalIntegrable_dilogKernel (negSquare_mem_dilogCut r))
  rw [← h1, ← h2]
  calc
    _ = ∫ t in (0 : ℝ)..1, g (t^2) * (2*t) * (1/4) := intervalIntegral.integral_congr hkernel
    _ = _ := by
      rw [intervalIntegral.integral_mul_const]
      have hs : (∫ t in (0 : ℝ)..1, g (t^2) * (2*t)) = ∫ t in (0 : ℝ)..1, g t := by simpa using hsub
      rw [hs]
      ring

private theorem arg_negImag_segment (r t : ℝ) :
    Complex.arg (1 - (t : ℂ) * (-(r : ℂ) * I)) = Real.arctan (t*r) := by
  let w : ℂ := 1 - (t : ℂ) * (-(r : ℂ) * I)
  have hre : w.re = 1 := by simp [w, Complex.mul_re, Complex.mul_im]
  have him : w.im = t*r := by simp [w, Complex.mul_re, Complex.mul_im]
  have h := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; norm_num)))
  calc
    _ = Real.arctan (Real.tan w.arg) := (Real.arctan_tan h.1 h.2).symm
    _ = _ := by rw [Complex.tan_arg, hre, him, div_one]

/-- The imaginary component on the imaginary axis as the real arctangent integral. -/
theorem principalDilog_negImag_im {r : ℝ} (hr : 0 < r) :
    (principalDilog (-(r : ℂ) * I)).im = -(∫ y in (0 : ℝ)..r, Real.arctan y / y) := by
  let f : ℝ → ℝ := fun y => Real.arctan y / y
  change _ = -(∫ y in (0 : ℝ)..r, f y)
  have hKernel (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      (dilogKernel (-(r : ℂ) * I) t).im = -(r * f (t*r)) := by
    simp only [dilogKernel, ite_eq_right ht.1.ne', Complex.div_ofReal_im, Complex.neg_im,
      Complex.log_im, arg_negImag_segment, f]
    field_simp [ht.1.ne', hr.ne']
  have h1 : (∫ t in (0 : ℝ)..1, (dilogKernel (-(r : ℂ) * I) t).im) =
      (principalDilog (-(r : ℂ) * I)).im :=
    Complex.imCLM.intervalIntegral_comp_comm (intervalIntegrable_dilogKernel (negImag_mem_dilogCut r))
  rw [← h1]
  calc
    _ = ∫ t in (0 : ℝ)..1, -(r * f (t*r)) := by
      simp only [intervalIntegral.integral_of_le zero_le_one]
      exact setIntegral_congr_fun measurableSet_Ioc hKernel
    _ = _ := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
      change -(r • (∫ t in (0 : ℝ)..1, f (t*r))) = _
      rw [intervalIntegral.smul_integral_comp_mul_right f r, zero_mul, one_mul]

/-- The principal dilogarithm is real at real arguments strictly below the cut. -/
theorem principalDilog_ofReal_im {x : ℝ} (hx : x < 1) :
    (principalDilog (x : ℂ)).im = 0 := by
  have hxcut : (x : ℂ) ∈ dilogCut := mem_dilogCut_iff.mpr (Or.inl (by simpa using hx))
  have him : (∫ t in (0 : ℝ)..1, (dilogKernel (x : ℂ) t).im) =
      (principalDilog (x : ℂ)).im :=
    Complex.imCLM.intervalIntegral_comp_comm (intervalIntegrable_dilogKernel hxcut)
  rw [← him]
  calc
    _ = ∫ t in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      by_cases h0 : t = 0
      · subst t
        simp [dilogKernel]
      have hp := one_sub_scaled_mem_slitPlane hxcut (by simpa using ht)
      have hpos : 0 < 1 - t*x := by
        simpa [Complex.mem_slitPlane_iff, Complex.mul_re, Complex.mul_im] using hp
      have hlog : Complex.log (1 - (t : ℂ) * (x : ℂ)) = (Real.log (1-t*x) : ℂ) := by
        simpa using (Complex.ofReal_log hpos.le).symm
      simp [dilogKernel, h0, hlog]
    _ = _ := by simp

/-- The real component on the imaginary axis in the original integration variable. -/
theorem principalDilog_negImag_re_integral {r : ℝ} (hr : 0 < r) :
    (principalDilog (-(r : ℂ) * I)).re = -(∫ y in (0 : ℝ)..r, Real.log (1+y^2) / y) / 2 := by
  let f : ℝ → ℝ := fun y => Real.log (1+y^2) / y
  change _ = -(∫ y in (0 : ℝ)..r, f y) / 2
  have hKernel (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      (dilogKernel (-(r : ℂ) * I) t).re = -(r * f (t*r)) / 2 := by
    simp only [dilogKernel, ite_eq_right ht.1.ne', Complex.div_ofReal_re, Complex.neg_re,
      Complex.log_re, log_norm_negImag_segment, f, mul_pow]
    field_simp [ht.1.ne', hr.ne']
  have h1 : (∫ t in (0 : ℝ)..1, (dilogKernel (-(r : ℂ) * I) t).re) =
      (principalDilog (-(r : ℂ) * I)).re :=
    Complex.reCLM.intervalIntegral_comp_comm (intervalIntegrable_dilogKernel (negImag_mem_dilogCut r))
  rw [← h1]
  calc
    _ = ∫ t in (0 : ℝ)..1, -(r * f (t*r)) / 2 := by
      simp only [intervalIntegral.integral_of_le zero_le_one]
      exact setIntegral_congr_fun measurableSet_Ioc hKernel
    _ = _ := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_neg,
        intervalIntegral.integral_const_mul]
      change -(r • (∫ t in (0 : ℝ)..1, f (t*r))) / 2 = _
      rw [intervalIntegral.smul_integral_comp_mul_right f r, zero_mul, one_mul]

/-- Before taking the square root, the two components are the stated log and arctangent integrals. -/
theorem saddlePhaseSquare_integral_components {r : ℝ} (hr : 0 < r) :
    (saddlePhaseSquare r).re = (∫ y in (0 : ℝ)..r, Real.log (1 + y^2) / y) ∧
    (saddlePhaseSquare r).im = 2 * ∫ y in (0 : ℝ)..r, Real.arctan y / y := by
  constructor
  · simp only [saddlePhaseSquare, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.re_ofNat, Complex.im_ofNat, neg_zero, zero_mul, sub_zero]
    rw [principalDilog_negImag_re_integral hr]
    ring
  · simp only [saddlePhaseSquare, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.re_ofNat, Complex.im_ofNat, neg_zero, zero_mul, add_zero]
    rw [principalDilog_negImag_im hr]
    ring

/-- The real and imaginary parts of the principal square root satisfy equation (7). -/
theorem saddleS_components_eq {r : ℝ} (hr : 0 < r) :
    (saddleS r).re^2 - (saddleS r).im^2 = -(principalDilog (-(r : ℂ)^2)).re / 2 ∧
    2 * (saddleS r).re * (saddleS r).im = 2 * ∫ y in (0 : ℝ)..r, Real.arctan y / y := by
  have hre := congrArg Complex.re (saddleS_sq r)
  rw [pow_two, Complex.mul_re, ← pow_two, ← pow_two] at hre
  have him := congrArg Complex.im (saddleS_sq r)
  rw [pow_two, Complex.mul_im] at him
  constructor
  · rw [hre]
    simp only [saddlePhaseSquare, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.re_ofNat, Complex.im_ofNat, neg_zero, zero_mul, sub_zero]
    rw [principalDilog_negImag_re]
    ring
  · calc
      _ = (saddleS r).re * (saddleS r).im + (saddleS r).im * (saddleS r).re := by ring
      _ = (saddlePhaseSquare r).im := him
      _ = _ := (saddlePhaseSquare_integral_components hr).2

end DurfeeCCS.Step06
