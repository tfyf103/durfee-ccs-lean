module

public import DurfeeCCS.Step08.AngularMeans
public import DurfeeCCS.Step08.ExpRemainder

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exponential error after taking an angular mean. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set

theorem norm_angularAverage_le (f : ℝ → ℂ) :
    ‖angularAverage f‖ ≤ angularMean (fun t => ‖f t‖) := by
  unfold angularAverage angularMean
  have h : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [← ofReal_ofNat, ← ofReal_mul, Complex.norm_of_nonneg (by positivity)]
  rw [norm_mul, norm_inv, h]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm (by linarith [Real.pi_pos]))
    (by positivity)

theorem norm_angularAverage_exp_sub_one_le {f : ℝ → ℂ} (hf : Continuous f)
    (hzero : angularAverage f = 0) {W : ℝ} (hW : 0 ≤ W)
    (hre : ∀ t ∈ Icc (-Real.pi) Real.pi, (f t).re ≤ W) :
    ‖angularAverage (fun t => exp (f t) - 1)‖ ≤
      (Real.exp W / 2) * angularMean (fun t => ‖f t‖ ^ 2) := by
  have he : Continuous (fun t => exp (f t) - 1) := by fun_prop
  have hid : angularAverage (fun t => exp (f t) - 1 - f t) =
      angularAverage (fun t => exp (f t) - 1) := by
    rw [angularAverage_sub (he.intervalIntegrable _ _) (hf.intervalIntegrable _ _), hzero, sub_zero]
  rw [← hid]
  refine (norm_angularAverage_le _).trans ?_
  have hC : Continuous (fun t => (Real.exp W / 2) * ‖f t‖ ^ 2) := by fun_prop
  have hF : Continuous (fun t => ‖exp (f t) - 1 - f t‖) := by fun_prop
  have hm (t : ℝ) (ht : t ∈ Icc (-Real.pi) Real.pi) :
      ‖exp (f t) - 1 - f t‖ ≤ (Real.exp W / 2) * ‖f t‖ ^ 2 := by
    calc
      _ ≤ (‖f t‖ ^ 2 / 2) * Real.exp (max 0 (f t).re) := norm_exp_sub_one_sub_le _
      _ ≤ (‖f t‖ ^ 2 / 2) * Real.exp W :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (max_le hW (hre t ht))) (by positivity)
      _ = _ := by ring
  unfold angularMean
  rw [mul_left_comm (Real.exp W / 2)]
  rw [← intervalIntegral.integral_const_mul (Real.exp W / 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (hF.intervalIntegrable _ _) (hC.intervalIntegrable _ _) hm

theorem angularMean_norm_div_sq (f : ℝ → ℂ) (z : ℂ) :
    angularMean (fun t => ‖f t / z‖ ^ 2) = (‖z‖ ^ 2)⁻¹ * angularMean (fun t => ‖f t‖ ^ 2) := by
  unfold angularMean
  simp_rw [norm_div, div_pow, div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  ring

end DurfeeCCS.Step08
