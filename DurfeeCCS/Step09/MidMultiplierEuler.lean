module

public import DurfeeCCS.Step09.MidMultiplierRadius
public import DurfeeCCS.Step09.MidPoissonEuler
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-! A logarithm of the inverse square of the Euler product on the right half-plane. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06

def midEulerLog (ζ : ℂ) : ℂ := -2 * eulerProductLog ζ

theorem norm_midEulerLog_le {ζ : ℂ} (hζ : 0 < ζ.re) :
    ‖midEulerLog ζ‖ ≤ 2 * Real.exp (-ζ.re) / (1 - Real.exp (-ζ.re)) ^ 2 := by
  rw [midEulerLog, norm_mul, norm_neg, norm_ofNat, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_eulerProductLog_le hζ) (by norm_num)

theorem exp_midEulerLog {ζ : ℂ} (hζ : 0 < ζ.re) :
    Complex.exp (midEulerLog ζ) = (eulerProduct ζ ^ 2)⁻¹ := by
  rw [midEulerLog, neg_mul, Complex.exp_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
    Complex.exp_nat_mul, exp_eulerProductLog_eq hζ]

theorem log_eulerInvSq_eq_midEulerLog {ζ : ℂ} (hζ : 0 < ζ.re) (hn : ‖midEulerLog ζ‖ < Real.pi) :
    Complex.log ((eulerProduct ζ ^ 2)⁻¹) = midEulerLog ζ := by
  have h := (Complex.abs_im_le_norm (midEulerLog ζ)).trans_lt hn
  rw [← exp_midEulerLog hζ, Complex.log_exp (abs_lt.mp h).1 (abs_lt.mp h).2.le]

theorem norm_midEulerLog_lt_of_re_ge {ζ : ℂ} {X q : ℝ}
    (hX : 0 < X) (hζ : X ≤ ζ.re) (hq : q < 1) (hQ : Real.exp (-X) < q) :
    ‖midEulerLog ζ‖ < 2 * q / (1 - q) ^ 2 := by
  have hq₀ : 0 < q := (Real.exp_pos _).trans hQ
  have hE : Real.exp (-ζ.re) < q :=
    (Real.exp_le_exp.mpr (neg_le_neg hζ)).trans_lt hQ
  refine (norm_midEulerLog_le (hX.trans_le hζ)).trans_lt ?_
  have hd : 0 < 1 - q := sub_pos.mpr hq
  have he := pow_le_pow_left₀ hd.le (sub_le_sub_left hE.le 1) 2
  calc
    _ < 2 * q / (1 - Real.exp (-ζ.re)) ^ 2 :=
      div_lt_div_of_pos_right (by linarith only [hE])
        (sq_pos_of_pos (sub_pos.mpr (hE.trans hq)))
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd) he

theorem norm_midEulerLog_lt_0005 {n : ℕ} {r η : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : |η| ≤ 8) :
    ‖midEulerLog (midEtaTransform (midEtaPoint n r η))‖ < 0.0005 := by
  have hz := re_midEtaTransform_midEtaPoint_gt_843 hn hr hmax hη
  have hQ : Real.exp (-8.43) < (0.00022 : ℝ) := by
    dyadic_interval +kernel [prec := 50]
  exact (norm_midEulerLog_lt_of_re_ge (by norm_num) hz.le (by norm_num) hQ).trans (by norm_num)

theorem norm_midEulerLog_lt_tiny {n : ℕ} {r η : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : |η| ≤ 3 / 2) :
    ‖midEulerLog (midEtaTransform (midEtaPoint n r η))‖ < (10 : ℝ) ^ (-70 : ℤ) := by
  have hz := re_midEtaTransform_midEtaPoint_gt_168 hn hr hmax hη
  have h₁ : Real.exp (-7 / 3) < (1 / 10 : ℝ) := by
    dyadic_interval +kernel [prec := 32]
  have h₂ : Real.exp (-168) < (1 / 10 : ℝ) ^ (72 : ℕ) := by
    rw [show (-168 : ℝ) = ((72 : ℕ) : ℝ) * (-7 / 3) by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ h₁ (Real.exp_nonneg _) (by norm_num)
  exact (norm_midEulerLog_lt_of_re_ge (by norm_num) hz.le (by norm_num) h₂).trans (by norm_num)

end DurfeeCCS.Step09
