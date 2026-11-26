module

public import DurfeeCCS.Step09.MidPhase
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Gaussian domination on compact ranges of the inverse contour parameter. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06

theorem re_inv_pos_of_re_pos {ζ : ℂ} (hζ : 0 < ζ.re) : 0 < ζ⁻¹.re := by
  have h₀ : ζ ≠ 0 := by
    intro h
    simp [h] at hζ
  rw [Complex.inv_re]
  exact div_pos hζ (Complex.normSq_pos.mpr h₀)

/-- The real part of a quadratic exponent, controlled by completing a square. -/
theorem re_quadratic_over_le {ζ : ℂ} {a c C x : ℝ} (hc : 0 < c)
    (hlo : c ≤ ζ⁻¹.re) (hhi : ‖ζ⁻¹‖ ≤ C) :
    (((a : ℂ) + (x : ℂ) * I) ^ 2 / ζ).re ≤
      C * a ^ 2 + 2 * C ^ 2 * a ^ 2 / c - c / 2 * x ^ 2 := by
  let b := ζ⁻¹.im
  have hb : |b| ≤ C := (Complex.abs_im_le_norm _).trans hhi
  have hcC : 0 ≤ C := (norm_nonneg _).trans hhi
  have ha : ζ⁻¹.re ≤ C := (Complex.re_le_norm _).trans hhi
  have hb2 : b ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hsq : 0 ≤ c / 2 * x ^ 2 + 2 * b * a * x + 2 * b ^ 2 * a ^ 2 / c := by
    have heq : c / 2 * x ^ 2 + 2 * b * a * x + 2 * b ^ 2 * a ^ 2 / c =
        (c * x + 2 * b * a) ^ 2 / (2 * c) := by
      field_simp
      ring
    rw [heq]
    positivity
  have h₁ := mul_le_mul_of_nonneg_right ha (sq_nonneg a)
  have h₂ := mul_le_mul_of_nonneg_right hlo (sq_nonneg x)
  have h₃ := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg a)) hc.le
  rw [div_eq_mul_inv, pow_two, Complex.mul_re, Complex.mul_re, Complex.mul_im]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.mul_re, Complex.mul_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  change (a * a - x * x) * ζ⁻¹.re - (a * x + x * a) * b ≤ _
  linarith

/-- A sequence of periodized Gaussian weights admits an absolute summable majorant. -/
theorem summable_int_real_gaussian {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2)) := by
  let ζ : ℝ := 2 * Real.pi ^ 2 / c
  have hζ : 0 < ζ := by unfold ζ; positivity
  refine (thetaGaussian_absolutelyConvergent (ζ := (ζ : ℂ)) (by simpa using hζ) 0).congr fun k => ?_
  have h : ((2 * (Real.pi : ℂ) * I * (k : ℂ)) ^ 2 / (2 * (ζ : ℂ))) =
      ((-c * (k : ℝ) ^ 2 : ℝ) : ℂ) := by
    dsimp [ζ]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [thetaGaussian, zero_add, h, norm_exp, Complex.ofReal_re]

private theorem add_sq_lower (x y : ℝ) :
    x ^ 2 / 2 - y ^ 2 ≤ (x + y) ^ 2 := by
  nlinarith [sq_nonneg (x + 2 * y)]

/-- Domination of the Poisson series uniformly in one angular period. -/
theorem norm_thetaGaussian_angle_le {ζ : ℂ} {a c C θ : ℝ} {k : ℤ}
    (hc : 0 < c) (hlo : c ≤ ζ⁻¹.re) (hhi : ‖ζ⁻¹‖ ≤ C) (hθ : |θ| ≤ Real.pi) :
    ‖thetaGaussian ((a : ℂ) + ((Real.pi / 2 + θ : ℝ) : ℂ) * I) ζ k‖ ≤
      Real.exp ((C * a ^ 2 + 2 * C ^ 2 * a ^ 2 / c) / 2 +
          c * (3 * Real.pi / 2) ^ 2 / 4) *
        Real.exp (-(c * Real.pi ^ 2 / 2) * (k : ℝ) ^ 2) := by
  let x : ℝ := (2 * Real.pi) * k
  let y : ℝ := Real.pi / 2 + θ
  have hy : |y| ≤ 3 * Real.pi / 2 := by
    have h := abs_add_le (Real.pi / 2) θ
    rw [abs_of_pos (show 0 < Real.pi / 2 by positivity)] at h
    dsimp only [y]
    linarith
  have hy₂ : y ^ 2 ≤ (3 * Real.pi / 2) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hxy := (sub_le_sub_left hy₂ (x ^ 2 / 2)).trans (add_sq_lower x y)
  have hq := re_quadratic_over_le (a := a) (x := x + y) hc hlo hhi
  have harg :
      ((a : ℂ) + ((Real.pi / 2 + θ : ℝ) : ℂ) * I + 2 * (Real.pi : ℂ) * I * (k : ℂ)) ^ 2 /
          (2 * ζ) = (((a : ℂ) + ((x + y : ℝ) : ℂ) * I) ^ 2 / ζ) / 2 := by
    dsimp only [x, y]
    push_cast
    ring
  rw [thetaGaussian, harg, norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
  have hxy' := mul_le_mul_of_nonneg_left hxy (show 0 ≤ c / 4 by positivity)
  dsimp only [x] at hxy'
  linarith

/-- The angular periodized frequency term, before the Euler modular substitution. -/
def midPoissonMode (r : ℝ) (ζ : ℂ) (p : ℤ) (χ : ℝ) : ℂ :=
  exp (((Real.log r : ℂ) + (midFrequency p : ℂ) * I) ^ 2 / ζ) *
    (exp (-(χ : ℂ) ^ 2 / ζ) / pairedProduct (midModeRadius r p) χ ζ)

/-- The unnormalized weight of a frequency in (47). -/
theorem norm_exp_midFrequency_le {r : ℝ} {p : ℤ} {ζ : ℂ} {c C : ℝ}
    (hc : 0 < c) (hlo : c ≤ ζ⁻¹.re) (hhi : ‖ζ⁻¹‖ ≤ C) :
    ‖exp (((Real.log r : ℂ) + (midFrequency p : ℂ) * I) ^ 2 / ζ)‖ ≤
      Real.exp (C * (Real.log r)^2 + 2 * C^2 * (Real.log r)^2 / c +
        (c / 2) * (Real.pi / 2)^2) *
        Real.exp (-(c * Real.pi ^ 2 / 4) * (p : ℝ) ^ 2) := by
  have hx : midFrequency p = Real.pi * (p : ℝ) + Real.pi / 2 := by unfold midFrequency; ring
  have hlower := add_sq_lower (Real.pi * (p : ℝ)) (Real.pi / 2)
  have hlower' := mul_le_mul_of_nonneg_left hlower (show 0 ≤ c / 2 by positivity)
  rw [norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h := re_quadratic_over_le (a := Real.log r) (x := midFrequency p) hc hlo hhi
  rw [hx] at h ⊢
  linarith

end DurfeeCCS.Step09
