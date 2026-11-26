module

public import DurfeeCCS.Step09.MidPhase
public import DurfeeCCS.Step08.PhaseGapComponents
public import DurfeeCCS.Step08.SaddleBesselAverage

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Dilogarithm inversion and conjugacy for the middle saddle. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step08
open scoped ComplexConjugate

theorem saddleS_sq_inv_radius {r : ℝ} (hr : 0 < r) :
    saddleS r ^ 2 = ((Real.log r : ℂ) + (Real.pi : ℂ) / 2 * I) ^ 2 +
      (Real.pi : ℂ) ^ 2 / 3 + 2 * principalDilog ((r⁻¹ : ℝ) * I) := by
  let z : ℂ := -(r : ℂ) * I
  have hz : z ∈ dilogInvCut := by
    apply mem_dilogInvCut_iff.mpr
    right
    simpa [z, Complex.mul_im] using hr.ne'
  have hlog : log (-z) = (Real.log r : ℂ) + (Real.pi : ℂ) / 2 * I := by
    rw [show -z = (r : ℂ) * I by unfold z; ring]
    rw [Complex.log_ofReal_mul hr I_ne_zero, Complex.log_I]
  have hzInv : z⁻¹ = (r⁻¹ : ℝ) * I := by
    have hC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    rw [Complex.ofReal_inv]
    apply inv_eq_of_mul_eq_one_right
    change (-(r : ℂ) * I) * ((r : ℂ)⁻¹ * I) = 1
    calc
      _ = -((r : ℂ) * (r : ℂ)⁻¹) * I ^ 2 := by ring
      _ = _ := by rw [mul_inv_cancel₀ hC, Complex.I_sq]; norm_num
  have h := principalDilog_inversion hz
  rw [hlog, hzInv] at h
  rw [saddleS_sq, saddlePhaseSquare]
  change -2 * principalDilog z = _
  linear_combination -2 * h

theorem saddleG_neg_radius_eq_shift (t χ : ℝ) :
    saddleG (-t) χ = saddleG t (χ + Real.pi) := by
  have hp : exp (((χ + Real.pi : ℝ) : ℂ) * I) = -exp ((χ : ℂ) * I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
  have hm : exp (-((χ + Real.pi : ℝ) : ℂ) * I) = -exp (-(χ : ℂ) * I) := by
    rw [Complex.ofReal_add, neg_add, add_mul, Complex.exp_add, neg_mul (Real.pi : ℂ),
      Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, mul_neg_one]
  unfold saddleG
  rw [hp, hm]
  simp only [Complex.ofReal_neg, neg_neg, mul_neg, neg_mul]

theorem saddleG_neg_radius_conj {t : ℝ} (ht : |t| ≤ 1) (χ : ℝ) :
    saddleG (-t) χ = conj (saddleG t χ) := by
  rw [saddleG_neg_radius_eq_shift, saddleG_add_pi ht]

theorem midModeRadius_phase_re {r : ℝ} (hr : 1 ≤ r) (p : ℤ) (χ : ℝ) :
    (saddleG (midModeRadius r p) χ).re = (saddleG r⁻¹ χ).re := by
  have ht : |r⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ hr
  unfold midModeRadius
  split <;> simp [saddleG_neg_radius_conj ht]

theorem saddleG_im_abs_le_origin {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (χ : ℝ) :
    |(saddleG t χ).im| ≤ (saddleG t 0).im := by
  have ha (θ : ℝ) : (saddleG t θ).im ≤ (saddleG t 0).im := by
    have h := (saddleG_component_gaps ht ht₁ θ).2
    rw [← saddleG_zero] at h
    have hp : 0 ≤ 2 * t / (1 + t ^ 2) * (1 - Real.cos θ) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one θ))
    linarith only [h,hp]
  apply abs_le.mpr ⟨?_, ha χ⟩
  have h := ha (χ + Real.pi)
  rw [saddleG_add_pi (by simpa [abs_of_pos ht] using ht₁), Complex.conj_im] at h
  linarith only [h]

theorem midModeRadius_phase_im {r : ℝ} (hr : 1 ≤ r) (p : ℤ) (χ : ℝ) :
    |(saddleG (midModeRadius r p) χ).im| ≤ (saddleG r⁻¹ 0).im := by
  have ht : 0 < r⁻¹ := by positivity
  have ht₁ := inv_le_one_of_one_le₀ hr
  have habs : |r⁻¹| ≤ 1 := by simpa [abs_of_pos ht] using ht₁
  unfold midModeRadius
  split <;> simpa [saddleG_neg_radius_conj habs] using saddleG_im_abs_le_origin ht ht₁ χ

@[simp] theorem midFrequency_zero : midFrequency 0 = Real.pi / 2 := by
  simp [midFrequency, div_eq_mul_inv]

@[simp] theorem midFrequency_neg_one : midFrequency (-1) = -(Real.pi / 2) := by
  unfold midFrequency
  push_cast
  ring

theorem midPhase_zero_value {r : ℝ} (hr : 0 < r) :
    midPhase r 0 0 = saddleS r ^ 2 := by
  rw [midPhase, midFrequency_zero, midModeRadius_zero, saddleS_sq_inv_radius hr]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_zero, zero_pow
    (by decide : 2 ≠ 0), sub_zero, saddleG, Complex.exp_zero, neg_zero, zero_mul, mul_one,
    Complex.ofReal_neg, neg_neg]
  ring

theorem midPhase_conj {r : ℝ} (hr : 1 ≤ r) (χ : ℝ) :
    midPhase r (-1) χ = conj (midPhase r 0 χ) := by
  have ht : |r⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ hr
  simp only [midPhase, midFrequency_zero, midFrequency_neg_one, midModeRadius_neg_one,
    midModeRadius_zero, saddleG_neg_radius_conj ht, map_sub, map_add, map_mul, map_pow,
    Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_ofNat, Complex.ofReal_neg]
  ring

theorem midPhase_neg_one_value {r : ℝ} (hr : 1 ≤ r) :
    midPhase r (-1) 0 = conj (saddleS r ^ 2) := by
  rw [midPhase_conj hr, midPhase_zero_value (by positivity)]

end DurfeeCCS.Step09
