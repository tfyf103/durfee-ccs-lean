module

public import DurfeeCCS.Step09.MidPhaseSymmetry
public import DurfeeCCS.Step07.MidSaddleTail
public import Mathlib.Analysis.Asymptotics.Lemmas

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The logarithmic asymptote of the middle saddle, and its imaginary limit. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step09

open Complex Filter Asymptotics DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08
open scoped Topology

def midSaddleLogShift (r : ℝ) : ℂ := (Real.log r : ℂ) + (Real.pi : ℂ) / 2 * I

@[simp] theorem midSaddleLogShift_re (r : ℝ) : (midSaddleLogShift r).re = Real.log r := by
  unfold midSaddleLogShift
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div]
  simp [Complex.mul_re]

@[simp] theorem midSaddleLogShift_im (r : ℝ) : (midSaddleLogShift r).im = Real.pi / 2 := by
  unfold midSaddleLogShift
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div]
  simp [Complex.mul_im]

theorem norm_saddleS_sub_logShift_le {r : ℝ} (hr : 1 < r) :
    ‖saddleS r - midSaddleLogShift r‖ ≤ (2 * Real.pi ^ 2 / 3) / Real.log r := by
  have hr' : 0 < r := by linarith
  have ht : 0 < Real.log r := Real.log_pos hr
  let q := midSaddleLogShift r
  have hLower : Real.log r ≤ ‖saddleS r + q‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.add_re, q, midSaddleLogShift_re]
    exact le_add_of_nonneg_left ((saddleS_components hr').1.trans (saddleS_components hr').2).le
  have hDiff :
      (saddleS r - q) * (saddleS r + q) =
        (Real.pi : ℂ) ^ 2 / 3 + 2 * principalDilog ((r⁻¹ : ℝ) * I) := by
    rw [show (saddleS r - q) * (saddleS r + q) = saddleS r ^ 2 - q ^ 2 by ring,
      saddleS_sq_inv_radius hr']
    change q ^ 2 + _ + _ - q ^ 2 = _
    ring
  have hI : |-r⁻¹| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr hr'.le)]
    exact inv_le_one_of_one_le₀ hr.le
  have hG : saddleG (-r⁻¹) 0 = -(2 * principalDilog ((r⁻¹ : ℝ) * I)) := by
    simp only [saddleG, Complex.ofReal_neg, neg_neg, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one, neg_zero]
    ring
  have hD := (norm_saddleG_le hI 0).trans
    (mul_le_of_le_one_right (by positivity : 0 ≤ Real.pi ^ 2 / 3) hI)
  have hZ :
      ‖(Real.pi : ℂ) ^ 2 / 3 + 2 * principalDilog ((r⁻¹ : ℝ) * I)‖ ≤
        2 * Real.pi ^ 2 / 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_pow, norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hG, norm_neg] at hD
    linarith only [hD]
  apply (le_div_iff₀ ht).mpr
  exact (mul_le_mul_of_nonneg_left hLower (norm_nonneg _)).trans
    (by rw [← norm_mul, hDiff]; exact hZ)

theorem saddleS_sub_logShift_isBigO :
    (fun r : ℝ => saddleS r - midSaddleLogShift r) =O[atTop]
      (fun r => (Real.log r)⁻¹) := by
  apply IsBigO.of_bound (2 * Real.pi ^ 2 / 3)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have h : 1 < r := by linarith
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.log_nonneg h.le)), ← div_eq_mul_inv]
  exact norm_saddleS_sub_logShift_le h

theorem tendsto_im_saddleS_pi_half :
    Tendsto (fun r : ℝ => (saddleS r).im) atTop (𝓝 (Real.pi / 2)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hInv : Tendsto (fun r : ℝ => (Real.log r)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have ht : Tendsto (fun r : ℝ => (2 * Real.pi ^ 2 / 3) / Real.log r) atTop (𝓝 0) := by
    rw [show (fun r : ℝ => (2 * Real.pi ^ 2 / 3) / Real.log r) =
      fun r : ℝ => (2 * Real.pi ^ 2 / 3) * (Real.log r)⁻¹ from funext fun _ => div_eq_mul_inv _ _]
    simpa only [mul_zero] using hInv.const_mul (2 * Real.pi ^ 2 / 3)
  refine squeeze_zero' (.of_forall (fun _ => norm_nonneg _)) ?_ ht
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have h : 1 < r := by linarith
  refine le_trans ?_ (norm_saddleS_sub_logShift_le h)
  simpa only [Real.norm_eq_abs, Complex.sub_im, midSaddleLogShift_im] using
    Complex.abs_im_le_norm (saddleS r - midSaddleLogShift r)

theorem saddleS_im_lt_pi_half_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    (saddleS r).im < Real.pi / 2 := by
  have h := saddleS_exp_im_lt_pi_half (Real.log_nonneg hr)
  simpa only [Real.exp_log (by linarith : 0 < r)] using h

end DurfeeCCS.Step09
