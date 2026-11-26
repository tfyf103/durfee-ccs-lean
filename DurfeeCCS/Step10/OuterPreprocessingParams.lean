module

public import DurfeeCCS.Step10.OuterPreprocessing

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Parameter majorants used before summation in Proposition 4.1. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Set DurfeeCCS.Step07

/-- A geometric summation factor for one side of the Durfee rectangle. -/
def outerGeomFactor (h u : ℝ) : ℝ := exp (-h / 2) / (1 - exp (-u))

theorem inverse_one_sub_exp_neg_le {u : ℝ} (hu : 0 < u) :
    (1 - exp (-u))⁻¹ ≤ 1 + u⁻¹ := by
  have hE : exp (-u) ≤ (1 + u)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr (by
      linarith [Real.add_one_le_exp u])
  apply (inv_le_iff_one_le_mul₀' (show 0 < 1 - exp (-u) from sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)))).mpr
  have h₁ : 0 ≤ 1 + u⁻¹ := by positivity
  calc
    _ = (1 - (1 + u)⁻¹) * (1 + u⁻¹) := by field_simp; ring
    _ ≤ _ := by gcongr

private theorem outerGeomFactor_le {y h u : ℝ} (hy : 0 < y) (hu : 0 < u)
    (hh : 2 * log y ≤ h) :
    outerGeomFactor h u ≤ (1 / y) * (1 + u⁻¹) := by
  have hw : exp (-h / 2) ≤ 1 / y := by
    rw [one_div, ← Real.exp_log hy, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [outerGeomFactor, div_eq_mul_inv]
  exact mul_le_mul hw (inverse_one_sub_exp_neg_le hu)
    (inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)).le)) (by positivity)

/-- The geometric parameter in the small-radius discard on page 44. -/
theorem smallRadius_geomFactor_lt {y X h : ℝ} (hy : 80 ≤ y)
    (hX : 0 < X) (hXy : X / y ≤ 1.00001)
    (hh : 8.76 < h) (hhLog : 2 * log y ≤ h) :
    outerGeomFactor h (sqrt (h ^ 2 + 4 * π ^ 2 / 3) / (4 * X)) < 0.47 := by
  let p := sqrt (h ^ 2 + 4 * π ^ 2 / 3)
  have hy₀ : 0 < y := by linarith
  have hh₀ : 0 < h := by linarith
  have hp : h ≤ p := Real.le_sqrt_of_sq_le (by nlinarith only [sq_nonneg π])
  have hp₀ : 0 < p := hh₀.trans_le hp
  have hp₈ : (8.76 : ℝ) ≤ p := hh.le.trans hp
  have hw := outerGeomFactor_le hy₀ (div_pos hp₀ (by positivity : 0 < 4 * X)) hhLog
  have hw₁ : (1 / y : ℝ) ≤ 1 / 80 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hy
  have hw₂ : 4 * (X / y) / p ≤ 4 * 1.00001 / 8.76 :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hXy (by norm_num)) (by norm_num) hp₈
  calc
    _ ≤ (1 / y) * (1 + (p / (4 * X))⁻¹) := hw
    _ = 1 / y + 4 * (X / y) / p := by field_simp [hp₀.ne', hy₀.ne', hX.ne']
    _ ≤ 1 / 80 + 4 * 1.00001 / 8.76 := add_le_add hw₁ hw₂
    _ < _ := by norm_num

/-- The geometric parameter in the Bessel kernel swap on page 45. -/
theorem kernelSwap_geomFactor_lt {y h : ℝ} (hy : 80 ≤ y)
    (hh : 8.76 < h) (hhLog : 2 * log y ≤ h) :
    outerGeomFactor h (sqrt (h ^ 2 + π ^ 2 / 3) / (3 * y)) < 0.355 := by
  let u := sqrt (h ^ 2 + π ^ 2 / 3)
  have hy₀ : 0 < y := by linarith
  have hh₀ : 0 < h := by linarith
  have hu₁ : h ≤ u := Real.le_sqrt_of_sq_le (by nlinarith only [sq_nonneg π])
  have hu₀ : 0 < u := hh₀.trans_le hu₁
  have hw := outerGeomFactor_le hy₀ (div_pos hu₀ (by positivity : 0 < 3 * y)) hhLog
  have hw₁ : (1 / y : ℝ) ≤ 1 / 80 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hy
  have hw₂ : (3 : ℝ) / u ≤ 3 / 8.76 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (hh.le.trans hu₁)
  calc
    _ ≤ (1 / y) * (1 + (u / (3 * y))⁻¹) := hw
    _ = 1 / y + 3 / u := by field_simp [hu₀.ne', hy₀.ne']
    _ ≤ 1 / 80 + 3 / 8.76 := add_le_add hw₁ hw₂
    _ < _ := by norm_num

/-- Difference between the main Bessel exponential rate and the replacement error rate. -/
theorem outerRho_re_sub_replacementSlope_gt {h : ℝ} (hh : 8.76 < h) :
    2 * π ^ 2 / (5 * h) < (outerRho h π).re - sqrt (h ^ 2 + π ^ 2 / 3) := by
  let a := (outerRho h π).re
  let b := (outerRho h π).im
  let u := sqrt (h ^ 2 + π ^ 2 / 3)
  let p := sqrt (h ^ 2 + 4 * π ^ 2 / 3)
  have hh₀ : 0 < h := by linarith
  have ha : h < a := outerRho_re_gt hh₀
  have ha₀ : 0 < a := hh₀.trans ha
  have hb : 0 < b := outerRho_im_pi_pos hh₀
  have hu₀ : 0 < u := by dsimp [u]; positivity
  have hp₀ : 0 < p := by dsimp [p]; positivity
  have hπ := Real.pi_lt_d4
  have hπ₂ := pow_le_pow_left₀ pi_pos.le hπ.le 2
  have hh₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8.76) hh.le 2
  have hp : p ≤ 1.084 * h := by
    dsimp only [p]
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [hπ₂, hh₂]
  have hu : u ≤ 1.022 * h := by
    dsimp only [u]
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [hπ₂, hh₂]
  have hap : a ≤ p := by
    have h := outerRhoAt_re_gap_pos (t := π) hh₀
      (show 0 < 4 * π ^ 2 / 3 by positivity) Real.pi_ne_zero
    change 0 < p - a at h
    linarith
  have ha₁ : a ≤ 1.084 * h := hap.trans hp
  have hb₁ : π / 1.084 ≤ b := by
    unfold b
    rw [outerRho_im_eq hh₀]
    apply (le_div_iff₀ ha₀).mpr
    have h := mul_le_mul_of_nonneg_left ha₁ (show 0 ≤ π / 1.084 by positivity)
    exact h.trans_eq (by ring)
  have hu₂ : u ^ 2 = h ^ 2 + π ^ 2 / 3 := Real.sq_sqrt (by positivity)
  have hsq : a ^ 2 - b ^ 2 = h ^ 2 + π ^ 2 / 3 := by
    have h := outerRhoAt_re_sq_sub_im_sq h π (4 * π ^ 2 / 3)
    change a ^ 2 - b ^ 2 = _ at h
    nlinarith only [h]
  have hgap : a - u = b ^ 2 / (a + u) := by
    apply (eq_div_iff (by positivity : a + u ≠ 0)).mpr
    nlinarith only [hsq, hu₂]
  have hs : a + u ≤ 2.106 * h := by linarith only [ha₁, hu]
  change 2 * π ^ 2 / (5 * h) < a - u
  rw [hgap]
  calc
    _ < (π / 1.084) ^ 2 / (2.106 * h) := by
      have hπ₂p := sq_pos_of_pos Real.pi_pos
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      rw [show 2 * π ^ 2 * (2.106 * h) = (2 * 2.106) * (π ^ 2 * h) by ring,
        show (π / 1.084) ^ 2 * (5 * h) = (5 / 1.084 ^ 2) * (π ^ 2 * h) by ring]
      exact mul_lt_mul_of_pos_right (by norm_num) (mul_pos hπ₂p hh₀)
    _ ≤ _ := div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) hb₁ 2) (by positivity) hs

end DurfeeCCS.Step10
