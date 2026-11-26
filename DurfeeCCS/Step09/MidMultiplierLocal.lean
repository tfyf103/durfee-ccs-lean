module

public import DurfeeCCS.Step09.MidMultiplierRay
public import DurfeeCCS.Step09.MidMultiplierUniform

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Logarithmic and multiplicative error on the central rectangle, equation (56). -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

/-- The logarithmic multiplier bound in (56), with t the reciprocal radius. -/
def midLocalLogBound (u t h : ℝ) : ℝ :=
  (13 / 16) * theta38K h * t * u + Real.sqrt (13 / 4) * u / 12 + 1 / 10 ^ 20

private theorem theta38K_nonneg {h : ℝ} (hh : h ≤ Real.pi / 2) : 0 ≤ theta38K h := by
  have hb : 1 ≤ Real.exp (2 * ((Real.pi / 2 - h) / 2) / 3) :=
    Real.one_le_exp_iff.mpr (by linarith)
  unfold theta38K
  positivity

private theorem theta38K_le_nineteen {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1) :
    theta38K h ≤ 19 := by
  let d : ℝ := (Real.pi / 2 - h) / 2
  have hd : (0.285 : ℝ) ≤ d := by dsimp [d]; linarith [Real.pi_gt_d4]
  have hd' : d ≤ Real.pi / 2 := by dsimp [d]; linarith [Real.pi_pos]
  have hs₀ := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ 0.285 by norm_num)
  have hs : (0.28 : ℝ) ≤ Real.sin d := by
    refine (show (0.28 : ℝ) ≤ Real.sin 0.285 by linarith only [hs₀]).trans ?_
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hd' hd
  have he : (0.19 : ℝ) ≤ Real.exp (2 * d / 3) - 1 := by
    nlinarith only [hd, Real.add_one_le_exp (2 * d / 3)]
  have h₁ := inv_anti₀ (show (0 : ℝ) < 0.28 ^ 2 by norm_num)
    (pow_le_pow_left₀ (show (0 : ℝ) ≤ 0.28 by norm_num) hs 2)
  have h₂ := inv_anti₀ (show (0 : ℝ) < 0.19 by norm_num) he
  exact (add_le_add h₁ h₂).trans (by norm_num)

theorem norm_midLogMultiplier_le_inner {n : ℕ} {r η χ h : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : 0 ≤ η) (hη' : η ≤ 3 / 2)
    (hh : 0 ≤ h) (hhi : h < Real.pi / 2) (hχ : |χ| ≤ h) :
    ‖midLogMultiplier r 0 (midEtaPoint n r η) χ‖ ≤ midLocalLogBound (midU n r) r⁻¹ h := by
  let u := midU n r
  let ζ := midEtaPoint n r η
  have hr' : 0 < r := by linarith
  have hu := saddleU_pos (by omega : 0 < n) hr'
  have hη₂ : 1 + η ^ 2 ≤ 13 / 4 := by
    nlinarith only [hη', mul_nonneg hη (sub_nonneg.mpr hη')]
  have hNorm : ‖-ζ / 12‖ ≤ Real.sqrt (13 / 4) * u / 12 := by
    rw [norm_div, norm_neg, norm_ofNat, show ‖ζ‖ = u * Real.sqrt (1 + η ^ 2) from
      norm_midEtaPoint (by omega) hr' η, mul_comm (Real.sqrt (13 / 4))]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hη₂) hu.le) (by norm_num)
  have hL : ‖saddleG (midModeRadius r 0) χ / ζ - pairedLog (midModeRadius r 0) χ ζ‖ ≤
      (13 / 16) * theta38K h * r⁻¹ * u := by
    rw [midModeRadius_zero, norm_sub_rev]
    have hLog := norm_pairedLog_neg_sub_saddleG_div_le_inner (inv_nonneg.mpr hr'.le)
      (inv_le_one_of_one_le₀ hr) hu hh hhi hχ hη hη'
    refine hLog.trans ?_
    have hK := theta38K_nonneg hhi.le
    have hMul := mul_le_mul_of_nonneg_right hη₂
      (div_nonneg (mul_nonneg (mul_nonneg hu.le (inv_nonneg.mpr hr'.le)) hK)
        (by norm_num : (0 : ℝ) ≤ 4))
    linarith only [hMul, show u * (1 + η ^ 2) * r⁻¹ * theta38K h / 4 =
      (1 + η ^ 2) * (u * r⁻¹ * theta38K h / 4) by ring, show
        (13 / 16 : ℝ) * theta38K h * r⁻¹ * u = (13 / 4) * (u * r⁻¹ * theta38K h / 4) by ring]
  have hE : ‖midEulerLog (midEtaTransform ζ)‖ ≤ (1 / 10 ^ 20 : ℝ) := by
    have he := norm_midEulerLog_lt_tiny hn hr hmax (by rwa [abs_of_nonneg hη])
    exact he.le.trans (by norm_num)
  unfold midLogMultiplier midLocalLogBound
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hNorm hE)) hL)).trans_eq
    (by ring)

theorem norm_midMultiplier_sub_one_le_inner {n : ℕ} {r η χ h : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : 0 ≤ η) (hη' : η ≤ 3 / 2)
    (hh : 0 ≤ h) (hhi : h < Real.pi / 2) (hχ : |χ| ≤ h) :
    ‖midMultiplier r 0 (midEtaPoint n r η) χ - 1‖ ≤
      Real.exp (midLocalLogBound (midU n r) r⁻¹ h) - 1 := by
  have hz : 0 < (midEtaPoint n r η).re := by
    rw [midEtaPoint_re]
    exact saddleU_pos (by omega) (by linarith)
  rw [midMultiplier_eq_exp_log hz]
  have he := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum
    (midLogMultiplier r 0 (midEtaPoint n r η) χ) 1
  simp at he
  exact he.trans (sub_le_sub_right
    (Real.exp_le_exp.mpr (norm_midLogMultiplier_le_inner hn hr hmax hη hη' hh hhi hχ)) _)

/-- The same central bound applies to the principal logarithm. -/
theorem norm_log_midMultiplier_le_inner {n : ℕ} {r η χ h : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : 0 ≤ η) (hη' : η ≤ 3 / 2)
    (hh : 0 ≤ h) (hhi : h ≤ 1) (hχ : |χ| ≤ h) :
    ‖Complex.log (midMultiplier r 0 (midEtaPoint n r η) χ)‖ ≤ midLocalLogBound (midU n r) r⁻¹ h := by
  let z := midEtaPoint n r η
  let L := midLogMultiplier r 0 z χ
  have hhp : h < Real.pi / 2 := by linarith [Real.pi_gt_d2]
  have hu := saddleU_pos (by omega : 0 < n) (by linarith : 0 < r)
  have hz : 0 < z.re := by simpa only [z, midEtaPoint_re] using hu
  have hnL := norm_midLogMultiplier_le_inner hn hr hmax hη hη' hh hhp hχ
  have hB : midLocalLogBound (midU n r) r⁻¹ h < Real.pi := by
    have hK := theta38K_le_nineteen hh hhi
    have hrinv := inv_le_one_of_one_le₀ hr
    have hR := inv_nonneg.mpr (show 0 ≤ r by linarith)
    have hu' := midU_lt_072 hn hr hmax
    have hs : Real.sqrt (13 / 4 : ℝ) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have ht := mul_le_mul (mul_le_mul hK hrinv hR (by norm_num)) hu'.le hu.le (by norm_num)
    have hb := mul_le_mul hs hu'.le hu.le (by norm_num)
    unfold midLocalLogBound
    linarith only [ht, hb, Real.pi_gt_d2]
  have hi : |L.im| < Real.pi := ((Complex.abs_im_le_norm _).trans hnL).trans_lt hB
  change ‖Complex.log (midMultiplier r 0 z χ)‖ ≤ _
  rw [midMultiplier_eq_exp_log hz, Complex.log_exp (abs_lt.mp hi).1 (abs_lt.mp hi).2.le]
  exact hnL

end DurfeeCCS.Step09
