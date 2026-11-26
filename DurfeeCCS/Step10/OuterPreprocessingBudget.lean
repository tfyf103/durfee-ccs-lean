module

public import DurfeeCCS.Step10.OuterPreprocessingParams
public import DurfeeCCS.Step10.OuterErrorNormalize

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Normalized forms of the three preprocessing majorants. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Set DurfeeCCS.Step07

private theorem outerRhoZero_le_scale {y h : ℝ} (hy : 80 ≤ y) (hh : 0 < h)
    (hhCap : h ≤ 4 * y ^ (1 / 3 : ℝ)) : sqrt (h ^ 2 + 4 * π ^ 2 / 3) ≤ 0.24 * y := by
  let t := y ^ (1 / 3 : ℝ)
  have hy₀ : 0 < y := by linarith
  have ht : 0 < t := Real.rpow_pos_of_pos hy₀ _
  have ht₂ : t ^ (2 : ℕ) = y ^ (2 / 3 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast hy₀.le]
    norm_num
  have ht₃ : t ^ (3 : ℕ) = y := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast hy₀.le, show (1 / 3 : ℝ) * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
  have htlo : (18.56 : ℝ) ≤ t ^ (2 : ℕ) := by
    rw [ht₂]
    exact (by norm_num : (18.56 : ℝ) ≤ 18.5663553344511).trans
      (outerEightyPow_lo.le.trans (Real.rpow_le_rpow (by norm_num) hy (by norm_num)))
  have hh₁ : h ≤ 0.216 * y := by
    change h ≤ 4 * t at hhCap
    refine hhCap.trans ?_
    rw [← ht₃]
    nlinarith only [mul_le_mul_of_nonneg_right htlo ht.le, ht.le]
  have hh₂ := pow_le_pow_left₀ hh.le hh₁ 2
  have hy₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 80) hy 2
  have hπ := pow_le_pow_left₀ pi_pos.le Real.pi_lt_d4.le 2
  apply sqrt_le_iff.mpr
  exact ⟨by positivity, by nlinarith only [hh₂, hy₂, hπ]⟩

private theorem outerSqrtDifference_le {y X : ℝ} (hy : 80 ≤ y)
    (hX₂ : X ^ 2 = y ^ 2 + 1 / 12) : X - y ≤ 1 / (24 * y) := by
  have hy₀ : 0 < y := by linarith
  apply (le_div_iff₀ (by positivity : 0 < 24 * y)).mpr
  nlinarith only [hX₂, sq_nonneg (X - y)]

theorem outerSqrtRatio_le {y X : ℝ} (hy : 80 ≤ y)
    (hX₂ : X ^ 2 = y ^ 2 + 1 / 12) : X / y ≤ 1.00001 := by
  have hy₀ : 0 < y := by linarith
  apply (div_le_iff₀ hy₀).mpr
  have h := (outerSqrtDifference_le hy hX₂).trans
    (div_le_div_of_nonneg_left zero_le_one (by norm_num) (show (1920 : ℝ) ≤ 24 * y by linarith))
  linarith only [h, hy]

/-- Scaling by the actual main-mode envelope leaves the small-radius error below 0.00004. -/
theorem smallRadius_budget {y X h : ℝ} (hy : 80 ≤ y) (hX : 0 < X)
    (hX₂ : X ^ 2 = y ^ 2 + 1 / 12) (hh : 8.76 < h) (hhLog : 2 * log y ≤ h)
    (hhCap : h ≤ 4 * y ^ (1 / 3 : ℝ)) :
    let p := sqrt (h ^ 2 + 4 * π ^ 2 / 3)
    let z := outerGeomFactor h (p / (4 * X))
    (X / (1 - z) ^ 2 * exp (X * p - 0.19 * p * y ^ 2 / (4 * X))) /
      outerTransformAmplitude y h < 0.00004 := by
  dsimp only
  let p := sqrt (h ^ 2 + 4 * π ^ 2 / 3)
  let z := outerGeomFactor h (p / (4 * X))
  let a := (outerRho h π).re
  have hy₀ : 0 < y := by linarith
  have hh₀ : 0 < h := by linarith
  have hp : h ≤ p := Real.le_sqrt_of_sq_le (by linarith [sq_nonneg π])
  have hp₀ : 0 < p := hh₀.trans_le hp
  have hXy := outerSqrtRatio_le hy hX₂
  have hz : z < 0.47 := smallRadius_geomFactor_lt hy hX hXy hh hhLog
  have hcoef : X / (1 - z) ^ 2 ≤ 3.6 * y := by
    have hX' := (div_le_iff₀ hy₀).mp hXy
    have hZ : (0.53 : ℝ) ≤ 1 - z := by linarith only [hz]
    calc
      _ ≤ (1.00001 * y) / (0.53 : ℝ) ^ 2 :=
        div_le_div₀ (by positivity) hX' (by norm_num) (pow_le_pow_left₀ (by norm_num) hZ 2)
      _ = (1.00001 / (0.53 : ℝ) ^ 2) * y := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) hy₀.le
  have hXgap : (X - y) * p ≤ 0.010 := by
    calc
      _ ≤ 1 / (24 * y) * p := mul_le_mul_of_nonneg_right (outerSqrtDifference_le hy hX₂) hp₀.le
      _ ≤ 1 / (24 * y) * (0.24 * y) :=
        mul_le_mul_of_nonneg_left (outerRhoZero_le_scale hy hh₀ hhCap) (by positivity)
      _ = _ := by field_simp [hy₀.ne']; ring
  have hRatio : 0.99999 ≤ y / X := by
    apply (le_div_iff₀ hX).mpr
    have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hy₀).mp hXy)
      (by norm_num : (0 : ℝ) ≤ 0.99999)
    linarith only [h, hy]
  have hLoss : 0.19 * 0.99999 * h * y / 4 ≤ 0.19 * p * y ^ 2 / (4 * X) := by
    rw [show 0.19 * p * y ^ 2 / (4 * X) = 0.19 * (y / X) * p * y / 4 by ring]
    gcongr
  have hGap : p - a ≤ 0.0114 * h := by
    have hG0 := outerRhoAt_re_gap_le (t := π) hh₀ (show 0 < 4 * π ^ 2 / 3 by positivity)
    change p - a ≤ (4 * π ^ 2 / 3) * π ^ 2 / (2 * h * (h ^ 2 + 4 * π ^ 2 / 3)) at hG0
    refine hG0.trans ?_
    calc
      _ ≤ (4 * π ^ 2 / 3) * π ^ 2 / (2 * h * h ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by
          apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * h)
          linarith [sq_nonneg π])
      _ = (2 * π ^ 4 / (3 * h ^ 4)) * h := by field_simp [hh₀.ne']; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hh₀.le
        calc
          _ ≤ 2 * (3.1416 : ℝ) ^ 4 / (3 * 8.76 ^ 4) := by gcongr; exact Real.pi_lt_d4.le
          _ ≤ _ := by norm_num
  have hExpo : X * p - 0.19 * p * y ^ 2 / (4 * X) - y * a ≤ -0.315 * y + 0.010 := by
    have hJ := mul_le_mul_of_nonneg_right hGap hy₀.le
    have hK := mul_le_mul_of_nonneg_right hh.le hy₀.le
    have hM : (0.315 : ℝ) ≤ (0.19 * 0.99999 / 4 - 0.0114) * 8.76 := by norm_num
    have hMy := mul_le_mul_of_nonneg_right hM hy₀.le
    linear_combination hXgap + hLoss + hJ + (0.19 * 0.99999 / 4 - 0.0114 : ℝ) * hK + hMy
  have hnorm : (X / (1 - z) ^ 2 * exp (X * p - 0.19 * p * y ^ 2 / (4 * X))) /
      outerTransformAmplitude y h =
      (X / (1 - z) ^ 2 * (4 * π * y ^ 2 / h)) *
      exp (X * p - 0.19 * p * y ^ 2 / (4 * X) - y * a) := by
    unfold outerTransformAmplitude
    rw [Real.exp_sub (X * p - 0.19 * p * y ^ 2 / (4 * X)) (y * a)]
    change (X / (1 - z) ^ 2 * exp (X * p - 0.19 * p * y ^ 2 / (4 * X))) /
      (h * exp (y * a) / (4 * π * y ^ 2)) = _
    field_simp [hy₀.ne', hh₀.ne', Real.pi_ne_zero]
  change _ / outerTransformAmplitude y h < _
  rw [hnorm]
  calc
    _ ≤ (3.6 * y * (4 * π * y ^ 2 / 8.76)) * exp (-0.315 * y + 0.010) := by gcongr
    _ ≤ (15 * π * y ^ 3 / 8) * exp (-0.315 * y + 0.010) := by
      apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
      have hm : 3.6 * y * (4 * π * y ^ 2 / 8.76) = (3.6 * 4 / 8.76) * (π * y ^ 3) := by ring
      rw [hm, show 15 * π * y ^ 3 / 8 = (15 / 8) * (π * y ^ 3) by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ < _ := smallRadius_majorant_lt hy

/-- The aggregate Bessel replacement error from the coefficient-wise majorants on page 45. -/
theorem kernelSwap_budget {y h : ℝ} (hy : 80 ≤ y) (hh : 8.76 < h)
    (hhCap : h ≤ 4 * y ^ (1 / 3 : ℝ)) :
    5 * y * exp ((y + 1 / (24 * y)) * sqrt (h ^ 2 + π ^ 2 / 3)) /
      outerTransformAmplitude y h < 0.0208 := by
  let u := sqrt (h ^ 2 + π ^ 2 / 3)
  let a := (outerRho h π).re
  have hy₀ : 0 < y := by linarith
  have hh₀ : 0 < h := by linarith
  have hp : u ≤ sqrt (h ^ 2 + 4 * π ^ 2 / 3) := Real.sqrt_le_sqrt (by linarith [sq_nonneg π])
  have hu : u ≤ 0.24 * y := hp.trans (outerRhoZero_le_scale hy hh₀ hhCap)
  have hJ : 1 / (24 * y) * u ≤ 0.010 := by
    calc
      _ ≤ 1 / (24 * y) * (0.24 * y) := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = _ := by field_simp [hy₀.ne']; ring
  have hG := mul_lt_mul_of_pos_right (outerRho_re_sub_replacementSlope_gt hh) hy₀
  have hExp : (y + 1 / (24 * y)) * u - y * a ≤ -(2 * π ^ 2 * y / (5 * h)) + 0.010 := by
    change 2 * π ^ 2 / (5 * h) * y < (a - u) * y at hG
    calc
      _ = -(a - u) * y + 1 / (24 * y) * u := by ring
      _ ≤ -(2 * π ^ 2 / (5 * h) * y) + 0.010 := by
        linarith only [hG, hJ]
      _ = _ := by ring
  have hnorm : 5 * y * exp ((y + 1 / (24 * y)) * u) / outerTransformAmplitude y h =
      20 * π / h * y ^ 3 * exp ((y + 1 / (24 * y)) * u - y * a) := by
    unfold outerTransformAmplitude
    rw [Real.exp_sub]
    change 5 * y * exp ((y + 1 / (24 * y)) * u) /
      (h * exp (y * a) / (4 * π * y ^ 2)) = _
    field_simp [hy₀.ne', hh₀.ne', Real.pi_ne_zero]
    ring
  change 5 * y * exp ((y + 1 / (24 * y)) * u) / outerTransformAmplitude y h < _
  rw [hnorm]
  refine lt_of_le_of_lt ?_ (kernelSwap_majorant_lt hy hh₀ hhCap)
  gcongr

/-- The tails added by completing the integer lattice contribute less than 10⁻³⁰. -/
theorem negativeExtension_budget {y h : ℝ} (hy : 80 ≤ y) (hhLog : 2 * log y ≤ h) :
    40 * y ^ 7 * exp (4 * π * y / sqrt 3) / outerTransformAmplitude y h < 1e-30 := by
  have hy₀ : 0 < y := by linarith
  have hlog : 0 < log y := Real.log_pos (by linarith)
  have hh₀ : 0 < h := (by positivity : 0 < 2 * log y).trans_le hhLog
  have ha : h < (outerRho h π).re := outerRho_re_gt hh₀
  have hExp := mul_le_mul_of_nonneg_left (hhLog.trans ha.le) hy₀.le
  have hR : 40 * y ^ 7 * exp (4 * π * y / sqrt 3) / outerTransformAmplitude y h =
      (160 * π * y ^ 9 / h) * exp (4 * π * y / sqrt 3 - y * (outerRho h π).re) := by
    unfold outerTransformAmplitude
    rw [Real.exp_sub]
    field_simp [hy₀.ne', hh₀.ne', Real.pi_ne_zero]
    ring
  rw [hR]
  calc
    _ ≤ (160 * π * y ^ 9 / (2 * log y)) * exp (y * (4 * π / sqrt 3 - 2 * log y)) := by
      have hC : 4 * π * y / sqrt 3 - y * (outerRho h π).re ≤
          y * (4 * π / sqrt 3 - 2 * log y) := by linear_combination hExp
      gcongr
    _ < _ := negativeExtension_majorant_lt hy

end DurfeeCCS.Step10
