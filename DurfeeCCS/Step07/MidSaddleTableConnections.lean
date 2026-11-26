module

public import DurfeeCCS.Step07.MidSaddleTableActual
public import DurfeeCCS.Step07.MidSaddleTail
public import DurfeeCCS.Step07.SaddleEndpointGrid
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Uniform endpoint transfer for the page 36 and page 38 inequalities. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open DurfeeCCS.Step06

private theorem modeAmplitudeUpper_interval (i : Fin 5) {t : ℝ}
    (ht : t ≤ (i.val : ℝ) + 1) :
    (saddleS (Real.exp t)).re ≤ modeUpperAmplitude i := by
  have hmono := monotoneOn_saddleS_re (Real.exp_pos t) (Real.exp_pos ((i.val : ℝ) + 1))
    (Real.exp_le_exp.mpr ht)
  refine hmono.trans ?_
  fin_cases i
  · simpa [saddleEndpointData, modeUpperAmplitude, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (13 : Fin 21)).re_upper
  · simpa [saddleEndpointData, modeUpperAmplitude, Rat.cast_ofScientific, show (1 : ℝ) + 1 = 2 by norm_num] using
      (saddleEndpointData_bounds (15 : Fin 21)).re_upper
  · simpa [saddleEndpointData, modeUpperAmplitude, Rat.cast_ofScientific, show (2 : ℝ) + 1 = 3 by norm_num] using
      (saddleEndpointData_bounds (17 : Fin 21)).re_upper
  · simpa [saddleEndpointData, modeUpperAmplitude, Rat.cast_ofScientific, show (3 : ℝ) + 1 = 4 by norm_num] using
      (saddleEndpointData_bounds (18 : Fin 21)).re_upper
  · simpa [saddleEndpointData, modeUpperAmplitude, Rat.cast_ofScientific, show (4 : ℝ) + 1 = 5 by norm_num] using
      (saddleEndpointData_bounds (19 : Fin 21)).re_upper

private theorem modeGapLower_interval (i : Fin 5) {t : ℝ} (ht : (i.val : ℝ) ≤ t) :
    modeLowerGap i ≤ minorArcSaddleGap t := by
  have h0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hmono := monotoneOn_minorArcSaddleGap monotoneOn_saddleS_im h0 (h0.trans ht) ht
  refine le_trans ?_ hmono
  fin_cases i
  · simpa [minorArcSaddleGap, modeLowerGap, Real.exp_zero] using saddle_at_one_sq_lower.le
  · simpa [minorArcSaddleGap, saddleEndpointData, modeLowerGap, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (13 : Fin 21)).gap_lower.le
  · have hgap : (2.47220 : ℝ) < minorArcSaddleGap 2 := by
      simpa [minorArcSaddleGap, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds (15 : Fin 21)).gap_lower
    exact le_of_lt (lt_trans (by norm_num [modeLowerGap]) hgap)
  · have hgap : (2.75110 : ℝ) < minorArcSaddleGap 3 := by
      simpa [minorArcSaddleGap, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds (17 : Fin 21)).gap_lower
    exact le_of_lt (lt_trans (by norm_num [modeLowerGap]) hgap)
  · simpa [minorArcSaddleGap, saddleEndpointData, modeLowerGap, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (18 : Fin 21)).gap_lower.le

/-- All ten entries of the page 36 table, on their full log intervals. -/
theorem modeGap_on_log_interval (wide : Bool) (i : Fin 5) {t β : ℝ}
    (htₗ : (i.val : ℝ) ≤ t) (htᵤ : t ≤ (i.val : ℝ) + 1)
    (hβ : modeMultiplier wide * Real.pi / 2 ≤ β) :
    modeGapTarget wide i <
      ((saddleS (Real.exp t)).re ^ 2 - t ^ 2 - modeShiftedSquare t β) /
        (saddleS (Real.exp t)).re :=
  modeGap_of_endpoint_enclosures wide i htₗ htᵤ
    (modeAmplitudeUpper_interval i htᵤ) (modeGapLower_interval i htₗ) hβ

/-- The explicit phase loss for the opposite halves of the main modes, page 38. -/
def oppositeHalfLogPhaseLoss (t z : ℝ) : ℝ :=
  let r := Real.exp t
  let a := (saddleS r).re
  let b := (saddleS r).im
  (a ^ 2 * z ^ 2 + r ^ 2 / (1 + r ^ 2) * Real.pi ^ 2 / 4) /
    (a * (1 + 2 * (b/a) ^ 2 + 2 * z ^ 2))

theorem oppositeHalf_first_log_interval {t z : ℝ} (htₗ : 0 ≤ t) (htᵤ : t ≤ 0.5) :
    0.32 < oppositeHalfLogPhaseLoss t z := by
  let r := Real.exp t
  let a := (saddleS r).re
  let b := (saddleS r).im
  have hr : 0 < r := Real.exp_pos _
  have hrₗ : 1 ≤ r := Real.one_le_exp_iff.mpr htₗ
  have hrᵤ : r ≤ Real.exp 0.5 := Real.exp_le_exp.mpr htᵤ
  have hal : 1.06975 ≤ a := saddle_at_one_lower.1.trans
    (monotoneOn_saddleS_re (by norm_num) hr hrₗ)
  have ha₁ : (saddleS (Real.exp 0.5)).re ≤ 1.37623 := by
    simpa [saddleEndpointData, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (10 : Fin 21)).re_upper
  have hah : a ≤ 1.377 := (monotoneOn_saddleS_re hr (Real.exp_pos _) hrᵤ).trans (by linarith)
  have hb₁ : (saddleS (Real.exp 0.5)).im ≤ 0.99542 := by
    simpa [saddleEndpointData, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (10 : Fin 21)).im_upper
  have hb : b ≤ 0.99542 := (monotoneOn_saddleS_im hrₗ (Real.one_le_exp_iff.mpr (by norm_num))
    hrᵤ).trans hb₁
  have hρ : 0 ≤ b / a := div_nonneg (saddleS_components hr).1.le (by linarith)
  have hρh : b / a ≤ 0.931 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hc : 0.5 ≤ r ^ 2 / (1 + r ^ 2) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hrₗ 2]
  exact oppositeHalf_first_phase_loss hal hah hρ hρh hc

theorem oppositeHalf_second_log_interval {t z : ℝ} (htₗ : 0.5 ≤ t) (htᵤ : t ≤ 1) :
    0.44 < oppositeHalfLogPhaseLoss t z := by
  let r := Real.exp t
  let a := (saddleS r).re
  let b := (saddleS r).im
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : 1 ≤ r := Real.one_le_exp_iff.mpr (by linarith)
  have hrₗ : Real.exp 0.5 ≤ r := Real.exp_le_exp.mpr htₗ
  have hrᵤ : r ≤ Real.exp 1 := Real.exp_le_exp.mpr htᵤ
  have hal' : 1.37622 ≤ (saddleS (Real.exp 0.5)).re := by
    simpa [saddleEndpointData, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (10 : Fin 21)).re_lower
  have hal : 1.37622 ≤ a := hal'.trans (monotoneOn_saddleS_re (Real.exp_pos _) hr hrₗ)
  have ha₁ : (saddleS (Real.exp 1)).re ≤ 1.73266 := by
    simpa [saddleEndpointData, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (13 : Fin 21)).re_upper
  have hah : a ≤ 1.733 := (monotoneOn_saddleS_re hr (Real.exp_pos _) hrᵤ).trans (by linarith)
  have hb₁ : (saddleS (Real.exp 1)).im ≤ 1.11586 := by
    simpa [saddleEndpointData, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (13 : Fin 21)).im_upper
  have hb : b ≤ 1.11586 := (monotoneOn_saddleS_im hr₁ (Real.one_le_exp_iff.mpr (by norm_num))
    hrᵤ).trans hb₁
  have hρ : 0 ≤ b / a := div_nonneg (saddleS_components hr).1.le (by linarith)
  have hρh : b / a ≤ 0.812 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hc : 0.731 ≤ r ^ 2 / (1 + r ^ 2) := oppositeHalf_second_ratios hr (by
    rw [show Real.log r = t from Real.log_exp t]
    linarith)
  exact oppositeHalf_second_phase_loss hal hah hρ hρh hc

end DurfeeCCS.Step07
