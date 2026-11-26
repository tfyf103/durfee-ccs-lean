module

public import DurfeeCCS.Step09.MidMultiplierRadius

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-! Exact coordinate and contour range statements of (49) and page 27. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step09

open Set DurfeeCCS.Step06 DurfeeCCS.Step07

theorem midSaddle_coordinate_bounds {r : ℝ} (hr : 1 ≤ r) :
    0.68 < (saddleS 1).im ^ 2 ∧ (saddleS 1).im ^ 2 ≤ (saddleS r).im ^ 2 ∧
      (saddleS r).re ^ 2 ≤ Real.log r ^ 2 + Real.pi ^ 2 / 3 := by
  have hOne := saddle_at_one_lower.2
  have hOneSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.85623) hOne 2
  have hMono : (saddleS 1).im ≤ (saddleS r).im :=
    monotoneOn_saddleS_im (by simp) hr hr
  have hRe := saddleS_exp_re_sq_le (Real.log_nonneg hr)
  rw [Real.exp_log (by positivity : 0 < r)] at hRe
  exact ⟨by linarith, pow_le_pow_left₀ (by linarith) hMono 2, hRe⟩

private theorem theta38Growth_div_lt {x : ℝ} (hx : 80 ≤ x) :
    theta38Growth x / x < 0.072 := by
  have hx' : 0 < x := by linarith
  apply (div_lt_iff₀ hx').mpr
  rcases eq_or_lt_of_le hx with h | h
  · subst x
    have hl : Real.log 80 < 4.4 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      dyadic_interval [prec := 20]
    have hl' : 0 ≤ Real.log 80 + 1 := by
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 80)]
    have hs := pow_le_pow_left₀ hl'
      (show Real.log 80 + 1 ≤ 5.4 by linarith) 2
    have hSqrt : theta38Growth 80 < 5.76 := by
      unfold theta38Growth
      calc
        _ < Real.sqrt ((5.76 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by positivity) (by linarith)
        _ = _ := Real.sqrt_sq (by norm_num)
    exact hSqrt.trans_le (by norm_num)
  · have hY : 1 < x / 80 := (lt_div_iff₀ (by norm_num)).mpr (by simpa using h)
    have hSqrt : Real.sqrt (x / 80) < x / 80 := by
      have hPos : 0 ≤ x / 80 := by linarith
      have hSq : x / 80 < (x / 80) ^ 2 := by
        nlinarith [mul_pos (show 0 < x / 80 by positivity) (sub_pos.mpr hY)]
      calc
        _ < Real.sqrt ((x / 80) ^ 2) := Real.sqrt_lt_sqrt hPos hSq
        _ = _ := Real.sqrt_sq hPos
    calc
      theta38Growth x ≤ 5.76 * Real.sqrt (x / 80) := theta38Growth_le hx
      _ < 5.76 * (x / 80) := mul_lt_mul_of_pos_left hSqrt (by norm_num)
      _ = _ := by ring

theorem midSaddle_parameter_range {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) :
    let a := (saddleS r).re
    let aₙ := Real.sqrt ((Real.log (n : ℝ) / 2 + 1) ^ 2 + 3.3)
    1 < a ∧ a ≤ aₙ ∧ 0 < midSlope r ∧ midSlope r < 1 ∧
      midU n r ≤ aₙ / Real.sqrt (n : ℝ) ∧ aₙ / Real.sqrt (n : ℝ) < 0.072 ∧
      Icc (-8 : ℝ) 8 ⊆ Icc (-(Real.pi / midU n r)) (Real.pi / midU n r) ∧
      (∀ η : ℝ, |η| ≤ 8 →
        ‖midEtaPoint n r η‖ < 0.581 ∧ 8.43 < (midEtaTransform (midEtaPoint n r η)).re) := by
  have hx : 80 ≤ Real.sqrt (n : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have ha := midSaddle_data hn hr hmax
  dsimp only at ha
  have hGrowth : theta38Growth (Real.sqrt (n : ℝ)) =
      Real.sqrt ((Real.log (n : ℝ) / 2 + 1) ^ 2 + 3.3) := by
    rw [theta38Growth, Real.log_sqrt (by positivity)]
  rw [← hGrowth]
  have hU : midU n r ≤ theta38Growth (Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) := by
    change (saddleS r).re / Real.sqrt (n : ℝ) ≤ _
    exact div_le_div_of_nonneg_right ha.2.1 (Real.sqrt_nonneg _)
  have hEight : 8 ≤ Real.pi / midU n r :=
    (le_div_iff₀ ha.2.2.2.2.1).mpr (eight_mul_midU_lt_pi hn hr hmax).le
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, hU, theta38Growth_div_lt hx, ?_, ?_⟩
  · exact Icc_subset_Icc (neg_le_neg hEight) hEight
  · exact fun _ hη => ⟨norm_midEtaPoint_lt hn hr hmax hη,
      re_midEtaTransform_midEtaPoint_gt_843 hn hr hmax hη⟩

end DurfeeCCS.Step09
