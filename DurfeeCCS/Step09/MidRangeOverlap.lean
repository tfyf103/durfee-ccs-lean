module

public import DurfeeCCS.Step09.MidProof
public import DurfeeCCS.Step08.FirstSaddlePhaseSign

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The overlap of the first and second saddle ranges. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open DurfeeCCS.Step06 DurfeeCCS.Step08

theorem saddle_ranges_relative_error {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 0 < r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hscale : 4 * Real.pi ≤ Real.sqrt ((n : ℝ) * r)) :
    |durfeeNegativeValue n r - saddleAmplitude n r * Real.cos (saddlePhase n r)| <
      (19 / 20 : ℝ) * saddleAmplitude n r := by
  by_cases hr₁ : r ≤ 1
  · have hm := saddleAmplitude_pos (by omega : 0 < n) hr
    exact (proposition35 hn hr hr₁ hscale).trans
      (mul_lt_mul_of_pos_right (by norm_num : (9 / 10 : ℝ) < 19 / 20) hm)
  · exact proposition311 hn (le_of_lt (lt_of_not_ge hr₁)) hmax

theorem saddle_ranges_at_one {n : ℕ} (hn : 6400 ≤ n) :
    |durfeeNegativeValue n 1 - firstSaddlePrediction n 1| < (9 / 10 : ℝ) * saddleAmplitude n 1 ∧
    |durfeeNegativeValue n 1 - firstSaddlePrediction n 1| < (19 / 20 : ℝ) * saddleAmplitude n 1 := by
  have hx : (80 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr zero_le_one
  have hmax : 1 ≤ Real.exp 1 * Real.sqrt (n : ℝ) :=
    one_le_mul_of_one_le_of_one_le he (by linarith only [hx])
  exact ⟨by simpa only [show (0.9 : ℝ) = 9 / 10 by norm_num] using midSaddle_radius_one hn,
    proposition311 hn le_rfl hmax⟩

theorem saddle_ranges_sign_at_phase {n k : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 0 < r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hscale : 4 * Real.pi ≤ Real.sqrt ((n : ℝ) * r))
    (hphase : saddlePhase n r = (k : ℝ) * Real.pi) :
    Real.sign (durfeeNegativeValue n r) = (-1 : ℝ) ^ k := by
  by_cases hr₁ : r ≤ 1
  · exact firstSaddle_sign_at_phase hn hr hr₁ hscale hphase
  · exact midSaddle_sign_at_phase hn (le_of_lt (lt_of_not_ge hr₁)) hmax hphase

end DurfeeCCS.Step09
