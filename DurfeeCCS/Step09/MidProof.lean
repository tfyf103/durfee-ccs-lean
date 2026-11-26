module

public import DurfeeCCS.Step09.MidMajorProof
public import DurfeeCCS.Step09.MidMinorProof
public import DurfeeCCS.Step09.MidOtherProof
public import DurfeeCCS.Step09.MidNonprincipalContour

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Proposition 3.11 and the alternating signs in the second saddle range. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open DurfeeCCS.Step06 DurfeeCCS.Step08

theorem mid_remaining_error_lt {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) :
    ‖midCentralContribution n r -
      (midContribution n r 0 0 8 + midContribution n r (-1) (-8) 0)‖ <
        0.002 * saddleAmplitude n r :=
  (norm_midCentral_other_le hn hr hmax (summable_mid_frequency_integral_norm hn hr hmax)).trans_lt
    (lemma310 hn hr hmax)

theorem proposition311 {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) :
    |durfeeNegativeValue n r - saddleAmplitude n r * Real.cos (saddlePhase n r)| <
      (19 / 20 : ℝ) * saddleAmplitude n r := by
  have h := midRelativeError_of_bounds (by omega : 0 < n) (show 0 < r by linarith)
    (eight_mul_midU_lt_pi hn hr hmax).le (lemma38 hn hr hmax) (lemma39 hn hr hmax)
    (mid_remaining_error_lt hn hr hmax)
  simpa only [firstSaddlePrediction, show (0.95 : ℝ) = 19/20 by norm_num] using h

theorem midSaddle_sign_at_cosine_extremum {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hcos : Real.cos (saddlePhase n r) = 1 ∨ Real.cos (saddlePhase n r) = -1) :
    Real.sign (durfeeNegativeValue n r) = Real.cos (saddlePhase n r) := by
  have h := proposition311 hn hr hmax
  have h' : |durfeeNegativeValue n r - firstSaddlePrediction n r| < 0.95 * saddleAmplitude n r := by
    simpa only [firstSaddlePrediction, show (0.95 : ℝ) = 19/20 by norm_num] using h
  obtain ⟨hpos,hneg⟩ := midSaddle_sign_of_relativeError (by omega : 0 < n) (show 0 < r by linarith) h'
  rcases hcos with h₁ | h₁
  · rw [Real.sign_of_pos (hpos h₁),h₁]
  · rw [Real.sign_of_neg (hneg h₁),h₁]

theorem midSaddle_sign_at_phase {n k : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hphase : saddlePhase n r = (k : ℝ) * Real.pi) :
    Real.sign (durfeeNegativeValue n r) = (-1 : ℝ)^k := by
  have hcos : Real.cos (saddlePhase n r) = (-1 : ℝ)^k := by
    rw [hphase, Real.cos_nat_mul_pi]
  refine (midSaddle_sign_at_cosine_extremum hn hr hmax ?_).trans hcos
  rw [hcos]
  exact neg_one_pow_eq_or ℝ k

end DurfeeCCS.Step09
