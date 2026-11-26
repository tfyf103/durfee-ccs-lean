module

public import DurfeeCCS.Step08.SaddleNormalization
public import DurfeeCCS.PartitionForm

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The error budgets and their sign consequences on the first saddle range. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open DurfeeCCS.Step06 DurfeeCCS.Step07

/-- The integer Durfee polynomial evaluated on the negative real axis. -/
def durfeeNegativeValue (n : ℕ) (r : ℝ) : ℝ :=
  (DurfeeCCS.durfeePolynomial n).eval₂ (Int.castRingHom ℝ) (-(r ^ 2))

def firstSaddlePrediction (n : ℕ) (r : ℝ) : ℝ :=
  saddleAmplitude n r * Real.cos (saddlePhase n r)

/-- The six certified sums, with the same radius cuts as in Proposition 3.5. -/
def firstSaddleNumericalBudget (n : ℕ) (r : ℝ) : ℝ :=
  let ω := saddleOmega n r
  if r ≤ 0.03 then firstSaddleTableSum 0.03 ω 0.99
  else if r ≤ 0.1 then firstSaddleTableSum 0.1 ω 0.99
  else if r ≤ 0.25 then firstSaddleTableSum 0.25 ω 0.55
  else if r ≤ 0.6 then firstSaddleCaseTwoError 0.6 ω 0.479
  else if r ≤ 0.9 then firstSaddleCaseTwoError 0.9 ω 0.692
  else firstSaddleCaseTwoError 1 ω 0.827

/-- The numerical part of Proposition 3.5, at the actual saddle scale. -/
theorem firstSaddleNumericalBudget_lt {n : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hscale : 4 * Real.pi ≤ Real.sqrt ((n : ℝ) * r)) :
    firstSaddleNumericalBudget n r < 9 / 10 := by
  unfold firstSaddleNumericalBudget saddleOmega
  split_ifs with h₁ h₂ h₃ h₄ h₅
  · exact (firstSaddleTable_sum_saddle_003 hr h₁ hscale).trans (by norm_num)
  · exact (firstSaddleTable_sum_saddle_01 hn (lt_of_not_ge h₁) h₂).trans (by norm_num)
  · exact (firstSaddleTable_sum_saddle_025 hn (lt_of_not_ge h₂) h₃).trans (by norm_num)
  · exact (firstSaddleCaseTwoError_saddle_06 hn (lt_of_not_ge h₃) h₄).trans (by norm_num)
  · exact (firstSaddleCaseTwoError_saddle_09 hn (lt_of_not_ge h₄) h₅).trans (by norm_num)
  · exact (firstSaddleCaseTwoError_saddle_1 hn (lt_of_not_ge h₅) hr₁).trans (by norm_num)

/-- Assemble the error of an angular model and the error of its saddle approximation. -/
theorem firstSaddle_relative_of_two_bounds {n : ℕ} (hn : 6400 ≤ n) {r Q e : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hscale : 4 * Real.pi ≤ Real.sqrt ((n : ℝ) * r))
    (hcontour : |durfeeNegativeValue n r - Q| ≤
      saddleAmplitude n r * (firstSaddleNumericalBudget n r - e))
    (hmodel : |Q - firstSaddlePrediction n r| ≤ saddleAmplitude n r * e) :
    |durfeeNegativeValue n r - firstSaddlePrediction n r| < (9 / 10) * saddleAmplitude n r := by
  have hpos : 0 < saddleAmplitude n r := saddleAmplitude_pos (by omega) hr
  calc
    _ ≤ |durfeeNegativeValue n r - Q| + |Q - firstSaddlePrediction n r| := abs_sub_le _ _ _
    _ ≤ saddleAmplitude n r * (firstSaddleNumericalBudget n r - e) +
        saddleAmplitude n r * e := add_le_add hcontour hmodel
    _ = saddleAmplitude n r * firstSaddleNumericalBudget n r := by ring
    _ < _ := by simpa only [mul_comm] using
      mul_lt_mul_of_pos_left (firstSaddleNumericalBudget_lt hn hr hr₁ hscale) hpos

theorem firstSaddle_sign_of_relative_error {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (herror : |durfeeNegativeValue n r - firstSaddlePrediction n r| <
      (9 / 10) * saddleAmplitude n r) :
    (Real.cos (saddlePhase n r) = 1 → 0 < durfeeNegativeValue n r) ∧
    (Real.cos (saddlePhase n r) = -1 → durfeeNegativeValue n r < 0) := by
  have hpos := saddleAmplitude_pos hn hr
  have ⟨hlo, hhi⟩ := abs_lt.mp herror
  constructor <;> intro hc
  · rw [firstSaddlePrediction, hc, mul_one] at hlo
    linarith
  · rw [firstSaddlePrediction, hc, mul_neg_one] at hhi
    linarith

end DurfeeCCS.Step08
