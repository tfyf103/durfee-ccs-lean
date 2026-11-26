module

public import DurfeeCCS.Step08.FirstSaddleCommonArc
public import DurfeeCCS.Step08.FirstSaddleMajorBound
public import DurfeeCCS.Step08.MidpointMainArcCaseOne
public import DurfeeCCS.Step08.MinorArcLargeRadius
public import DurfeeCCS.Step08.SaddleBesselApproximation
public import DurfeeCCS.Step08.SaddleMinorArc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Assembly of the six certified radius ranges in Proposition 3.5. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07

private theorem firstSaddle_contour_three_terms {n : ℕ} (hn : 6400 ≤ n) {r B U : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1)
    (hB :
      let u := saddleU n r
      Real.exp (saddleOmega n r) / (2*Real.pi) *
        (∫ v in Icc (-(16*u)) (16*u), ‖durfeeExponentialMean r u v-saddleExponentialMean r u v‖) ≤
        saddleAmplitude n r * B)
    (hU :
      let u := saddleU n r
      Real.exp (saddleOmega n r) / (2*Real.pi) *
        (∫ v in Icc (-Real.pi) Real.pi \ Icc (-(16*u)) (16*u), ‖durfeeExponentialMean r u v‖) ≤
        saddleAmplitude n r * U) :
    |durfeeNegativeValue n r-saddleBesselAverage n r| ≤
      saddleAmplitude n r * (B+U+firstSaddleL16 (saddleOmega n r)) := by
  have h := saddle_contour_difference_le hn hr hr₁
  have hL := saddle_tail_error_le (by omega : 0 < n) hr hr₁
  dsimp only at h hB hU hL
  rw [mul_add, mul_add] at h
  exact h.trans ((add_le_add (add_le_add hB hU) hL).trans_eq (by ring))

private theorem firstSaddle_contour_budget {n : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) :
    |durfeeNegativeValue n r-saddleBesselAverage n r| ≤ saddleAmplitude n r *
      (firstSaddleNumericalBudget n r-firstSaddleE (saddleOmega n r) (saddleGamma r)) := by
  let ω := saddleOmega n r
  let M := saddleAmplitude n r
  have hn' : 0 < n := by omega
  have hM : 0 ≤ M := (saddleAmplitude_pos hn' hr).le
  have hcoord := (firstSaddle_coordinates_bounds hr hr₁).1
  have hcommon := firstSaddle_common_error_le hn' hr hr₁
  have hSmall {r₀ : ℝ} (hrr : r ≤ r₀) (hr₀ : r₀ ≤ 1/4) :
      |durfeeNegativeValue n r-saddleBesselAverage n r| ≤ M *
        (firstSaddleTableSum r₀ ω (saddleGamma r)-firstSaddleE ω (saddleGamma r)) := by
    have hB := firstSaddleMainArcBudget_le_caseOne hn hr hrr hr₀
    have hU := durfee_minor_error_le hn' hr hrr (hr₀.trans_lt (by norm_num))
    have h := firstSaddle_contour_three_terms hn hr hr₁ (hcommon.trans (mul_le_mul_of_nonneg_left hB hM)) hU
    exact h.trans_eq (by unfold firstSaddleTableSum; ring)
  have hLarge {r₀ β off high piBound μ : ℝ} (hquarter : 0.25 < r) (hrr : r ≤ r₀)
      (hr₀ : r₀ ≤ 1) (hβ : 0 < β) (ha : β*r ≤ (saddleS r).re^2) (hμ : 0 ≤ μ)
      (hrow : FirstSaddleArcRow r₀ β off high piBound μ) :
      |durfeeNegativeValue n r-saddleBesselAverage n r| ≤ M *
        (firstSaddleCaseTwoError r₀ ω μ-firstSaddleE ω 0.55) := by
    have hquarter' : 1/4 < r := by linarith only [hquarter]
    have hB := firstSaddleMainArcBudget_le_case_two hn hquarter'.le hrr hr₀
    have hU := durfee_minor_error_case_two_row hn hquarter' hrr hr₀ hβ ha hμ hrow
    have h := firstSaddle_contour_three_terms hn hr hr₁ (hcommon.trans (mul_le_mul_of_nonneg_left hB hM)) hU
    exact h.trans_eq (by unfold firstSaddleCaseTwoError; ring)
  unfold firstSaddleNumericalBudget
  split_ifs with h₀₃ h₁ hquarter h₆ h₉
  · have hγ : r ≤ 0.1 := by linarith only [h₀₃]
    simpa only [saddleGamma, ite_eq_left hγ] using hSmall h₀₃ (by norm_num)
  · simpa only [saddleGamma, ite_eq_left h₁] using hSmall h₁ (by norm_num)
  · simpa only [saddleGamma, ite_eq_right h₁] using hSmall hquarter (by norm_num)
  · simpa only [saddleGamma, ite_eq_right h₁] using hLarge (lt_of_not_ge hquarter) h₆
      (by norm_num) (by norm_num) (by simpa only [one_mul] using hcoord) (by norm_num) firstSaddleArcRow_06
  · simpa only [saddleGamma, ite_eq_right h₁] using hLarge (lt_of_not_ge hquarter) h₉
      (by norm_num) (by norm_num) (by simpa only [one_mul] using hcoord) (by norm_num) firstSaddleArcRow_09
  · have ha := (firstSaddleRadius_sharp (le_of_lt (lt_of_not_ge h₉)) hr₁).le
    simpa only [saddleGamma, ite_eq_right h₁] using hLarge (lt_of_not_ge hquarter) hr₁
      le_rfl (by norm_num) ha (by norm_num) firstSaddleArcRow_1

/-- Proposition 3.5, the uniform relative error on the first saddle region. -/
theorem proposition35 {n : ℕ} (hn : 6400 ≤ n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hscale : 4*Real.pi ≤ Real.sqrt ((n : ℝ)*r)) :
    |durfeeNegativeValue n r-saddleAmplitude n r*Real.cos (saddlePhase n r)| <
      (9/10)*saddleAmplitude n r := by
  have hn' : 0 < n := by omega
  exact firstSaddle_relative_of_two_bounds hn hr hr₁ hscale (firstSaddle_contour_budget hn hr hr₁)
    (lemma34 hn' hr hr₁)

/-- The polynomial has the required signs at the positive and negative cosine extrema. -/
theorem firstSaddle_sign {n : ℕ} (hn : 6400 ≤ n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hscale : 4*Real.pi ≤ Real.sqrt ((n : ℝ)*r)) :
    (Real.cos (saddlePhase n r) = 1 → 0 < durfeeNegativeValue n r) ∧
      (Real.cos (saddlePhase n r) = -1 → durfeeNegativeValue n r < 0) :=
  firstSaddle_sign_of_relative_error (by omega) hr (proposition35 hn hr hr₁ hscale)

end DurfeeCCS.Step08
