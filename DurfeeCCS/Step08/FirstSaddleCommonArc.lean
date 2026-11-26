module

public import DurfeeCCS.Step08.DurfeeContour
public import DurfeeCCS.Step08.MidpointMainArcRescale

import Mathlib.Tactic.Ring

/-! Identify the first term of (40) with the common-arc expression in (41). -/

public section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06

theorem durfee_saddle_difference_eq_angularAverage {r u : ℝ}
    (hr : |r| ≤ 1) (hu : 0 < u) (v : ℝ) :
    durfeeExponentialMean r u v - saddleExponentialMean r u v =
      angularAverage (firstSaddleCommonArcDifference r u v) := by
  have hp : Continuous (fun θ : ℝ => (v, θ)) := continuous_const.prodMk continuous_id
  have hlog : Continuous (fun θ => pairedLog r θ (verticalPoint u v)) := by
    change Continuous ((fun p : ℝ × ℝ => pairedLog r p.2 (verticalPoint u p.1)) ∘ fun θ => (v, θ))
    exact (continuous_pairedLog_vertical r hr hu).comp hp
  have hL : Continuous (fun θ => exp (pairedLog r θ (verticalPoint u v)) - 1) :=
    (Complex.continuous_exp.comp hlog).sub continuous_const
  have hG : Continuous (fun θ => exp (saddleG r θ / verticalPoint u v) - 1) :=
    (Complex.continuous_exp.comp ((continuous_saddleG hr).div_const _)).sub continuous_const
  rw [durfeeExponentialMean, saddleExponentialMean,
    ← angularAverage_sub (hL.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  congr 1
  ext θ
  unfold firstSaddleCommonArcDifference
  ring

theorem firstSaddle_common_error_le {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    let u := saddleU n r
    Real.exp (saddleOmega n r) / (2 * Real.pi) *
      (∫ v in Icc (-(16 * u)) (16 * u),
        ‖durfeeExponentialMean r u v - saddleExponentialMean r u v‖) ≤
      saddleAmplitude n r * firstSaddleMainArcBudget n r := by
  dsimp only
  have hr' : |r| ≤ 1 := by rwa [abs_of_pos hr]
  simp_rw [durfee_saddle_difference_eq_angularAverage hr' (saddleU_pos hn hr)]
  exact firstSaddleCommonArc_le hn hr hr₁

end DurfeeCCS.Step08
