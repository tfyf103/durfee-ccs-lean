module

public import DurfeeCCS.Step08.AngularMeans
public import DurfeeCCS.Step08.NearOriginLaplace
public import DurfeeCCS.Step08.SaddleBesselAverage

import Mathlib.Tactic.FunProp

/-! The angular exponential mean in the saddle model. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06

def saddleExponentialMean (r u v : ℝ) : ℂ :=
  angularAverage (fun θ => exp (saddleG r θ / verticalPoint u v) - 1)

theorem continuous_saddleExponentialMean {r u : ℝ} (hr : |r| ≤ 1) (hu : 0 < u) :
    Continuous (saddleExponentialMean r u) := by
  have hζ : Continuous (fun p : ℝ × ℝ => verticalPoint u p.1) := by
    unfold verticalPoint
    fun_prop
  have hg := (continuous_saddleG hr).comp (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  have hf : Continuous (fun p : ℝ × ℝ =>
      exp (saddleG r p.2 / verticalPoint u p.1) - 1) :=
    (Complex.continuous_exp.comp (hg.div hζ (fun p => verticalPoint_ne_zero hu p.1))).sub
      continuous_const
  unfold saddleExponentialMean angularAverage
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun v θ => exp (saddleG r θ / verticalPoint u v) - 1) hf _ _)

end DurfeeCCS.Step08
