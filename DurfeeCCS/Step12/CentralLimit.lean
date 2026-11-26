module

public import DurfeeCCS.Step12.CentralLimitChar
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! Weak convergence for finite Bernoulli rows with diverging total variance. -/

public section

open Filter
open scoped BigOperators Topology

namespace DurfeeCCS

open MeasureTheory ProbabilityTheory in
/-- A row law with the centered Bernoulli characteristic function converges
weakly to the standard Gaussian under divergence of the total variance. -/
theorem tendsto_gaussianReal_of_bernoulli_charFun {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (p : ∀ n, ι n → ℝ) (hp : ∀ n i, p n i ∈ Set.Icc (0 : ℝ) 1)
    (hV : Tendsto (fun n ↦ bernoulliVariance (p n)) atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ)
    (hμ : ∀ n t, charFun (μ n : Measure ℝ) t =
      ∏ i, centeredBernoulliChar (p n i) (t / Real.sqrt (bernoulliVariance (p n)))) :
    Tendsto μ atTop (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hG : charFun (gaussianReal 0 1) t = Complex.exp (↑(-(t ^ 2) / 2 : ℝ)) := by
    rw [charFun_gaussianReal]
    push_cast
    ring_nf
  simpa only [ProbabilityMeasure.coe_mk, hμ, hG] using
    tendsto_prod_centeredBernoulliChar p hp hV t

end DurfeeCCS
