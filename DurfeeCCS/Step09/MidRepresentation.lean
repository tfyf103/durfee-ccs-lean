module

public import DurfeeCCS.Step09.MidPoisson
public import DurfeeCCS.Step09.MidPhaseShape
public import DurfeeCCS.Step09.MidPhaseCurvature

import Mathlib.Tactic.Linarith

/-! Lemma 3.6 with the exact periodized formula, phase bounds and curvature. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory DurfeeCCS.Step06
open scoped ComplexConjugate

theorem lemma36 {r : ℝ} (hr : 1 ≤ r) :
    (∀ ζ : ℂ, 0 < ζ.re →
      durfeeAnalyticF (-(r : ℂ)^2) (exp (-ζ)) =
        (ζ*eulerProduct ζ^2)⁻¹ *
          (∑' p : ℤ, ∫ χ : ℝ, midPoissonMode r ζ p χ)) ∧
    (∀ (p : ℤ) (χ : ℝ),
      (midPhase r p χ).re ≤ Real.log r ^ 2 - midFrequency p ^ 2 + Real.pi ^ 2 / 3 -
        (saddleG r⁻¹ 0).re - χ ^ 2 / (1 + r⁻¹ ^ 2) ∧
      |(midPhase r p χ).im| ≤ 2 * Real.log r * |midFrequency p| + (saddleG r⁻¹ 0).im) ∧
    midPhase r 0 0 = saddleS r ^ 2 ∧
    midPhase r (-1) 0 = conj (saddleS r ^ 2) ∧
    deriv (deriv (midPhase r 0)) 0 = -2 * (r : ℂ) * I / (1 + (r : ℂ) * I) :=
  ⟨fun _ hζ => durfeeAnalyticF_midPoisson hr hζ, midPhase_component_bounds hr,
    midPhase_zero_value (by linarith), midPhase_neg_one_value hr, deriv_deriv_midPhase_zero hr⟩

end DurfeeCCS.Step09
