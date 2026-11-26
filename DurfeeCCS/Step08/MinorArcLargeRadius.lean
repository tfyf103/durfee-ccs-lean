module

public import DurfeeCCS.Step08.MinorArcEnvelope
public import DurfeeCCS.Step08.MinorArcPi
public import DurfeeCCS.Step08.MinorArcSine

import Mathlib.Tactic.Linarith

/-! Cover the whole minor arc by the four estimates on pages 21–22. -/

public section

namespace DurfeeCCS.Step08

open MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07

theorem firstSaddleArcEstimates {r r₀ u v : ℝ} (hr : 0 < r) (hrr : r ≤ r₀)
    (hr₀ : r₀ ≤ 1) (hu : 0 < u) (hmin : 16 * u ≤ |v|) (hmax : |v| ≤ Real.pi)
    (θ : ℝ) : FirstSaddleArcEstimates r r₀ u v θ := by
  unfold FirstSaddleArcEstimates
  by_cases hv : ∃ q : ℚ, OnMinorRationalArc v q
  · obtain ⟨q,hq⟩ := hv
    by_cases h₁ : q.den = 1
    · exact Or.inr (Or.inr (Or.inr (norm_pairedLog_on_zero_arc hr (hrr.trans hr₀) hu θ
        (minorArc_den_one_eq_zero hq hmax h₁).2 hmin)))
    by_cases h₂ : q.den = 2
    · refine Or.inr (Or.inr (Or.inl (norm_pairedLog_pi_arc hr hrr hr₀ hu θ v ?_)))
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have ho : Odd (2 * k + 1) := ⟨k, by omega⟩
      exact (minorArc_sin_pi_odd hq h₂ ho (by omega)).le
    · have hd : 3 ≤ q.den := by have := q.den_pos; omega
      exact Or.inr (Or.inl (norm_pairedLog_high_arc hr hrr hr₀ hu θ hq hd))
  · exact Or.inl (norm_pairedLog_outside_rational_arcs hr hrr hr₀ hu θ (fun q hq => hv ⟨q,hq⟩))

theorem durfee_minor_error_case_two_row {n : ℕ} (hn : 6400 ≤ n)
    {r r₀ β off high πBound μ : ℝ}
    (hr : 1 / 4 < r) (hrr : r ≤ r₀) (hr₀ : r₀ ≤ 1) (hβ : 0 < β)
    (ha : β * r ≤ (saddleS r).re ^ 2) (hμ : 0 ≤ μ)
    (hrow : FirstSaddleArcRow r₀ β off high πBound μ) :
    let u := saddleU n r
    let ω := saddleOmega n r
    Real.exp ω / (2 * Real.pi) *
      (∫ v in Icc (-Real.pi) Real.pi \ Icc (-(16 * u)) (16 * u),
        ‖durfeeExponentialMean r u v‖) ≤
      saddleAmplitude n r * firstSaddleMinorArcError ω μ := by
  have hn' : 0 < n := by omega
  have hr' : 0 < r := by linarith
  refine durfee_minor_error_case_two hn' hr (hrr.trans hr₀) hμ (fun v hmin hmax θ => ?_)
  exact (Complex.re_le_norm _).trans (norm_pairedLog_le_minorEnvelope hn hr' hrr hr₀ hβ ha hrow
    (firstSaddleArcEstimates hr' hrr hr₀ (saddleU_pos hn' hr') hmin hmax θ))

end DurfeeCCS.Step08
