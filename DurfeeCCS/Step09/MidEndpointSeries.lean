module

public import DurfeeCCS.Step07.SaddleEndpoints

import Mathlib.Tactic.Linarith

/-! The 10,000- and 10,001-term endpoint enclosures in the proof of Lemma 3.8. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step07

/-- Each of the 5,000 consecutive pairs contributes two terms. The upper
partial sum includes the one extra even-indexed term. Rational input enclosures
may be used to round the two sums outwards at the endpoints. -/
theorem midEndpoint_partial_sums {t : ℝ} (ht : 0 ≤ t) {p q s w : ℚ}
    (hp : 0 ≤ p) (hp₂ : (p : ℝ) ≤ Real.exp (-2*t))
    (hq₂ : Real.exp (-2*t) ≤ (q : ℝ)) (hq : q ≤ 1)
    (hs : 0 ≤ s) (hs₁ : (s : ℝ) ≤ Real.exp (-t))
    (hw₁ : Real.exp (-t) ≤ (w : ℝ)) (hw : w ≤ 1) :
    let z := saddlePhaseSquare (Real.exp t)
    (t^2 + Real.pi^2/12 - (saddlePartialUpper 1 5000 p q : ℝ)/2 ≤ z.re ∧
      z.re ≤ t^2 + Real.pi^2/12 - (saddlePartial 1 5000 p q : ℝ)/2) ∧
    (Real.pi*t + 2*(saddlePartial 2 5000 s w : ℝ) ≤ z.im ∧
      z.im ≤ Real.pi*t + 2*(saddlePartialUpper 2 5000 s w : ℝ)) := by
  have hR := saddlePartial_bounds_re 5000 hp hp₂ hq₂ hq
  have hI := saddlePartial_bounds_im 5000 hs hs₁ hw₁ hw
  dsimp only
  rw [phaseSquare_re_exp,phaseSquare_im_exp ht]
  exact ⟨⟨by linarith only [hR.2], by linarith only [hR.1]⟩,
    ⟨by linarith only [hI.1], by linarith only [hI.2]⟩⟩

end DurfeeCCS.Step09
