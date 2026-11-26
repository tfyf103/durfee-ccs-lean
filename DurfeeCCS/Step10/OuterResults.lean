module

public import DurfeeCCS.Step10.OuterSigns
public import DurfeeCCS.Step10.OuterFar
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Polynomial

theorem farThreshold_eq_shifted {n : ℕ} (hn : 1 ≤ n) :
    farThreshold n = 4 * ((n : ℝ) - 1 / 12) ^ (1 / 6 : ℝ) := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold farThreshold outerY
  rw [sqrt_eq_rpow, ← rpow_mul (by linarith : 0 ≤ (n : ℝ) - 1 / 12)]
  norm_num

theorem outerMonomialDominance : OuterMonomialDominance := by
  intro n hn d hd hdm hf
  exact lemma43 hn hd hdm hf

/-- Translate Proposition 4.1 from logarithmic coordinates back to the paper's radius. -/
theorem outerBesselApproximation_at_radius (hApprox : OuterBesselApproximation)
    {n : ℕ} (hn : 6401 ≤ n) {r : ℝ} (hr : 0 < r)
    (hlo : log ((n : ℝ) - 1 / 12) ≤ 2 * log r)
    (hhi : 2 * log r ≤ 4 * ((n : ℝ) - 1 / 12) ^ (1 / 6 : ℝ)) :
    |Step08.durfeeNegativeValue n r - outerPrediction (outerY n) (2 * log r)| <
      0.99 * outerTransformAmplitude (outerY n) (2 * log r) := by
  have hp := hApprox n hn (2 * log r) hlo ((farThreshold_eq_shifted (by omega : 1 ≤ n)).symm ▸ hhi)
  simpa only [show 2 * log r / 2 = log r by ring, exp_log hr] using hp

/-- Corollary 4.4 using the unconditional far-range estimate. -/
theorem corollary44_of_proposition41 (hApprox : OuterBesselApproximation)
    {n : ℕ} (hn : 6401 ≤ n) :
    ∃ d₀ : ℕ, ∃ x : ℕ → ℝ,
      (0.92 * outerY n < d₀ ∧ d₀ ≤ n.sqrt - 1) ∧
      (∀ d, d₀ ≤ d → d < n.sqrt → 0 < x d ∧
        (SignType.sign ((durfeePolynomialReal n).eval (-x d)) : ℝ) = (-1 : ℝ) ^ d) ∧
      StrictMonoOn x (Set.Ico d₀ n.sqrt) ∧
      (outerStart n ≤ log (x d₀) ∧ log (x d₀) ≤ outerStart n + 2) ∧
      |Step06.saddlePhase n (sqrt (x d₀)) - π * d₀| < 0.48 ∧
      ∃ r : Fin (n.sqrt - d₀) ↪ ℝ, ∀ i,
        r i < -x d₀ ∧ (durfeePolynomialReal n).IsRoot (r i) :=
  outerAlternating_of_estimates hApprox outerMonomialDominance hn

end DurfeeCCS.Step10
