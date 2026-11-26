module

public import DurfeeCCS.Step10.OuterApproximation
public import DurfeeCCS.Step10.OuterFiniteExpansion
public import DurfeeCCS.Step10.OuterPreprocessingSmall
public import DurfeeCCS.Step10.OuterPreprocessingSwapSigned
public import DurfeeCCS.Step10.OuterResults
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset

/-- The discarded triples, coefficient replacements, and lattice extension together
cost strictly less than 0.022 times the outer amplitude. -/
theorem outerPreprocessing_bound : OuterPreprocessingError := by
  intro n hn h hh hcap
  let A := outerTransformAmplitude (outerY n) h
  let V := Step08.durfeeNegativeValue n (exp (h / 2))
  let G := ∑ abj ∈ outerGoodTriples n, outerTripleValue n h abj
  let K := ∑ abj ∈ outerGoodTriples n, outerTripleKernelPositive n h abj
  let L := ∑ abj ∈ outerGoodTriples n, outerTripleKernel n h abj
  have hh' := (outerStart_gt hn).trans_le hh
  have hy : 0 < outerY n := lt_trans (by norm_num) (eighty_lt_outerY hn)
  have hA : 0 < A := outerTransformAmplitude_pos hy (by linarith)
  have hl : 2 * log (outerY n) ≤ h := by
    rw [← outerStart_eq (by omega : 1 ≤ n)]
    exact hh
  have hsub : outerGoodTriples n ⊆ outerTripleBox n := filter_subset _ _
  have hs : V - G = ∑ abj ∈ outerTripleBox n \ outerGoodTriples n, outerTripleValue n h abj := by
    change Step08.durfeeNegativeValue n (exp (h / 2)) - G = _
    rw [durfeeNegativeValue_eq_outerTripleSum (by omega : 0 < n) h, ← sum_sdiff hsub]
    change _ + G - G = _
    ring
  have h₁ : |V - G| < 0.00004 * A := by
    rw [hs]
    exact (Finset.abs_sum_le_sum_abs _ _).trans_lt
      ((div_lt_iff₀ hA).mp (smallRadius_sum_error_lt hn hh hcap))
  have h₂ : |G - K| < 0.0208 * A :=
    abs_outerGoodTriples_values_sub_kernelPositive_lt hn hh' hl hcap
  have h₃ : |K - L| < 1e-30 * A := by
    rw [abs_sub_comm]
    exact outerNegativeExtension_error hn hl
  change |V - L| < 0.022 * A
  rw [show V - L = (V - G) + ((G - K) + (K - L)) by ring]
  have H := (abs_add_le (V - G) (G - K + (K - L))).trans
    (add_le_add le_rfl (abs_add_le (G - K) (K - L)))
  linarith only [H, h₁, h₂, h₃, hA]

/-- Proposition 4.1 with the exact domain and strict error tolerance of the manuscript. -/
theorem proposition41 : OuterBesselApproximation :=
  outerBesselApproximation_of_errors outerPreprocessing_bound outerTripleMass_bound

/-- Proposition 4.1 stated at the radius r of the Durfee evaluation. -/
theorem proposition41_at_radius {n : ℕ} (hn : 6401 ≤ n) {r : ℝ} (hr : 0 < r)
    (hlo : log ((n : ℝ) - 1 / 12) ≤ 2 * log r)
    (hhi : 2 * log r ≤ 4 * ((n : ℝ) - 1 / 12) ^ (1 / 6 : ℝ)) :
    |Step08.durfeeNegativeValue n r - outerPrediction (outerY n) (2 * log r)| <
      0.99 * outerTransformAmplitude (outerY n) (2 * log r) :=
  outerBesselApproximation_at_radius proposition41 hn hr hlo hhi

/-- Corollary 4.4. The interval to the left of the first sample contains at least m-d*
distinct negative roots. -/
theorem corollary44 {n : ℕ} (hn : 6401 ≤ n) :
    ∃ d₀ : ℕ, ∃ x : ℕ → ℝ,
      (0.92 * outerY n < d₀ ∧ d₀ ≤ n.sqrt - 1) ∧
      (∀ d, d₀ ≤ d → d < n.sqrt → 0 < x d ∧
        (SignType.sign ((durfeePolynomialReal n).eval (-x d)) : ℝ) = (-1 : ℝ) ^ d) ∧
      StrictMonoOn x (Set.Ico d₀ n.sqrt) ∧
      (outerStart n ≤ log (x d₀) ∧ log (x d₀) ≤ outerStart n + 2) ∧
      |Step06.saddlePhase n (sqrt (x d₀)) - π * d₀| < 0.48 ∧
      ∃ r : Fin (n.sqrt - d₀) ↪ ℝ, ∀ i,
        r i < -x d₀ ∧ (durfeePolynomialReal n).IsRoot (r i) :=
  corollary44_of_proposition41 proposition41 hn

end DurfeeCCS.Step10
