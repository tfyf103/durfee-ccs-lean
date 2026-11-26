module

public import DurfeeCCS.Step09.MidMinorContour
public import DurfeeCCS.Step09.MidMinorProductFourier

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The smaller-arc estimate, Lemma 3.9. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

/-- Equation (62) as an estimate for the modulus, valid also at zero factors. -/
theorem norm_pairedProduct_le_midMinorBudget {r u : ℝ} (hr : 1 ≤ r) (hu : 0 < u)
    (v θ : ℝ) :
    ‖pairedProduct r θ (verticalPoint u v)‖ ≤
      Real.exp ((Real.log r ^ 2 + midMinorModeBudget u (Real.log r) v) / u) := by
  let t := Real.log r
  have ht : 0 ≤ t := Real.log_nonneg hr
  refine (norm_pairedProduct_le_clippedLog hr hu v θ).trans (Real.exp_le_exp.mpr ?_)
  apply (le_div_iff₀ hu).mpr
  let A := ∑' m : ℕ, max (midFactorLogRadius u t m) 0
  let B := ∑' m : ℕ, midMinorWeight 1 u t m
  let C := (∑' m : ℕ, (Complex.log (1 + midClippedTerm u t v θ m)
    + Complex.log (1 + midClippedTerm u t v (-θ) m))).re
  have h₁ : 2*u*A ≤ t^2 := midFactorLoss_sum hu ht
  have h₂ : ((2:ℝ)*(1-midMinorAlpha)*B)*u = 0.1 * (u * ‖midMinorMode 1 u t 0‖) := by
    rw [midMinorMode_zero, Complex.norm_real, Real.norm_eq_abs]
    have hB : 0 ≤ B := tsum_nonneg (fun _ => Real.exp_nonneg _)
    rw [show (∑' m : ℕ, midMinorWeight 1 u t m) = B from rfl, abs_of_nonneg hB]
    unfold midMinorAlpha
    ring
  have h₃ : C*u ≤ ∑' i : ℕ, midMinorWeightMode (i+1) * (u * ‖midMinorMode (i+1) u t v‖) := by
    have h := mul_le_mul_of_nonneg_right (midClipped_log_fourier_le hu t v θ) hu.le
    rw [← tsum_mul_right] at h
    refine h.trans_eq ?_
    apply tsum_congr
    intro i
    unfold midMinorWeightMode midMinorAlpha
    ring
  change (2*A + 2*(1-midMinorAlpha)*B+C)*u ≤ t^2 + midMinorModeBudget u t v
  unfold midMinorModeBudget
  linarith only [h₁,h₂,h₃]

theorem log_pairedProduct_le_midMinorBudget {r u : ℝ} (hr : 1 ≤ r) (hu : 0 < u)
    (v θ : ℝ) (hp : pairedProduct r θ (verticalPoint u v) ≠ 0) :
    u * Real.log ‖pairedProduct r θ (verticalPoint u v)‖ ≤
      Real.log r ^ 2 + midMinorModeBudget u (Real.log r) v := by
  have he := Real.log_le_log (norm_pos_iff.mpr hp) (norm_pairedProduct_le_midMinorBudget hr hu v θ)
  rw [Real.log_exp] at he
  rw [mul_comm]
  exact (le_div_iff₀ hu).mp he

/-- Equation (64), with the certified value (q^*) for the active row. -/
theorem norm_pairedProduct_le_minor_row {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (i : Fin 18)
    (hl : ((minorArcData i).left : ℝ) ≤ Real.log r)
    (hh : i.val < 17 → Real.log r ≤ ((minorArcData i).right : ℝ))
    {v : ℝ} (hv : 8*midU n r ≤ |v|) (hv' : |v| ≤ Real.pi) (θ : ℝ) :
    ‖pairedProduct r θ (verticalPoint (midU n r) v)‖ ≤
      Real.exp ((Real.log r^2+minorArcQstarRow i)/midU n r) := by
  have hu := saddleU_pos (by omega : 0 < n) (show 0 < r by linarith)
  refine (norm_pairedProduct_le_midMinorBudget hr hu v θ).trans (Real.exp_le_exp.mpr ?_)
  apply div_le_div_of_nonneg_right _ hu.le
  exact add_le_add_right (midMinorModeBudget_le_actual_row hn hr hmax i hl hh hv hv') _

theorem lemma39 {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n:ℝ)) :
    ‖midOuterContribution n r‖ < 0.05 * saddleAmplitude n r :=
  lemma39_of_modeEnvelope hn hr hmax
    (fun v θ => norm_pairedProduct_le_midMinorBudget hr (saddleU_pos (by omega) (by linarith)) v θ)

end DurfeeCCS.Step09
