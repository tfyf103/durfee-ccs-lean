module

public import DurfeeCCS.Step09.MidPoisson

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Dominated exchange of the Poisson sum and a vertical contour integral. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set Filter DurfeeCCS.Step06 DurfeeCCS.Step08
open scoped Topology

/-- The inverse of a vertical contour parameter has a uniform right-half-plane bound. -/
theorem re_inv_verticalPoint_ge {u B : ℝ} (hu : 0 < u) {v : ℝ} (hv : |v| ≤ B) :
    u / (u ^ 2 + B ^ 2) ≤ (verticalPoint u v)⁻¹.re := by
  have hB' := pow_le_pow_left₀ (abs_nonneg v) hv 2
  rw [sq_abs] at hB'
  rw [Complex.inv_re, Complex.normSq_apply, verticalPoint_re, verticalPoint_im]
  simp only [← pow_two]
  exact div_le_div_of_nonneg_left hu.le (by positivity) (by linarith)

theorem norm_inv_verticalPoint_le {u : ℝ} (hu : 0 < u) (v : ℝ) :
    ‖(verticalPoint u v)⁻¹‖ ≤ u⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ hu
  simpa only [verticalPoint_re, abs_of_pos hu] using Complex.abs_re_le_norm (verticalPoint u v)

private theorem midPoissonMode_integral_continuous {r u : ℝ} (hr : 1 ≤ r) (hu : 0 < u)
    (p : ℤ) : Continuous (fun v : ℝ => ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ) := by
  apply continuous_iff_continuousAt.mpr
  intro v₀
  let B : ℝ := |v₀| + 1
  let c : ℝ := u / (u^2 + B^2)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hlocal : ∀ᶠ v in 𝓝 v₀, |v| ≤ B :=
    (continuous_abs.continuousAt (x := v₀)).eventually_le_const (by dsimp only [B]; linarith)
  have hC := continuous_midPoissonMode_vertical hr hu p
  have hG := (integrable_exp_neg_mul_sq hc).const_mul (midPoissonModeBound r u c u⁻¹ p)
  refine continuousAt_of_dominated ?_ ?_ hG ?_
  · exact Eventually.of_forall (fun v => ((hC.comp
      (continuous_const.prodMk continuous_id : Continuous (fun χ : ℝ => (v, χ)))).aestronglyMeasurable))
  · filter_upwards [hlocal] with v hv
    refine ae_of_all _ fun χ => ?_
    exact norm_midPoissonMode_le hr hu (by simp) hc (re_inv_verticalPoint_ge hu hv)
      (norm_inv_verticalPoint_le hu v) p χ
  · exact ae_of_all _ fun χ => (hC.comp
      (continuous_id.prodMk continuous_const : Continuous (fun v : ℝ => (v, χ)))).continuousAt

private theorem norm_integral_midPoissonMode_le {r u B : ℝ} (hr : 1 ≤ r) (hu : 0 < u)
    {v : ℝ} (hv : |v| ≤ B) (p : ℤ) :
    let c := u / (u^2 + B^2)
    ‖∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ‖ ≤
      midPoissonModeBound r u c u⁻¹ p * ∫ χ : ℝ, Real.exp (-c * χ^2) := by
  dsimp only
  let c := u / (u^2 + B^2)
  have hc : 0 < c := by dsimp only [c]; positivity
  change ‖∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ‖ ≤
    midPoissonModeBound r u c u⁻¹ p * ∫ χ : ℝ, Real.exp (-c * χ^2)
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((integrable_exp_neg_mul_sq hc).const_mul _)
  exact ae_of_all _ fun χ => norm_midPoissonMode_le hr hu (by simp) hc
    (re_inv_verticalPoint_ge hu hv) (norm_inv_verticalPoint_le hu v) _ χ

/-- Summable absolute bounds for the integrals of the individual χ contributions. -/
theorem summable_norm_integral_midPoissonMode {r u : ℝ} (hr : 1 ≤ r) (hu : 0 < u) (v : ℝ) :
    Summable (fun p : ℤ => ‖∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ‖) := by
  let c := u / (u^2 + |v|^2)
  have hc : 0 < c := by dsimp only [c]; positivity
  exact ((midPoissonModeBound_summable r u hc u⁻¹).mul_right _).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_integral_midPoissonMode_le hr hu le_rfl)

/-- Any continuous weight may be inserted before exchanging a compact vertical
contour integral and the integer sum of the χ integrals in (47). -/
theorem hasSum_intervalIntegral_midPoissonMode {r u : ℝ} (hr : 1 ≤ r) (hu : 0 < u)
    {w : ℝ → ℂ} (hw : Continuous w) (a b : ℝ) :
    HasSum (fun p : ℤ => ∫ v in a..b, w v * ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ)
      (∫ v in a..b, w v * ∑' p : ℤ, ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ) := by
  let B : ℝ := max |a| |b|
  let c : ℝ := u / (u^2 + B^2)
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp ((isCompact_uIcc.image hw).isBounded)
  have hWB : ∀ v ∈ uIoc a b, ‖w v‖ ≤ M :=
    fun v hv => hM _ ⟨v, uIoc_subset_uIcc hv, rfl⟩
  have hB : ∀ v ∈ uIoc a b, |v| ≤ B := by
    intro v hv
    have hv' := uIoc_subset_uIcc hv
    obtain ⟨hl,hh⟩ := hv'
    have ha : -B ≤ a ∧ a ≤ B := abs_le.mp (le_max_left |a| |b|)
    have hb : -B ≤ b ∧ b ≤ B := abs_le.mp (le_max_right |a| |b|)
    exact abs_le.mpr ⟨(le_min ha.1 hb.1).trans hl, hh.trans (max_le ha.2 hb.2)⟩
  let K := ∫ χ : ℝ, Real.exp (-c * χ^2)
  have hK : 0 ≤ K := integral_nonneg (fun _ => Real.exp_nonneg _)
  let V (p : ℤ) : ℝ := M * (midPoissonModeBound r u c u⁻¹ p * K)
  have hV : Summable V := ((midPoissonModeBound_summable r u hc u⁻¹).mul_right K).mul_left M
  have hF (p : ℤ) : Continuous (fun v : ℝ => w v * ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ) :=
    hw.mul (midPoissonMode_integral_continuous hr hu p)
  have hdom (p : ℤ) (v : ℝ) (hv : v ∈ uIoc a b) :
      ‖w v * ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ‖ ≤ V p := by
    rw [norm_mul]
    exact mul_le_mul (hWB v hv) (norm_integral_midPoissonMode_le hr hu (hB v hv) p)
      (norm_nonneg _) ((norm_nonneg _).trans (hWB v hv))
  exact intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun p v => w v * ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ)
    (f := fun v => w v * ∑' p : ℤ, ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ)
    (fun p _ => V p) (fun p => (hF p).aestronglyMeasurable)
    (fun p => ae_of_all _ (hdom p))
    (ae_of_all _ fun _ _ => hV) intervalIntegrable_const
    (ae_of_all _ fun v _ => (summable_norm_integral_midPoissonMode hr hu v).of_norm.hasSum.mul_left (w v))

end DurfeeCCS.Step09
