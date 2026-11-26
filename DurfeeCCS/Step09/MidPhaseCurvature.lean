module

public import DurfeeCCS.Step09.MidPhaseDerivatives

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The local curvature at the middle saddle, including the radius-one endpoint. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex Filter DurfeeCCS.Step06 DurfeeCCS.Step08
open scoped Topology

private theorem midSaddleSeed_zero (t ε : ℝ) :
    midSaddleSeed t ε 0 = -(t : ℂ) * I := by
  simp [midSaddleSeed]

private theorem midSaddleSeed_re_lt_one_near_zero (t ε : ℝ) :
    ∀ᶠ χ : ℝ in 𝓝 0, (midSaddleSeed t ε (χ : ℂ)).re < 1 := by
  have hc : Continuous (fun χ : ℝ => (midSaddleSeed t ε (χ : ℂ)).re) := by
    unfold midSaddleSeed
    fun_prop
  have h : (midSaddleSeed t ε ((0 : ℝ) : ℂ)).re < 1 := by
    simp [midSaddleSeed_zero, Complex.mul_re]
  exact (hc.continuousAt (x := 0)).eventually_lt_const h

private theorem hasDerivAt_midPhase_zeroMode {r χ : ℝ} (hr : 0 < r)
    (hp : (midSaddleSeed (-r⁻¹) 1 (χ : ℂ)).re < 1)
    (hm : (midSaddleSeed (-r⁻¹) (-1) (χ : ℂ)).re < 1) :
    HasDerivAt (midPhase r 0)
      (-2 * (χ : ℂ) - midSaddleGDerivative (-r⁻¹) (χ : ℂ)) χ := by
  have ht : (-r⁻¹ : ℝ) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hr.ne')
  have hd := (hasDerivAt_midSaddleGComplex ht hp hm).comp_ofReal
  simp_rw [midSaddleGComplex_ofReal] at hd
  have hq : HasDerivAt (fun x : ℝ => (x : ℂ)^2) (2 * (χ : ℂ)) χ := by
    simpa using (((hasDerivAt_id (χ : ℂ)).pow 2).comp_ofReal)
  unfold midPhase
  rw [midModeRadius_zero]
  convert ((hasDerivAt_const χ
    (((Real.log r : ℂ) + (midFrequency 0 : ℂ) * I) ^ 2 + (Real.pi : ℂ) ^ 2 / 3)).sub hq).sub hd using 1
  ring

/-- The origin is a stationary angular point in the zero frequency. -/
theorem hasDerivAt_midPhase_zero {r : ℝ} (hr : 0 < r) :
    HasDerivAt (midPhase r 0) 0 0 := by
  have hs (ε : ℝ) : (midSaddleSeed (-r⁻¹) ε ((0 : ℝ) : ℂ)).re < 1 := by
    simp [midSaddleSeed_zero, Complex.mul_re]
  simpa [midSaddleGDerivative, midSaddleSeed_zero] using
    (hasDerivAt_midPhase_zeroMode hr (hs 1) (hs (-1)))

private theorem curvature_at_zero_identity {r : ℝ} (hr : 0 < r) :
    -2 - midSaddleGSecond (-r⁻¹) 0 = -2 * (r : ℂ) * I / (1 + (r : ℂ) * I) := by
  have hR : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hX : 1 - (r : ℂ)⁻¹ * I ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    rw [← Complex.ofReal_inv] at he
    norm_num [Complex.mul_re] at he
  have hY : 1 + (r : ℂ) * I ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.mul_re] at he
  have hD : -I + (r : ℂ) ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    exact hr.ne' he
  simp only [midSaddleGSecond, midSaddleSeed_zero, Complex.ofReal_neg, Complex.ofReal_inv, neg_neg]
  field_simp
  ring_nf
  rw [I_sq]
  field_simp [hD]
  ring

/-- The second angular derivative is exactly the curvature in Lemma 3.6.
The seeds are locally off the dilogarithm cut even at radius one. -/
theorem hasDerivAt_deriv_midPhase_zero {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (midPhase r 0)) (-2 * (r : ℂ) * I / (1 + (r : ℂ) * I)) 0 := by
  let t := -r⁻¹
  let f (χ : ℝ) : ℂ := -2 * (χ : ℂ) - midSaddleGDerivative t (χ : ℂ)
  have he : deriv (midPhase r 0) =ᶠ[𝓝 0] f := by
    filter_upwards [midSaddleSeed_re_lt_one_near_zero t 1, midSaddleSeed_re_lt_one_near_zero t (-1)]
      with χ hp hm
    exact (hasDerivAt_midPhase_zeroMode hr hp hm).deriv
  have hs (ε : ℝ) : (midSaddleSeed t ε ((0 : ℝ) : ℂ)).re < 1 := by
    simp [midSaddleSeed_zero, Complex.mul_re]
  have hg := (hasDerivAt_midSaddleGDerivative (hs 1) (hs (-1))).comp_ofReal
  have hlin : HasDerivAt (fun x : ℝ => -2 * (x : ℂ)) (-2 : ℂ) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).const_mul (-2 : ℂ)).comp_ofReal)
  have hf : HasDerivAt f (-2 - midSaddleGSecond t 0) 0 := by
    change HasDerivAt ((fun x : ℝ => -2 * (x : ℂ)) - (fun x : ℝ => midSaddleGDerivative t (x : ℂ))) _ _
    simpa only [Complex.ofReal_zero] using hlin.sub hg
  rw [curvature_at_zero_identity hr] at hf
  exact hf.congr_of_eventuallyEq he

theorem deriv_deriv_midPhase_zero {r : ℝ} (hr : 1 ≤ r) :
    deriv (deriv (midPhase r 0)) 0 = -2 * (r : ℂ) * I / (1 + (r : ℂ) * I) :=
  (hasDerivAt_deriv_midPhase_zero (by positivity)).deriv

end DurfeeCCS.Step09
