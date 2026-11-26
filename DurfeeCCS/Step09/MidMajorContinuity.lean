module

public import DurfeeCCS.Step09.MidMultiplierRadius
public import DurfeeCCS.Step08.LogArcMean
public import DurfeeCCS.Step08.SaddleBesselAverage
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Joint continuity of the transformed integrand on each vertical line. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory DurfeeCCS.Step06 DurfeeCCS.Step08
open Set

private theorem continuousOn_eulerProduct_right :
    ContinuousOn eulerProduct {ζ : ℂ | 0 < ζ.re} := by
  let τ (ζ : ℂ) : ℂ := I * ζ / (2 * (Real.pi : ℂ))
  have hτ : Continuous τ := by unfold τ; fun_prop
  have hm (ζ : ℂ) (hζ : 0 < ζ.re) : 0 < (τ ζ).im := by
    unfold τ
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im, Complex.mul_im]
    simpa using div_pos hζ (by positivity : (0 : ℝ) < 2 * Real.pi)
  have he (ζ : ℂ) : eulerProduct ζ = exp (ζ / 24) * ModularForm.eta (τ ζ) := by
    rw [show τ ζ = I * ζ / (2 * (Real.pi : ℂ)) from rfl, eta_rightHalfPlane, ← mul_assoc, ← exp_add]
    rw [show ζ / 24 + -ζ / 24 = 0 by ring, exp_zero, one_mul]
  have hf : ContinuousOn (fun ζ => ModularForm.eta (τ ζ)) {ζ : ℂ | 0 < ζ.re} := by
    intro ζ hζ
    exact (((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (hm ζ hζ)).continuousAt).comp
      hτ.continuousAt).continuousWithinAt
  exact ((show Continuous (fun ζ : ℂ => exp (ζ / 24)) by fun_prop).continuousOn.mul hf).congr
    (fun ζ _ => he ζ)

private theorem eulerProduct_ne_zero_of_re_pos {ζ : ℂ} (hζ : 0 < ζ.re) : eulerProduct ζ ≠ 0 := by
  have hτ : 0 < (I * ζ / (2 * (Real.pi : ℂ))).im := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im, Complex.mul_im]
    simpa using div_pos hζ (by positivity : (0 : ℝ) < 2 * Real.pi)
  intro he
  have hh := ModularForm.eta_ne_zero hτ
  rw [eta_rightHalfPlane, he, mul_zero] at hh
  exact hh rfl

theorem continuous_midEtaPoint (n : ℕ) (r : ℝ) : Continuous (midEtaPoint n r) := by
  unfold midEtaPoint
  fun_prop

private theorem midEtaPoint_nonzero_at {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    midEtaPoint n r η ≠ 0 :=
  fun h => (saddleU_pos hn hr).ne' (by simpa using congrArg Complex.re h)

theorem continuous_midPhase {r : ℝ} (hr : 1 ≤ r) (p : ℤ) : Continuous (midPhase r p) := by
  unfold midPhase
  exact ((continuous_const.sub ((Complex.continuous_ofReal : Continuous fun x : ℝ => (x : ℂ)).pow 2))).sub
    (continuous_saddleG (midModeRadius_abs_le_one hr p))

theorem continuous_midIntegrand {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 ≤ r) (p : ℤ) :
    Continuous (fun x : ℝ × ℝ => midIntegrand n r p x.1 x.2) := by
  let ζ (x : ℝ × ℝ) := midEtaPoint n r x.1
  let q (x : ℝ × ℝ) := midEtaTransform (ζ x)
  have hζ : Continuous ζ := (continuous_midEtaPoint n r).comp continuous_fst
  have hp : 0 < r := by positivity
  have hnζ (x : ℝ × ℝ) : ζ x ≠ 0 := midEtaPoint_nonzero_at hn hp x.1
  have hq : Continuous q := continuous_const.div hζ hnζ
  have hpq (x : ℝ × ℝ) : 0 < (q x).re := by
    dsimp only [q, ζ]
    rw [re_midEtaTransform_midEtaPoint hn hp]
    have hu := saddleU_pos hn hp
    positivity
  have hEuler : Continuous (fun x => eulerProduct (q x)) :=
    continuousOn_eulerProduct_right.comp_continuous hq hpq
  have hEulerNZ (x : ℝ × ℝ) : eulerProduct (q x) ^ 2 ≠ 0 :=
    pow_ne_zero _ (eulerProduct_ne_zero_of_re_pos (hpq x))
  have hG := (continuous_saddleG (midModeRadius_abs_le_one hr p)).comp
    (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  have hPL₀ := (continuous_pairedLog_vertical (midModeRadius r p)
    (midModeRadius_abs_le_one hr p) (saddleU_pos hn hp)).comp
      (show Continuous (fun x : ℝ × ℝ => (midU n r * x.1, x.2)) by fun_prop)
  have hPL : Continuous (fun x : ℝ × ℝ => pairedLog (midModeRadius r p) x.2 (ζ x)) := by
    simpa only [Function.comp_def, ζ, midEtaPoint_eq_vertical] using hPL₀
  have hP := (continuous_midPhase hr p).comp
    (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  have hEP : Continuous (fun x : ℝ × ℝ => exp ((n : ℂ) * ζ x + midPhase r p x.2 / ζ x)) :=
    Complex.continuous_exp.comp ((continuous_const.mul hζ).add (hP.div hζ hnζ))
  have hE : Continuous (fun x : ℝ × ℝ => exp (-ζ x / 12) / eulerProduct (q x) ^ 2) :=
    (Complex.continuous_exp.comp (hζ.neg.div_const 12)).div (hEuler.pow 2) hEulerNZ
  have hEL : Continuous (fun x : ℝ × ℝ =>
      exp (saddleG (midModeRadius r p) x.2 / ζ x - pairedLog (midModeRadius r p) x.2 (ζ x))) :=
    Complex.continuous_exp.comp ((hG.div hζ hnζ).sub hPL)
  exact hEP.mul (hE.mul hEL)

end DurfeeCCS.Step09
