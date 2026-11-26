module

public import DurfeeCCS.Step10.OuterRho
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The antiderivative and the squared-scale derivative for the outer Bessel transform. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Complex Filter Set MeasureTheory intervalIntegral DurfeeCCS.Step06

theorem outerRoot_slit {ζ : ℂ} (hζ : 0 < ζ.re) {u : ℝ} (hu : 0 ≤ u) :
    ζ ^ 2 + (u : ℂ) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  by_cases hz : ζ.im = 0
  · left
    rw [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, hz]
    simpa only [mul_zero, sub_zero] using (add_pos_of_pos_of_nonneg (mul_pos hζ hζ) hu)
  · right
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_im, add_zero]
    rw [mul_comm ζ.im ζ.re, ← two_mul]
    exact mul_ne_zero (by norm_num) (mul_ne_zero hζ.ne' hz)

private theorem hasDerivAt_outerRoot {ζ : ℂ} (hζ : 0 < ζ.re) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun w : ℝ => (ζ ^ 2 + (w : ℂ)).sqrt)
      (1 / (2 * (ζ ^ 2 + (u : ℂ)).sqrt)) u := by
  have hz := outerRoot_slit hζ hu
  have hp := (Complex.hasDerivAt_sqrt hz).comp (u : ℂ)
    ((hasDerivAt_id (u : ℂ)).const_add (ζ ^ 2))
  convert hp.comp_ofReal using 1 <;> try rfl
  change 1 / (2 * (ζ ^ 2 + (u : ℂ)).sqrt) = (ζ ^ 2 + (u : ℂ)) ^ (-1 / 2 : ℂ) / 2 * 1
  rw [mul_one, show (-1 / 2 : ℂ) = -(2 : ℂ)⁻¹ by norm_num, Complex.cpow_neg]
  change 1 / (2 * (ζ ^ 2 + (u : ℂ)).sqrt) = ((ζ ^ 2 + (u : ℂ)).sqrt)⁻¹ / 2
  ring

/-- Derivative in the nonnegative squared scale, with the same branch as in (73). -/
theorem sinhKernelDerivative {ζ : ℂ} (hζ : 0 < ζ.re) {u : ℝ} (hu : 0 ≤ u) (y : ℝ) :
    HasDerivAt
      (fun s : ℝ => Complex.sinh ((y : ℂ) * (ζ ^ 2 + (s : ℂ)).sqrt) /
        (ζ ^ 2 + (s : ℂ)).sqrt)
      ((y : ℂ) * Complex.cosh ((y : ℂ) * (ζ ^ 2 + (u : ℂ)).sqrt) / (2 * (ζ ^ 2 + (u : ℂ))) -
        Complex.sinh ((y : ℂ) * (ζ ^ 2 + (u : ℂ)).sqrt) / (2 * (ζ ^ 2 + (u : ℂ)).sqrt ^ 3)) u := by
  let z := (ζ ^ 2 + (u : ℂ)).sqrt
  have hn : z ≠ 0 := by
    intro H
    apply Complex.slitPlane_ne_zero (outerRoot_slit hζ hu)
    rw [← principalSqrt_sq (ζ ^ 2 + (u : ℂ))]
    change z ^ 2 = 0
    simp [H]
  have hd : HasDerivAt (fun w : ℝ => (ζ ^ 2 + (w : ℂ)).sqrt) (1 / (2 * z)) u :=
    hasDerivAt_outerRoot hζ hu
  have hnum : HasDerivAt (fun w : ℝ => sinh ((y : ℂ) * (ζ ^ 2 + (w : ℂ)).sqrt))
      (cosh ((y : ℂ) * z) * ((y : ℂ) * (1 / (2 * z)))) u := by
    simpa only [Function.comp_def, smul_eq_mul, mul_comm _ (cosh ((y : ℂ) * z))] using
      (Complex.hasDerivAt_sinh ((y : ℂ) * z)).scomp u (hd.const_mul (y : ℂ))
  have h := hnum.fun_div hd hn
  refine h.congr_deriv ?_
  symm
  have hsq : z ^ 2 = ζ ^ 2 + (u : ℂ) := principalSqrt_sq _
  change (y : ℂ) * cosh ((y : ℂ) * z) / (2 * (ζ ^ 2 + (u : ℂ))) -
    sinh ((y : ℂ) * z) / (2 * z ^ 3) =
      (cosh ((y : ℂ) * z) * ((y : ℂ) * (1 / (2 * z))) * z -
        sinh ((y : ℂ) * z) * (1 / (2 * z))) / z ^ 2
  rw [← hsq]
  field_simp [hn]

/-- Primitive in the complex square-root variable used in (70). -/
def kernelEndpoint (y : ℝ) (Q z : ℂ) : ℂ :=
  (Q - z ^ 2) * Complex.cosh ((y : ℂ) * z) / (y : ℂ) +
    2 * z * Complex.sinh ((y : ℂ) * z) / (y : ℂ) ^ 2 -
    2 * Complex.cosh ((y : ℂ) * z) / (y : ℂ) ^ 3

theorem hasDerivAt_kernelEndpoint {y : ℝ} (hy : y ≠ 0) (Q z : ℂ) :
    HasDerivAt (kernelEndpoint y Q) ((Q - z ^ 2) * Complex.sinh ((y : ℂ) * z)) z := by
  have hd := hasDerivAt_id z
  have hs := (hd.const_mul (y : ℂ)).csinh
  have hc := (hd.const_mul (y : ℂ)).ccosh
  have h := ((((hd.pow 2).const_sub Q).mul hc).div_const (y : ℂ)).add
    ((((hd.const_mul (2 : ℂ)).mul hs).div_const ((y : ℂ) ^ 2))) |>.sub
      ((hc.const_mul (2 : ℂ)).div_const ((y : ℂ) ^ 3))
  refine h.congr_deriv ?_
  simp only [id_eq, Pi.pow_apply, mul_one, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 by decide, pow_one]
  field_simp [Complex.ofReal_ne_zero.mpr hy]
  ring

/-- The integral expression at the right-hand side of (69). -/
def kernelTransformIntegralFormula (y : ℝ) (ζ : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) ^ 3 / 9) *
    ∫ t in (0 : ℝ)..1,
      let z := (ζ ^ 2 + ((4 * Real.pi ^ 2 / 3 * t ^ 2 : ℝ) : ℂ)).sqrt
      ((t * (1 - t ^ 2) : ℝ) : ℂ) *
        (Complex.sinh ((y : ℂ) * z) / z - Complex.sinh ((y : ℂ) * ζ) / ζ)

theorem principalSqrt_zeta_sq {ζ : ℂ} (hζ : 0 < ζ.re) : (ζ ^ 2).sqrt = ζ := by
  have hs : (ζ ^ 2).sqrt ^ 2 = ζ ^ 2 := principalSqrt_sq _
  have hr : 0 ≤ (ζ ^ 2).sqrt.re := by
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp <;> positivity
  rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hs with he | he
  · exact he
  · rw [he, Complex.neg_re] at hr
    linarith

private theorem hasDerivAt_kernelEndpointParam {y : ℝ} (hy : y ≠ 0) {ζ : ℂ} (hζ : 0 < ζ.re)
    {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    let z := (ζ ^ 2 + ((a * t ^ 2 : ℝ) : ℂ)).sqrt
    HasDerivAt (fun s : ℝ => kernelEndpoint y (ζ ^ 2 + (a : ℂ))
      (ζ ^ 2 + ((a * s ^ 2 : ℝ) : ℂ)).sqrt)
      ((a : ℂ) ^ 2 * ((t * (1 - t ^ 2) : ℝ) : ℂ) * Complex.sinh ((y : ℂ) * z) / z) t := by
  dsimp only
  let z := (ζ ^ 2 + ((a * t ^ 2 : ℝ) : ℂ)).sqrt
  have ht := ((hasDerivAt_id t).pow 2).const_mul a
  have hd := (hasDerivAt_outerRoot hζ (by positivity : 0 ≤ a * t ^ 2)).scomp t ht
  have h := (hasDerivAt_kernelEndpoint hy (ζ ^ 2 + (a : ℂ)) z).scomp t hd
  refine h.congr_deriv ?_
  symm
  simp only [id_eq, mul_one, show (2 - 1 : ℕ) = 1 by decide, pow_one, Complex.real_smul,
    smul_eq_mul, Nat.cast_ofNat]
  rw [show ((a * (2 * t) : ℝ) : ℂ) = (a : ℂ) * (2 * (t : ℂ)) by push_cast; rfl]
  change _ = (↑a * (2 * ↑t) * (1 / (2 * z))) *
    (((ζ ^ 2 + (a : ℂ)) - z ^ 2) * sinh ((y : ℂ) * z))
  rw [show z ^ 2 = ζ ^ 2 + ((a * t ^ 2 : ℝ) : ℂ) from principalSqrt_sq _]
  push_cast [z]
  ring

/-- Evaluation of the manuscript's integral expression by its two endpoint values. -/
theorem kernelTransformIntegral_endpoints {y : ℝ} {ζ : ℂ} (hy : y ≠ 0) (hζ : 0 < ζ.re) :
    kernelTransformIntegralFormula y ζ + (Real.pi : ℂ) ^ 3 * Complex.sinh ((y : ℂ) * ζ) / (18 * ζ) =
      (1 / (8 * (Real.pi : ℂ))) *
        (kernelEndpoint y (ζ ^ 2 + ((4 * Real.pi ^ 2 / 3 : ℝ) : ℂ))
          (ζ ^ 2 + ((4 * Real.pi ^ 2 / 3 : ℝ) : ℂ)).sqrt -
        kernelEndpoint y (ζ ^ 2 + ((4 * Real.pi ^ 2 / 3 : ℝ) : ℂ)) ζ) := by
  let a := 4 * Real.pi ^ 2 / 3
  let z (t : ℝ) := (ζ ^ 2 + ((a * t ^ 2 : ℝ) : ℂ)).sqrt
  let A (t : ℝ) := ((t * (1 - t ^ 2) : ℝ) : ℂ)
  let f (t : ℝ) := A t * Complex.sinh ((y : ℂ) * z t) / z t
  let b := Complex.sinh ((y : ℂ) * ζ) / ζ
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hz (t : ℝ) : z t ≠ 0 := by
    intro H
    have H' := principalSqrt_sq (ζ ^ 2 + ((a * t ^ 2 : ℝ) : ℂ))
    change z t ^ 2 = _ at H'
    rw [H, zero_pow (by decide : (2 : ℕ) ≠ 0)] at H'
    exact Complex.slitPlane_ne_zero (outerRoot_slit hζ (by positivity : 0 ≤ a * t ^ 2)) H'.symm
  have hzc : Continuous z := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hzc' := (hasDerivAt_outerRoot hζ (by positivity : 0 ≤ a * t ^ 2)).continuousAt
    exact hzc'.comp (f := fun s : ℝ => a * s ^ 2) (by fun_prop)
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hf : Continuous f := (hA.mul (Complex.continuous_sinh.comp (hzc.const_mul (y : ℂ)))).div hzc hz
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun t _ => hasDerivAt_kernelEndpointParam hy hζ ha t)
    (((hf.const_mul ((a : ℂ) ^ 2)).intervalIntegrable 0 1).congr
      (fun t _ => by dsimp [f, A, z]; ring))
  have H' : ((a : ℂ) ^ 2) * (∫ t in (0 : ℝ)..1, f t) =
      kernelEndpoint y (ζ ^ 2 + (a : ℂ)) (ζ ^ 2 + (a : ℂ)).sqrt -
        kernelEndpoint y (ζ ^ 2 + (a : ℂ)) ζ := by
    rw [← intervalIntegral.integral_const_mul]
    convert H using 1
    · apply intervalIntegral.integral_congr
      intro t _
      dsimp [f, z, A]
      ring
    · simp [principalSqrt_zeta_sq hζ]
  have hAint : (∫ t in (0 : ℝ)..1, A t) = 1 / 4 := by
    have hi := integral_pow (a := (0 : ℝ)) (b := 1) 3
    have hj := integral_pow (a := (0 : ℝ)) (b := 1) 1
    have he (t : ℝ) : A t = ((t - t ^ 3 : ℝ) : ℂ) := by dsimp [A]; push_cast; ring
    simp_rw [he]
    rw [intervalIntegral.integral_ofReal]
    have hx : IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
      continuous_id.intervalIntegrable _ _
    have hx3 : IntervalIntegrable (fun t : ℝ => t ^ 3) volume 0 1 :=
      (continuous_id.pow 3).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hx hx3, hi]
    simp only [pow_one] at hj
    rw [hj]
    norm_num
  have hi : kernelTransformIntegralFormula y ζ = (2 * (Real.pi : ℂ) ^ 3 / 9) *
      ((∫ t in (0 : ℝ)..1, f t) - (1 / 4) * b) := by
    rw [kernelTransformIntegralFormula, ← hAint, ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) ((hA.mul_const b).intervalIntegrable _ _)]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [f, A, z, b]
    ring
  rw [hi]
  change _ = (1 / (8 * (Real.pi : ℂ))) *
    (kernelEndpoint y (ζ ^ 2 + (a : ℂ)) (ζ ^ 2 + (a : ℂ)).sqrt -
      kernelEndpoint y (ζ ^ 2 + (a : ℂ)) ζ)
  rw [← H']
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp [a, b]
  push_cast
  field_simp [hpi]
  ring

end DurfeeCCS.Step10
