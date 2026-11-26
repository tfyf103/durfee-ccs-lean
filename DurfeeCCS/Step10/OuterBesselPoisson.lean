module

public import DurfeeCCS.Step10.OuterBesselKernel
public import DurfeeCCS.Step10.OuterErrorLattice
public import Mathlib.Analysis.Fourier.PoissonSummation

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Absolute convergence and shifted Poisson summation for the outer kernel. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open MeasureTheory Set Filter Complex intervalIntegral Asymptotics
open scoped FourierTransform ContDiff

private def smoothKernel (y x : ℝ) : ℂ :=
  (outerBesselCore (y ^ 2 - x ^ 2) : ℂ)

private theorem contDiff_smoothKernel (y : ℝ) : ContDiff ℝ 2 (smoothKernel y) := by
  exact Complex.ofRealCLM.contDiff.comp (contDiff_outerBesselCore.comp (by fun_prop))

private theorem smoothKernel_boundary (y : ℝ) : smoothKernel y y = 0 ∧ smoothKernel y (-y) = 0 := by
  simp [smoothKernel]

private theorem hasDerivAt_outerExp (ζ : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (ζ * (t : ℂ))) (ζ * Complex.exp (ζ * (x : ℂ))) x := by
  have h := (((hasDerivAt_id (x : ℂ)).const_mul ζ).cexp).comp_ofReal
  simpa [mul_comm] using h

private theorem transform_by_parts {y : ℝ} (hy : 0 ≤ y) {ζ : ℂ} (hζ : ζ ≠ 0) :
    kernelTransform y ζ * ζ ^ 2 =
      (∫ x in -y..y, deriv (deriv (smoothKernel y)) x * Complex.exp (ζ * (x : ℂ))) -
        deriv (smoothKernel y) y * Complex.exp (ζ * (y : ℂ)) +
        deriv (smoothKernel y) (-y) * Complex.exp (ζ * ((-y : ℝ) : ℂ)) := by
  let f := smoothKernel y
  let E (x : ℝ) := Complex.exp (ζ * (x : ℂ))
  let P (x : ℝ) := f x * E x / ζ - deriv f x * E x / ζ ^ 2
  have hf : ContDiff ℝ 2 f := contDiff_smoothKernel y
  have hf₁ : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf₁d : Differentiable ℝ (deriv f) := hf₁.differentiable (by norm_num)
  have hcE : Continuous E := by dsimp [E]; fun_prop
  have hc₂ : Continuous (fun x => deriv (deriv f) x * E x / ζ ^ 2) :=
    (hf₁.continuous_deriv_one.mul hcE).div_const (ζ ^ 2)
  have hc₀ : Continuous (fun x => f x * E x) := hf.continuous.mul hcE
  have hP (x : ℝ) : HasDerivAt P
      (f x * E x - deriv (deriv f) x * E x / ζ ^ 2) x := by
    have hE := hasDerivAt_outerExp ζ x
    have hp := ((((hfd x).hasDerivAt).mul hE).div_const ζ).sub
      ((((hf₁d x).hasDerivAt).mul hE).div_const (ζ ^ 2))
    convert hp using 1
    field_simp [hζ]
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -y) (b := y)
    (fun x _ => hP x) ((hc₀.sub hc₂).intervalIntegrable _ _)
  rw [intervalIntegral.integral_sub (hc₀.intervalIntegrable _ _) (hc₂.intervalIntegrable _ _),
    intervalIntegral.integral_div] at H
  have hfz : f y = 0 ∧ f (-y) = 0 := smoothKernel_boundary y
  simp only [P, hfz.1, hfz.2, zero_mul, zero_div, zero_sub] at H
  rw [kernelTransform_eq_core hy]
  change (∫ x in -y..y, f x * E x) * ζ ^ 2 =
    (∫ x in -y..y, deriv (deriv f) x * E x) - deriv f y * E y + deriv f (-y) * E (-y)
  field_simp [hζ] at H
  linear_combination H

/-- Two integrations by parts give a uniform inverse-square bound on each vertical line. -/
theorem kernelTransform_vertical_bound {y : ℝ} (hy : 0 ≤ y) (h : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, v ≠ 0 →
      ‖kernelTransform y ((h : ℂ) + (v : ℂ) * I)‖ ≤ C / v ^ 2 := by
  let f := smoothKernel y
  let B := Real.exp (|h| * y)
  let C := B * ((∫ x in -y..y, ‖deriv (deriv f) x‖) + ‖deriv f y‖ + ‖deriv f (-y)‖)
  have hy' : -y ≤ y := by linarith
  have hc₂ : Continuous (deriv (deriv f)) :=
    ((show ContDiff ℝ (1 + 1) f from contDiff_smoothKernel y).deriv').continuous_deriv_one
  have hconst : 0 ≤ C := by
    have hi : 0 ≤ ∫ x in -y..y, ‖deriv (deriv f) x‖ :=
      intervalIntegral.integral_nonneg hy' (fun _ _ => norm_nonneg _)
    positivity
  refine ⟨C, hconst, ?_⟩
  intro v hv
  let ζ : ℂ := (h : ℂ) + (v : ℂ) * I
  have hvb : |v| ≤ ‖ζ‖ := by
    simpa [ζ, Complex.add_im, Complex.mul_im] using Complex.abs_im_le_norm ζ
  have hζ : ζ ≠ 0 := by
    intro hz
    exact hv (abs_eq_zero.mp (le_antisymm (hvb.trans_eq (by simp [hz])) (abs_nonneg _)))
  let E (x : ℝ) := Complex.exp (ζ * (x : ℂ))
  have hexp (x : ℝ) (hx : x ∈ Icc (-y) y) : ‖E x‖ ≤ B := by
    change ‖Complex.exp (ζ * (x : ℂ))‖ ≤ Real.exp (|h| * y)
    rw [Complex.norm_exp, mul_comm ζ, Complex.re_ofReal_mul, Real.exp_le_exp]
    have hrex : ζ.re = h := by simp [ζ, Complex.add_re, Complex.mul_re]
    rw [hrex]
    calc
      x * h ≤ |x * h| := le_abs_self _
      _ = |x| * |h| := abs_mul _ _
      _ ≤ |h| * y := by
        rw [mul_comm |h| y]
        exact mul_le_mul_of_nonneg_right (abs_le.2 hx) (abs_nonneg _)
  have hint : ‖∫ x in -y..y, deriv (deriv f) x * E x‖ ≤
      B * ∫ x in -y..y, ‖deriv (deriv f) x‖ := by
    have he : Continuous E := by dsimp [E]; fun_prop
    refine (intervalIntegral.norm_integral_le_integral_norm hy').trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hy' ((hc₂.mul he).norm.intervalIntegrable _ _)
      ((hc₂.norm.const_mul B).intervalIntegrable _ _) (fun x hx => ?_)
    rw [norm_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hexp x hx) (norm_nonneg _)
  have h₁ := norm_sub_le (∫ x in -y..y, deriv (deriv f) x * E x) (deriv f y * E y)
  have h₂ := norm_add_le ((∫ x in -y..y, deriv (deriv f) x * E x) - deriv f y * E y)
    (deriv f (-y) * E (-y))
  have hb : ‖kernelTransform y ζ‖ * ‖ζ‖ ^ 2 ≤ C := by
    rw [← norm_pow, ← norm_mul, transform_by_parts hy hζ]
    change ‖(∫ x in -y..y, deriv (deriv f) x * E x) - deriv f y * E y + deriv f (-y) * E (-y)‖ ≤ C
    have hpos := mul_le_mul_of_nonneg_left (hexp y ⟨hy', le_rfl⟩) (norm_nonneg (deriv f y))
    have hneg := mul_le_mul_of_nonneg_left (hexp (-y) ⟨le_rfl, hy'⟩) (norm_nonneg (deriv f (-y)))
    rw [norm_mul] at h₁ h₂
    dsimp [C]
    linarith
  apply (le_div_iff₀ (sq_pos_of_ne_zero hv)).2
  calc
    _ ≤ ‖kernelTransform y ζ‖ * ‖ζ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [← sq_abs v]
      exact pow_le_pow_left₀ (abs_nonneg _) hvb 2
    _ ≤ C := hb


/-- The full odd-frequency series is absolutely convergent on every vertical line. -/
theorem summable_kernelTransform_odd {y : ℝ} (hy : 0 ≤ y) (h : ℝ) :
    Summable (fun m : ℤ => ‖kernelTransform y ((h : ℂ) + (outerFrequency m : ℂ) * I)‖) := by
  obtain ⟨C, hC, hbound⟩ := kernelTransform_vertical_bound hy h
  let f (m : ℤ) := ‖kernelTransform y ((h : ℂ) + (outerFrequency m : ℂ) * I)‖
  let g (m : ℕ) := (C / Real.pi ^ 2) * (1 / ((m + 1 : ℕ) : ℝ) ^ 2)
  have hg : Summable g :=
    ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
      Nat.succ_injective).mul_left _
  have hcomp (m : ℕ) : 0 < outerPositiveFrequency m ∧
      Real.pi * ((m + 1 : ℕ) : ℝ) ≤ outerPositiveFrequency m := by
    refine ⟨outerPositiveFrequency_pos m, ?_⟩
    rw [outerPositiveFrequency, outerFrequency_nat, mul_comm Real.pi]
    push_cast
    exact mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) m])
      Real.pi_pos.le
  have hcmp (m : ℕ) : C / (outerPositiveFrequency m) ^ 2 ≤ g m := by
    dsimp [g]
    rw [mul_one_div, div_div, ← mul_pow]
    exact div_le_div_of_nonneg_left hC (by positivity)
      (pow_le_pow_left₀ (by positivity) (hcomp m).2 2)
  have hp : Summable (fun m : ℕ => f m) := hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m =>
    (hbound _ (hcomp m).1.ne').trans (hcmp m))
  have hn : Summable (fun m : ℕ => f (-(m + 1 : ℤ))) := by
    apply hg.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro m
    simp only [outerFrequency_neg_nat]
    exact (hbound _ (neg_ne_zero.mpr (hcomp m).1.ne')).trans (by simpa only [neg_sq] using hcmp m)
  exact (hp.hasSum.of_nat_of_neg_add_one hn.hasSum).summable

private def modulatedKernel (y h x : ℝ) : ℂ :=
  (outerBesselKernel y x : ℂ) * Complex.exp (((h : ℂ) + (Real.pi : ℂ) * I) * (x : ℂ))

private theorem fourier_modulatedKernel {y : ℝ} (hy : 0 ≤ y) (h w : ℝ) :
    𝓕 (modulatedKernel y h) w =
      kernelTransform y ((h : ℂ) + ((Real.pi - 2 * Real.pi * w : ℝ) : ℂ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, kernelTransform,
    intervalIntegral.integral_eq_integral_of_support_subset]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    rw [smul_eq_mul, modulatedKernel, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · intro x hx
    have hk : outerBesselKernel y x ≠ 0 := by
      intro H
      simp [Function.mem_support, H] at hx
    exact ⟨by
      contrapose! hk
      exact outerBesselKernel_eq_zero hy (by rw [← abs_neg x]; exact (show y ≤ -x by linarith).trans (le_abs_self _)),
      by
        contrapose! hk
        exact outerBesselKernel_eq_zero hy (hk.le.trans (le_abs_self _))⟩

private theorem eventually_abs_ge (a : ℝ) : ∀ᶠ x : ℝ in cocompact ℝ, a ≤ |x| := by
  filter_upwards [(isCompact_Icc (a := -a) (b := a)).compl_mem_cocompact] with x hx
  by_contra! h
  exact hx (abs_le.mp h.le)

/-- Poisson summation on an arbitrary translate, with the alternating factor on the integer index. -/
theorem shifted_outerBessel_poisson {y : ℝ} (hy : 0 ≤ y) (h a : ℝ) :
    (∑' d : ℤ, (-(Real.exp h : ℂ)) ^ d * (outerBesselKernel y ((d : ℝ) + a) : ℂ)) =
      (Real.exp (-h * a) : ℂ) *
        ∑' m : ℤ, Complex.exp (-((outerFrequency m * a : ℝ) : ℂ) * I) *
          kernelTransform y ((h : ℂ) + (outerFrequency m : ℂ) * I) := by
  have hc : Continuous (modulatedKernel y h) := by
    unfold modulatedKernel
    exact (Complex.continuous_ofReal.comp (continuous_outerBesselKernel y)).mul (by fun_prop)
  have hzero : modulatedKernel y h =ᶠ[cocompact ℝ] 0 := by
    filter_upwards [eventually_abs_ge y] with x hx
    simp [modulatedKernel, outerBesselKernel_eq_zero hy hx]
  have hdecay : Asymptotics.IsBigO (cocompact ℝ) (modulatedKernel y h) (|·| ^ (-(2 : ℝ))) :=
    (isBigO_congr hzero EventuallyEq.rfl).mpr (isBigO_zero _ _)
  obtain ⟨C, hC, hbound⟩ := kernelTransform_vertical_bound hy h
  have hFdecay : Asymptotics.IsBigO (cocompact ℝ) (𝓕 (modulatedKernel y h)) (|·| ^ (-(2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound (C / Real.pi ^ 2) ?_
    filter_upwards [eventually_abs_ge 1] with w hw
    have hw' : 0 < |w| := by linarith
    let v : ℝ := Real.pi - 2 * Real.pi * w
    have hv : Real.pi * |w| ≤ |v| := by
      have hh := abs_sub_abs_le_abs_sub (2 * Real.pi * w) Real.pi
      rw [abs_sub_comm, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi),
        abs_of_pos Real.pi_pos] at hh
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hw)]
    have hv' : 0 < |v| := (mul_pos Real.pi_pos hw').trans_le hv
    have hs := pow_le_pow_left₀ (by positivity) hv 2
    rw [mul_pow, sq_abs, sq_abs] at hs
    rw [fourier_modulatedKernel hy, Real.norm_eq_abs, Real.rpow_neg hw'.le,
      show (2 : ℝ) = (↑(2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      abs_of_nonneg (by positivity), sq_abs]
    change ‖kernelTransform y ((h : ℂ) + (v : ℂ) * I)‖ ≤ C / Real.pi ^ 2 * (w ^ 2)⁻¹
    rw [← div_eq_mul_inv, div_div]
    exact (hbound v (abs_pos.mp hv')).trans (div_le_div_of_nonneg_left hC
      (mul_pos (sq_pos_of_ne_zero Real.pi_ne_zero) (sq_pos_of_ne_zero (abs_pos.mp hw'))) hs)
  have hpo := Real.tsum_eq_tsum_fourier_of_rpow_decay hc (by norm_num : (1 : ℝ) < 2)
    hdecay hFdecay a
  let c : ℂ := Complex.exp (-((h : ℂ) + (Real.pi : ℂ) * I) * (a : ℂ))
  let z : ℂ := (h : ℂ) + (Real.pi : ℂ) * I
  have lhs : (∑' d : ℤ, (-(Real.exp h : ℂ)) ^ d * (outerBesselKernel y ((d : ℝ) + a) : ℂ)) =
      c * ∑' d : ℤ, modulatedKernel y h (a + (d : ℝ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro d
    have he : Complex.exp z = -(Real.exp h : ℂ) := by
      dsimp [z]
      rw [Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, mul_neg_one]
    have hexp : Complex.exp (d * z) =
        c * Complex.exp (z * ((a + (d : ℝ) : ℝ) : ℂ)) := by
      dsimp [c, z]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← he, ← Complex.exp_int_mul, hexp, modulatedKernel, add_comm (d : ℝ) a]
    change _ = c * (↑(outerBesselKernel y (a + ↑d)) * Complex.exp (z * ↑(a + (d : ℝ))))
    ring
  rw [lhs, hpo, ← tsum_mul_left (a := c), ← (Equiv.neg ℤ).tsum_eq,
    ← tsum_mul_left (a := (Real.exp (-h * a) : ℂ))]
  apply tsum_congr
  intro m
  change c * (𝓕 (modulatedKernel y h) (↑(-m) : ℝ) * fourier (-m) (a : UnitAddCircle)) =
    (Real.exp (-h * a) : ℂ) * (Complex.exp (-((outerFrequency m * a : ℝ) : ℂ) * I) *
      kernelTransform y ((h : ℂ) + (outerFrequency m : ℂ) * I))
  have hv : Real.pi - 2 * Real.pi * ((-m : ℤ) : ℝ) = outerFrequency m := by
    push_cast [outerFrequency]
    ring
  rw [fourier_modulatedKernel hy, hv, fourier_coe_apply]
  dsimp [c]
  rw [mul_comm (kernelTransform _ _), ← mul_assoc, ← Complex.exp_add,
      Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast [outerFrequency]
  ring

end DurfeeCCS.Step10
