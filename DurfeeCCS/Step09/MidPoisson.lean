module

public import DurfeeCCS.Step09.MidPoissonProduct
public import DurfeeCCS.Step09.MidPoissonGaussian
public import DurfeeCCS.Step09.MidPoissonLattice
public import DurfeeCCS.Step06.Branches
public import DurfeeCCS.Step08.AngularMeans

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Equation (47) as an absolutely convergent sum of integrals. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory DurfeeCCS.Step06 DurfeeCCS.Step08

def midPoissonModeBound (r u c C : ℝ) (p : ℤ) : ℝ :=
  (Real.exp (C * (Real.log r)^2 + 2 * C^2 * (Real.log r)^2 / c +
    (c / 2) * (Real.pi / 2)^2) / pairedEulerLower u ^ 2) *
    Real.exp (-(c * Real.pi ^ 2 / 4) * (p : ℝ) ^ 2)

theorem midPoissonModeBound_summable (r u : ℝ) {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Summable (midPoissonModeBound r u c C) :=
  (summable_int_real_gaussian (c := c * Real.pi ^ 2 / 4) (by positivity)).mul_left _

/-- A separable, absolutely summable and integrable bound for the Poisson kernel. -/
theorem norm_midPoissonMode_le {r u c C : ℝ} {ζ : ℂ} (hr : 1 ≤ r) (hu : 0 < u)
    (hζ : u ≤ ζ.re) (hc : 0 < c) (hlo : c ≤ ζ⁻¹.re) (hhi : ‖ζ⁻¹‖ ≤ C) (p : ℤ)
    (χ : ℝ) :
    ‖midPoissonMode r ζ p χ‖ ≤ midPoissonModeBound r u c C p * Real.exp (-c * χ ^ 2) := by
  have hP := pairedEulerLower_sq_le_norm_pairedProduct hu (midModeRadius_abs_le_one hr p) hζ χ
  have hL : 0 < pairedEulerLower u ^ 2 := sq_pos_of_pos (pairedEulerLower_pos hu)
  have hE := norm_exp_midFrequency_le (r := r) (p := p) hc hlo hhi
  have hG : ‖exp (-(χ : ℂ) ^ 2 / ζ)‖ ≤ Real.exp (-c * χ ^ 2) := by
    rw [norm_exp, div_eq_mul_inv, ← Complex.ofReal_pow, ← Complex.ofReal_neg, Complex.re_ofReal_mul]
    exact Real.exp_le_exp.2 (by linarith [mul_le_mul_of_nonneg_right hlo (sq_nonneg χ)])
  have hden := div_le_div₀ (Real.exp_nonneg _) hG hL hP
  rw [midPoissonMode, norm_mul, norm_div]
  refine (mul_le_mul hE hden (by positivity) (by positivity)).trans_eq ?_
  unfold midPoissonModeBound
  ring

/-- Continuity in both real integration variables on each fixed vertical line. -/
theorem continuous_midPoissonMode_vertical {r u : ℝ} (hr : 1 ≤ r) (hu : 0 < u) (p : ℤ) :
    Continuous (fun x : ℝ × ℝ => midPoissonMode r (verticalPoint u x.1) p x.2) := by
  have hζ : Continuous (fun x : ℝ × ℝ => verticalPoint u x.1) := by unfold verticalPoint; fun_prop
  have hz (x : ℝ × ℝ) : verticalPoint u x.1 ≠ 0 := fun he => by
    have hh := congrArg Complex.re he
    simp at hh
    exact hu.ne' hh
  have hnum : Continuous (fun x : ℝ × ℝ =>
      exp (-(x.2 : ℂ)^2 / verticalPoint u x.1)) :=
    Complex.continuous_exp.comp ((by fun_prop :
      Continuous (fun x : ℝ × ℝ => -(x.2 : ℂ)^2)).div hζ hz)
  have hfreq : Continuous (fun x : ℝ × ℝ =>
      exp (((Real.log r : ℂ) + (midFrequency p : ℂ) * I) ^ 2 / verticalPoint u x.1)) :=
    Complex.continuous_exp.comp (continuous_const.div hζ hz)
  exact hfreq.mul (hnum.div (continuous_pairedProduct_vertical_small (midModeRadius r p)
    (midModeRadius_abs_le_one hr p) hu) (fun x => pairedProduct_ne_zero_small
      (midModeRadius_abs_le_one hr p) (by simpa using hu) x.2))

/-- The integrals in (47) converge absolutely for every phase. -/
theorem integrable_midPoissonMode {r : ℝ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : 0 < ζ.re) (p : ℤ) :
    Integrable (midPoissonMode r ζ p) := by
  have hc := re_inv_pos_of_re_pos hζ
  have hc₀ : Integrable (fun χ : ℝ => Real.exp (-ζ⁻¹.re * χ ^ 2)) := integrable_exp_neg_mul_sq hc
  have hp : Continuous (fun χ : ℝ => midPoissonMode r ζ p χ) := by
    have hf := (continuous_midPoissonMode_vertical hr hζ p).comp
      (continuous_const.prodMk continuous_id : Continuous (fun χ : ℝ => (ζ.im, χ)))
    have h : verticalPoint ζ.re ζ.im = ζ := Complex.re_add_im ζ
    simpa only [Function.comp_def, h] using hf
  refine (hc₀.const_mul (midPoissonModeBound r ζ.re ζ⁻¹.re ‖ζ⁻¹‖ p)).mono'
    hp.aestronglyMeasurable (ae_of_all _ fun χ => ?_)
  exact norm_midPoissonMode_le hr hζ le_rfl hc le_rfl le_rfl p χ

private def midPoissonArgument (r θ : ℝ) : ℂ :=
  (Real.log r : ℂ) + ((Real.pi / 2 + θ : ℝ) : ℂ) * I

private theorem exp_midPoissonArgument {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    exp (midPoissonArgument r θ) = (r : ℂ) * I * exp ((θ : ℂ) * I) := by
  have h : (((Real.pi / 2 + θ : ℝ) : ℂ) * I) = (Real.pi : ℂ) / 2 * I + (θ : ℂ) * I := by
    push_cast
    ring
  rw [midPoissonArgument, h, exp_add, exp_add, ← Complex.ofReal_exp, Real.exp_log hr,
    Complex.exp_pi_div_two_mul_I]
  ring

private def midPoissonPair (r : ℝ) (ζ : ℂ) (ij : ℤ × ℤ) (θ : ℝ) : ℂ :=
  thetaGaussian (midPoissonArgument r θ) ζ ij.1 * thetaGaussian (midPoissonArgument r (-θ)) ζ ij.2 /
    pairedProduct (-r⁻¹) θ ζ

private theorem hasSum_integral_midPoissonPair {r : ℝ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : 0 < ζ.re) :
    HasSum (fun ij : ℤ × ℤ => ∫ θ in -Real.pi..Real.pi, midPoissonPair r ζ ij θ)
      (∫ θ in -Real.pi..Real.pi, ∑' ij : ℤ × ℤ, midPoissonPair r ζ ij θ) := by
  let a := Real.log r
  let c := ζ⁻¹.re
  let C := ‖ζ⁻¹‖
  let L := pairedEulerLower ζ.re ^ 2
  let v (j : ℤ) := Real.exp ((C * a ^ 2 + 2 * C ^ 2 * a ^ 2 / c) / 2 +
      c * (3 * Real.pi / 2) ^ 2 / 4) * Real.exp (-(c * Real.pi ^ 2 / 2) * (j : ℝ) ^ 2)
  let V (ij : ℤ × ℤ) := (v ij.1 * v ij.2) / L
  have hc : 0 < c := re_inv_pos_of_re_pos hζ
  have hL : 0 < L := sq_pos_of_pos (pairedEulerLower_pos hζ)
  have hv₀ (j : ℤ) : 0 ≤ v j := by dsimp [v]; positivity
  have hv : Summable v :=
    (summable_int_real_gaussian (c := c * Real.pi ^ 2 / 2) (by positivity)).mul_left _
  have hV : Summable V := by
    simpa only [V, div_eq_mul_inv] using (hv.mul_of_nonneg hv hv₀ hv₀).mul_right L⁻¹
  have hR : |-r⁻¹| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ hr
  have hb (ij : ℤ × ℤ) {θ : ℝ} (ht : |θ| ≤ Real.pi) : ‖midPoissonPair r ζ ij θ‖ ≤ V ij := by
    have hp := pairedEulerLower_sq_le_norm_pairedProduct hζ hR le_rfl θ
    have h₁ : ‖thetaGaussian (midPoissonArgument r θ) ζ ij.1‖ ≤ v ij.1 :=
      norm_thetaGaussian_angle_le hc le_rfl le_rfl ht
    have h₂ : ‖thetaGaussian (midPoissonArgument r (-θ)) ζ ij.2‖ ≤ v ij.2 :=
      norm_thetaGaussian_angle_le hc le_rfl le_rfl (by simpa only [abs_neg] using ht)
    rw [midPoissonPair, norm_div, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul h₁ h₂ (norm_nonneg _) (hv₀ _)) hL hp
  have hf (ij : ℤ × ℤ) : Continuous (midPoissonPair r ζ ij) := by
    unfold midPoissonPair
    have ha : Continuous (fun θ : ℝ => thetaGaussian (midPoissonArgument r θ) ζ ij.1) := by
      unfold thetaGaussian midPoissonArgument
      fun_prop
    have h₂ : Continuous (fun θ : ℝ => thetaGaussian (midPoissonArgument r (-θ)) ζ ij.2) := by
      unfold thetaGaussian midPoissonArgument
      fun_prop
    exact (ha.mul h₂).div (continuous_pairedProduct_angle_small _ hR hζ) (pairedProduct_ne_zero_small hR hζ)
  have hI : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hθ (θ : ℝ) (ht : θ ∈ Set.uIoc (-Real.pi) Real.pi) : |θ| ≤ Real.pi := by
    rw [Set.uIoc_of_le hI] at ht
    exact abs_le.mpr ⟨ht.1.le, ht.2⟩
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (F := midPoissonPair r ζ) (f := fun θ => ∑' ij, midPoissonPair r ζ ij θ)
    (fun ij _ => V ij) (fun ij => (hf ij).aestronglyMeasurable)
    (fun ij => ae_of_all _ fun θ ht => hb ij (hθ θ ht))
    (ae_of_all _ fun _ _ => hV) intervalIntegrable_const
    (ae_of_all _ fun θ ht => (hV.of_norm_bounded (fun ij => hb ij (hθ θ ht))).hasSum)

private theorem pairedProduct_eq_tsum_midPoissonPair {r : ℝ} (hr : 1 ≤ r) {ζ : ℂ}
    (hζ : 0 < ζ.re) (θ : ℝ) :
    pairedProduct r θ ζ = (2 * Real.pi / (ζ * eulerProduct ζ ^ 2)) *
      ∑' ij : ℤ × ℤ, midPoissonPair r ζ ij θ := by
  have hr₀ : 0 < r := by linarith
  have hz : ζ ≠ 0 := by
    intro h
    simp [h] at hζ
  have hR : |-r⁻¹| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ hr
  let P := pairedProduct (-r⁻¹) θ ζ
  have hP : P ≠ 0 := pairedProduct_ne_zero_small hR hζ θ
  have hE := eulerProduct_ne_zero_right hζ
  have h := theta_mul_theta_eq_pairedProduct hr₀.ne' hζ θ
  rw [← exp_midPoissonArgument hr₀ θ, ← exp_midPoissonArgument hr₀ (-θ),
    theta_gaussian_transform hζ, theta_gaussian_transform hζ] at h
  let f := thetaGaussian (midPoissonArgument r θ) ζ
  let g := thetaGaussian (midPoissonArgument r (-θ)) ζ
  have hs : (∑' ij : ℤ × ℤ, midPoissonPair r ζ ij θ) = ((∑' j, f j) * ∑' j, g j) / P := by
    unfold midPoissonPair
    change (∑' ij : ℤ × ℤ, f ij.1 * g ij.2 / P) = _
    simp only [div_eq_mul_inv, tsum_mul_right]
    rw [tsum_mul_tsum_of_summable_norm (thetaGaussian_absolutelyConvergent hζ _)
      (thetaGaussian_absolutelyConvergent hζ _)]
  change ((2 * (Real.pi : ℂ) / ζ).sqrt * (∑' j, f j)) *
    ((2 * (Real.pi : ℂ) / ζ).sqrt * (∑' j, g j)) =
      eulerProduct ζ ^ 2 * pairedProduct r θ ζ * P at h
  have hroot : (2 * (Real.pi : ℂ) / ζ).sqrt ^ 2 = 2 * (Real.pi : ℂ) / ζ := principalSqrt_sq _
  rw [hs]
  calc
    _ = (eulerProduct ζ ^ 2 * pairedProduct r θ ζ * P) / (eulerProduct ζ ^ 2 * P) := by
      field_simp
    _ = _ := by
      rw [← h]
      rw [show (2 * (Real.pi : ℂ) / ζ).sqrt * (∑' j, f j) *
          ((2 * (Real.pi : ℂ) / ζ).sqrt * (∑' j, g j)) =
        (2 * (Real.pi : ℂ) / ζ).sqrt ^ 2 * ((∑' j, f j) * (∑' j, g j)) by ring, hroot]
      field_simp

private theorem midPoissonPair_reindex (r : ℝ) (ζ : ℂ) (p m : ℤ) (θ : ℝ) :
    midPoissonPair r ζ (midPoissonIndex.symm (p, m)) θ =
      midPoissonMode r ζ p (θ + (p + 2 * m : ℤ) * Real.pi) := by
  unfold midPoissonPair midPoissonMode
  rw [pairedProduct_midPoisson_shift, ← mul_div_assoc, ← exp_add]
  unfold thetaGaussian
  rw [← exp_add]
  congr 2
  change (midPoissonArgument r θ + 2 * (Real.pi : ℂ) * I * ((p + m : ℤ) : ℂ)) ^ 2 / (2 * ζ) +
    (midPoissonArgument r (-θ) + 2 * (Real.pi : ℂ) * I * ((-m : ℤ) : ℂ)) ^ 2 / (2 * ζ) = _
  unfold midPoissonArgument midFrequency
  push_cast
  ring_nf
  simp [I_sq]
  ring

/-- The exact Poisson-integral expansion, including the boundary radius one. -/
theorem durfeeAnalyticF_midPoisson {r : ℝ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : 0 < ζ.re) :
    durfeeAnalyticF (-(r : ℂ) ^ 2) (exp (-ζ)) =
      (ζ * eulerProduct ζ ^ 2)⁻¹ *
        (∑' p : ℤ, ∫ χ : ℝ, midPoissonMode r ζ p χ) := by
  have hS := hasSum_integral_midPoissonPair hr hζ
  have hR : Summable (fun ij : ℤ × ℤ => ∫ θ in -Real.pi..Real.pi,
      midPoissonPair r ζ (midPoissonIndex.symm ij) θ) :=
    midPoissonIndex.symm.summable_iff.mpr hS.summable
  have hT : (∑' ij : ℤ × ℤ, ∫ θ in -Real.pi..Real.pi, midPoissonPair r ζ ij θ) =
      ∑' p : ℤ, ∫ χ : ℝ, midPoissonMode r ζ p χ := by
    rw [← midPoissonIndex.symm.tsum_eq (fun ij : ℤ × ℤ =>
      ∫ θ in -Real.pi..Real.pi, midPoissonPair r ζ ij θ), hR.tsum_prod]
    refine tsum_congr fun p => ?_
    simp_rw [midPoissonPair_reindex]
    exact (hasSum_midPoisson_angular_tiles (integrable_midPoissonMode hr hζ p) p).tsum_eq
  rw [durfeeAnalyticF_eq_pairedAngle r hζ]
  simp_rw [pairedProduct_eq_tsum_midPoissonPair hr hζ]
  rw [intervalIntegral.integral_const_mul, ← hS.tsum_eq, hT]
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  field_simp

/-- The separated form of the expansion, as it is written in (47). -/
theorem durfeeAnalyticF_eq_poisson_integrals {r : ℝ} (hr : 1 ≤ r) {ζ : ℂ}
    (hζ : 0 < ζ.re) :
    durfeeAnalyticF (-(r : ℂ) ^ 2) (exp (-ζ)) =
      (ζ * eulerProduct ζ ^ 2)⁻¹ *
        ∑' p : ℤ, exp (((Real.log r : ℂ) + (midFrequency p : ℂ) * I) ^ 2 / ζ) *
          ∫ χ : ℝ, exp (-(χ : ℂ) ^ 2 / ζ) / pairedProduct (midModeRadius r p) χ ζ := by
  simp only [durfeeAnalyticF_midPoisson hr hζ, midPoissonMode, integral_const_mul]

end DurfeeCCS.Step09
