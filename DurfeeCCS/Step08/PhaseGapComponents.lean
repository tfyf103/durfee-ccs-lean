module

public import DurfeeCCS.Step08.PhaseGapIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The real and imaginary angular gaps from equation (22). -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06
open scoped Interval Real

theorem saddleLogArgument_re (θ y : ℝ) : (saddleLogArgument θ y).re = 1 - y^2 := by
  norm_num [saddleLogArgument, pow_two, Complex.mul_re, Complex.mul_im]

theorem saddleLogArgument_im (θ y : ℝ) : (saddleLogArgument θ y).im = 2 * y * Real.cos θ := by
  norm_num [saddleLogArgument, pow_two, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re]

theorem saddleLogArgument_norm_sq (θ y : ℝ) :
    ‖saddleLogArgument θ y‖ ^ 2 = (1 + y^2)^2 - 4 * y^2 * Real.sin θ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, saddleLogArgument_re, saddleLogArgument_im]
  linear_combination 4 * y^2 * Real.sin_sq_add_cos_sq θ

private theorem saddleLogArgument_ne_zero {θ y : ℝ} (hy : y ∈ Ioo 0 1) :
    saddleLogArgument θ y ≠ 0 := by
  intro h
  have hre : 0 < (saddleLogArgument θ y).re := by
    rw [saddleLogArgument_re]
    nlinarith [sq_lt_sq₀ hy.1.le zero_le_one |>.2 hy.2]
  simp [h] at hre

private theorem log_norm_saddleLogArgument_zero (y : ℝ) :
    Real.log ‖saddleLogArgument 0 y‖ = Real.log (1 + y^2) := by
  have hs : ‖saddleLogArgument 0 y‖ = 1 + y^2 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    simp [saddleLogArgument_norm_sq]
  rw [hs]

private theorem saddle_log_real_gap {y : ℝ} (hy : y ∈ Ioo 0 1) (θ : ℝ) :
    2 * y^2 * Real.sin θ ^ 2 / (1 + y^2)^2 ≤
      Real.log ‖saddleLogArgument 0 y‖ - Real.log ‖saddleLogArgument θ y‖ := by
  have hnorm : 0 < ‖saddleLogArgument θ y‖ := norm_pos_iff.mpr (saddleLogArgument_ne_zero hy)
  have hd : 0 < (1 + y^2)^2 := by positivity
  have hp := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos hnorm) hd)
  rw [Real.log_div (by positivity) hd.ne', Real.log_pow, Real.log_pow, Nat.cast_two,
    div_sub_one hd.ne', saddleLogArgument_norm_sq] at hp
  rw [log_norm_saddleLogArgument_zero]
  have h : (((1 + y^2)^2 - 4*y^2*Real.sin θ^2) - (1 + y^2)^2) / (1 + y^2)^2 =
      -(2 * (2*y^2*Real.sin θ^2 / (1+y^2)^2)) := by ring
  rw [h] at hp
  linarith

private theorem saddleLogArgument_arg_eq_arctan {y : ℝ} (hy : y ∈ Ioo 0 1) (θ : ℝ) :
    (saddleLogArgument θ y).arg = Real.arctan (2*y*Real.cos θ / (1-y^2)) := by
  have hpos : 0 < (saddleLogArgument θ y).re := by
    rw [saddleLogArgument_re]
    have hsq := (sq_lt_sq₀ hy.1.le zero_le_one).2 hy.2
    linarith
  have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos))
  rw [← Real.arctan_tan ha.1 ha.2, Complex.tan_arg, saddleLogArgument_re, saddleLogArgument_im]

private theorem arctan_linear_gap {y c : ℝ} (hy : y ∈ Ioo 0 1)
    (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1) :
    (2 * y * (1 - y^2) / (1 + y^2)^2) * (1-c) ≤
      Real.arctan (2*y / (1-y^2)) - Real.arctan (2*y*c / (1-y^2)) := by
  let A := 2*y / (1-y^2)
  let B := 2*y*(1-y^2) / (1+y^2)^2
  let F (u : ℝ) := Real.arctan (A*u) - B*u
  have hsq := (sq_lt_sq₀ hy.1.le zero_le_one).2 hy.2
  have hd : 0 < 1-y^2 := by linarith
  have hAB (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) : B ≤ A / (1+(A*u)^2) := by
    have num : 0 ≤ 2*y*(1-y^2) := mul_nonneg (mul_nonneg (by norm_num) hy.1.le) hd.le
    have hu_sq : u^2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg u) (abs_le.mpr hu) 2
    have H : A / (1+(A*u)^2) = 2*y*(1-y^2) / ((1-y^2)^2 + (2*y)^2*u^2) := by
      dsimp [A]
      field_simp [hd.ne']
    rw [H]
    apply div_le_div_of_nonneg_left num (by positivity)
    have h := mul_le_mul_of_nonneg_left hu_sq (sq_nonneg (2*y))
    nlinarith only [h]
  have hdF (u : ℝ) : HasDerivAt F (A / (1+(A*u)^2) - B) u := by
    have h₁ := (Real.hasDerivAt_arctan (A*u)).comp u ((hasDerivAt_id u).const_mul A)
    have h₂ := (hasDerivAt_id u).const_mul B
    convert h₁.sub h₂ using 1
    · rfl
    · simp only [mul_one, div_eq_mul_inv]
      ring
  have hmono : MonotoneOn F (Icc (-1 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun u _ => (hdF u).continuousAt.continuousWithinAt
    · exact fun u _ => (hdF u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hdF u).deriv]
      exact sub_nonneg.mpr (hAB u (interior_subset hu))
  have hh := hmono (show c ∈ Icc (-1 : ℝ) 1 from ⟨hc₁, hc₂⟩)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨by norm_num, le_rfl⟩) hc₂
  have he : A*c = 2*y*c/(1-y^2) := by dsimp [A]; ring
  change _ ≤ Real.arctan A - Real.arctan (2*y*c/(1-y^2))
  rw [← he]
  change B * (1-c) ≤ _
  dsimp [F] at hh
  rw [mul_one, mul_one] at hh
  linarith only [hh]

private theorem saddle_arg_gap {y : ℝ} (hy : y ∈ Ioo 0 1) (θ : ℝ) :
    (2*y*(1-y^2) / (1+y^2)^2)*(1-Real.cos θ) ≤
      (saddleLogArgument 0 y).arg - (saddleLogArgument θ y).arg := by
  rw [saddleLogArgument_arg_eq_arctan hy, saddleLogArgument_arg_eq_arctan hy,
    Real.cos_zero, mul_one]
  exact arctan_linear_gap hy (Real.neg_one_le_cos θ) (Real.cos_le_one θ)

private theorem deriv_sq_div_one_add_sq (x : ℝ) : HasDerivAt
    (fun t : ℝ => t^2 / (1+t^2)) (2*x/(1+x^2)^2) x := by
  have h := (hasDerivAt_id x).pow 2
  have hx : 1 + (id x)^2 ≠ 0 := by positivity
  convert h.div (h.const_add 1) hx using 1
  · rfl
  · simp only [id, Nat.cast_two, Nat.reduceSub, pow_one, mul_one]
    congr 1
    ring

private theorem deriv_div_one_add_sq (x : ℝ) : HasDerivAt
    (fun t : ℝ => t / (1+t^2)) ((1-x^2)/(1+x^2)^2) x := by
  have h := hasDerivAt_id x
  have hx : 1 + (id x)^2 ≠ 0 := by positivity
  convert h.div ((h.pow 2).const_add 1) hx using 1
  · rfl
  · simp only [id, Nat.cast_two, Nat.reduceSub, pow_one, one_mul, mul_one]
    congr 1
    change 1-x^2 = 1+x^2-x*(2*x)
    ring

private theorem saddleG_integral_components {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (θ : ℝ) :
    (saddleG r θ).re = ∫ y in (0 : ℝ)..r, Real.log ‖saddleLogArgument θ y‖ / y ∧
      (saddleG r θ).im = ∫ y in (0 : ℝ)..r, (saddleLogArgument θ y).arg / y := by
  rw [saddleG_eq_log_integral hr hr₁ θ]
  have h := intervalIntegrable_saddle_log hr hr₁ θ
  have h₁ := intervalIntegral.intervalIntegral_re h
  have h₂ := intervalIntegral.intervalIntegral_im h
  change (∫ y in (0 : ℝ)..r, (Complex.log (saddleLogArgument θ y) / (y : ℂ)).re) = _ at h₁
  change (∫ y in (0 : ℝ)..r, (Complex.log (saddleLogArgument θ y) / (y : ℂ)).im) = _ at h₂
  exact ⟨by simpa only [Complex.div_ofReal_re, Complex.log_re, RCLike.re_to_complex] using h₁.symm,
    by simpa only [Complex.div_ofReal_im, Complex.log_im, RCLike.im_to_complex] using h₂.symm⟩

/-- Both component gaps of (22), including the endpoint radius (r=1). -/
theorem saddleG_component_gaps {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (θ : ℝ) :
    r^2 / (1+r^2) * Real.sin θ ^ 2 ≤ (saddleS r ^ 2).re - (saddleG r θ).re ∧
      2*r/(1+r^2)*(1-Real.cos θ) ≤ (saddleS r ^ 2).im - (saddleG r θ).im := by
  rw [← saddleG_zero r]
  have h (φ : ℝ) := intervalIntegrable_saddle_log hr hr₁ φ
  have hre (φ : ℝ) : IntervalIntegrable (fun y : ℝ => Real.log ‖saddleLogArgument φ y‖ / y)
      volume 0 r := by
    simpa only [Complex.div_ofReal_re, Complex.log_re] using
      (show IntervalIntegrable (fun y : ℝ =>
        (Complex.log (saddleLogArgument φ y) / (y : ℂ)).re) volume 0 r from
        ⟨Complex.reCLM.integrable_comp (h φ).1,
          Complex.reCLM.integrable_comp (h φ).2⟩)
  have him (φ : ℝ) : IntervalIntegrable (fun y : ℝ => (saddleLogArgument φ y).arg / y)
      volume 0 r := by
    simpa only [Complex.div_ofReal_im, Complex.log_im] using
      (show IntervalIntegrable (fun y : ℝ =>
        (Complex.log (saddleLogArgument φ y) / (y : ℂ)).im) volume 0 r from
        ⟨Complex.imCLM.integrable_comp (h φ).1,
          Complex.imCLM.integrable_comp (h φ).2⟩)
  have hsub (y : ℝ) (hy : y ∈ Ioo 0 r) : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hy.1, hy.2.trans_le hr₁⟩
  have hdenom : Continuous (fun y : ℝ => (1+y^2)^2) := by fun_prop
  have hdenom₀ (y : ℝ) : (1+y^2)^2 ≠ 0 := by positivity
  constructor
  · let p (y : ℝ) := 2*y/(1+y^2)^2 * Real.sin θ^2
    have hnum : Continuous (fun y : ℝ => 2*y) := by fun_prop
    have hp : IntervalIntegrable p volume 0 r := ((hnum.div₀ hdenom hdenom₀).mul_const
      (Real.sin θ^2)).intervalIntegrable ..
    have hpi : (∫ y in (0 : ℝ)..r, p y) = r^2/(1+r^2)*Real.sin θ^2 := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, add_zero,
        zero_div, zero_mul, sub_zero] using (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => (deriv_sq_div_one_add_sq y).mul_const (Real.sin θ^2)) hp)
    rw [(saddleG_integral_components hr hr₁ 0).1, (saddleG_integral_components hr hr₁ θ).1,
      ← intervalIntegral.integral_sub (hre 0) (hre θ), ← hpi]
    refine intervalIntegral.integral_mono_on_of_le_Ioo hr.le hp ((hre 0).sub (hre θ)) ?_
    intro y hy
    change p y ≤ Real.log ‖saddleLogArgument 0 y‖ / y - Real.log ‖saddleLogArgument θ y‖ / y
    rw [← sub_div]
    apply (le_div_iff₀ hy.1).mpr
    have hp' : p y * y = 2*y^2*Real.sin θ^2/(1+y^2)^2 := by dsimp [p]; ring
    rw [hp']
    exact saddle_log_real_gap (hsub y hy) θ
  · let p (y : ℝ) := ((1-y^2)/(1+y^2)^2) * (2*(1-Real.cos θ))
    have hnum : Continuous (fun y : ℝ => 1-y^2) := by fun_prop
    have hp : IntervalIntegrable p volume 0 r := ((hnum.div₀ hdenom hdenom₀).mul_const
      (2*(1-Real.cos θ))).intervalIntegrable ..
    have hpi : (∫ y in (0 : ℝ)..r, p y) = 2*r/(1+r^2)*(1-Real.cos θ) := by
      have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => (deriv_div_one_add_sq y).mul_const (2*(1-Real.cos θ))) hp
      simp only [zero_div, zero_mul, sub_zero] at hh
      rw [hh]
      ring
    rw [(saddleG_integral_components hr hr₁ 0).2, (saddleG_integral_components hr hr₁ θ).2,
      ← intervalIntegral.integral_sub (him 0) (him θ), ← hpi]
    refine intervalIntegral.integral_mono_on_of_le_Ioo hr.le hp ((him 0).sub (him θ)) ?_
    intro y hy
    change p y ≤ (saddleLogArgument 0 y).arg / y - (saddleLogArgument θ y).arg / y
    rw [← sub_div]
    apply (le_div_iff₀ hy.1).mpr
    have hp' : p y*y = (2*y*(1-y^2)/(1+y^2)^2)*(1-Real.cos θ) := by dsimp [p]; ring
    rw [hp']
    exact saddle_arg_gap (hsub y hy) θ

theorem saddleG_im_nonneg_of_cos_nonneg {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hθ : 0 ≤ Real.cos θ) : 0 ≤ (saddleG r θ).im := by
  rw [(saddleG_integral_components hr hr₁ θ).2]
  apply intervalIntegral.integral_nonneg hr.le
  intro y hy
  apply div_nonneg ?_ hy.1
  apply Complex.arg_nonneg_iff.mpr
  rw [saddleLogArgument_im]
  exact mul_nonneg (mul_nonneg (by norm_num) hy.1) hθ

theorem saddleG_im_nonpos_of_cos_nonpos {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hθ : Real.cos θ ≤ 0) : (saddleG r θ).im ≤ 0 := by
  rw [(saddleG_integral_components hr hr₁ θ).2]
  have hh : 0 ≤ ∫ y in (0 : ℝ)..r, -((saddleLogArgument θ y).arg/y) := by
    apply intervalIntegral.integral_nonneg hr.le
    intro y hy
    apply neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg ?_ hy.1)
    have him : (saddleLogArgument θ y).im ≤ 0 := by
      rw [saddleLogArgument_im]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hy.1) hθ
    rcases lt_or_eq_of_le him with hlt | heq
    · exact (Complex.arg_neg_iff.mpr hlt).le
    · have hRe : 0 ≤ (saddleLogArgument θ y).re := by
        rw [saddleLogArgument_re]
        exact sub_nonneg.mpr (pow_le_one₀ hy.1 (hy.2.trans hr₁))
      exact (Complex.arg_eq_zero_iff.mpr ⟨hRe, heq⟩).le
  rw [intervalIntegral.integral_neg] at hh
  exact neg_nonneg.mp hh

end DurfeeCCS.Step08
