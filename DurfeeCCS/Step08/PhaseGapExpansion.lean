module

public import DurfeeCCS.Step08.PhaseGapComponents
public import DurfeeCCS.Step08.PhaseGapParameters
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The logarithmic expansion on the central part of the arc, pp. 14–15. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07
open scoped Real Interval

noncomputable def saddleLogPerturbation (ψ y : ℝ) : ℂ :=
  2*(y : ℂ)*I*(ψ : ℂ)/(1+(y : ℂ)*I)^2

private theorem saddleLogBase_ne_zero (y : ℝ) : (1+(y : ℂ)*I) ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp [Complex.mul_re] at h'

private theorem norm_saddleLogPerturbation {ψ y : ℝ} (hψ : 0 ≤ ψ) (hy : 0 ≤ y) :
    ‖saddleLogPerturbation ψ y‖ = 2*y*ψ/(1+y^2) := by
  have h : ‖1+(y : ℂ)*I‖^2 = 1+y^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  simp [saddleLogPerturbation, norm_pow, h, Real.norm_of_nonneg hψ,
    Real.norm_of_nonneg hy]

private theorem saddleLogPerturbation_norm_bounds {ψ y : ℝ} (hψ : 0 ≤ ψ) (hy : 0 ≤ y) :
    ‖saddleLogPerturbation ψ y‖ ≤ ψ ∧ ‖saddleLogPerturbation ψ y‖ ≤ 2*y*ψ := by
  rw [norm_saddleLogPerturbation hψ hy]
  constructor
  · rw [div_le_iff₀ (by positivity)]
    nlinarith only [mul_nonneg hψ (sq_nonneg (y-1))]
  · exact div_le_self (by positivity) (le_add_of_nonneg_right (sq_nonneg y))

private theorem saddleLogArgument_perturbation {θ y : ℝ} (hy : y ∈ Ioo 0 1)
    (hψ : 1-Real.cos θ < 1) :
    Complex.log (saddleLogArgument 0 y) - Complex.log (saddleLogArgument θ y) =
      -Complex.log (1-saddleLogPerturbation (1-Real.cos θ) y) := by
  let ψ := 1-Real.cos θ
  let u := saddleLogPerturbation ψ y
  have hyC := saddleLogBase_ne_zero y
  have hBase : saddleLogArgument 0 y = (1+(y : ℂ)*I)^2 := by
    simp only [saddleLogArgument, Real.cos_zero, Complex.ofReal_one, mul_one]
    linear_combination (norm := ring_nf) -((y : ℂ)^2) * Complex.I_sq
  have hA : saddleLogArgument θ y = saddleLogArgument 0 y * (1-u) := by
    have h := show saddleLogArgument θ y = saddleLogArgument 0 y - 2*(y : ℂ)*I*(ψ : ℂ) by
      unfold saddleLogArgument ψ
      simp only [Real.cos_zero, Complex.ofReal_one, Complex.ofReal_sub, mul_one]
      ring
    rw [h, hBase]
    unfold u saddleLogPerturbation
    field_simp
  have ha : 0 < (saddleLogArgument 0 y).re := by
    rw [saddleLogArgument_re]
    nlinarith only [hy.1, hy.2, mul_pos hy.1 (sub_pos.mpr hy.2)]
  have hu := (saddleLogPerturbation_norm_bounds (sub_nonneg.mpr (Real.cos_le_one θ)) hy.1.le).1
  have hu' : ‖u‖ < 1 := hu.trans_lt hψ
  have hb : 0 < (1-u).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith only [hu', Complex.re_le_norm u]
  rw [hA, log_mul_of_pos_re ha hb]
  ring

/-- The logarithmic difference identity used before the central Taylor expansion. -/
theorem saddleG_log_perturbation {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hψ : 1-Real.cos θ < 1) :
    saddleS r^2 - saddleG r θ = ∫ y in (0 : ℝ)..r,
      -Complex.log (1-saddleLogPerturbation (1-Real.cos θ) y) / (y : ℂ) := by
  rw [← saddleG_zero r, saddleG_eq_log_integral hr hr₁ 0, saddleG_eq_log_integral hr hr₁ θ,
    ← intervalIntegral.integral_sub (intervalIntegrable_saddle_log hr hr₁ 0)
      (intervalIntegrable_saddle_log hr hr₁ θ)]
  refine intervalIntegral.integral_congr_Ioo_of_le hr.le ?_
  intro y hy
  dsimp only
  rw [← sub_div, saddleLogArgument_perturbation ⟨hy.1, hy.2.trans_le hr₁⟩ hψ]

private theorem integral_saddleLog_linear (r ψ : ℝ) :
    (∫ y in (0 : ℝ)..r, 2*I*(ψ : ℂ)/(1+(y : ℂ)*I)^2) = 2*(r : ℂ)*I*(ψ : ℂ)/(1+(r : ℂ)*I) := by
  let k : ℂ := 2*I*(ψ : ℂ)
  have hd (y : ℝ) : HasDerivAt (fun t : ℝ => k*((t : ℂ)/(1+(t : ℂ)*I)))
      (k/(1+(y : ℂ)*I)^2) y := by
    have h := hasDerivAt_id (y : ℂ)
    have hq := (h.div ((h.mul_const I).const_add 1) (saddleLogBase_ne_zero y)).const_mul k
    convert hq.comp_ofReal using 1
    · rfl
    · simp [id, k, div_eq_mul_inv, mul_assoc]
  have hc : Continuous (fun y : ℝ => k/(1+(y : ℂ)*I)^2) :=
    continuous_const.div₀ (by fun_prop) (fun y => pow_ne_zero 2 (saddleLogBase_ne_zero y))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable 0 r)
  simp only [Complex.ofReal_zero, zero_div, mul_zero, sub_zero] at h
  change (∫ y in (0 : ℝ)..r, k/(1+(y : ℂ)*I)^2) = _
  rw [h]
  unfold k
  ring

private theorem log_perturbation_remainder {u : ℂ} {ψ : ℝ} (hψ : ψ < 1) (hu : ‖u‖ ≤ ψ) :
    ‖-Complex.log (1-u)-u‖ ≤ ‖u‖*ψ/(2*(1-ψ)) := by
  have h := Complex.norm_log_one_add_sub_self_le (z := -u) (by simpa using hu.trans_lt hψ)
  have hn : -(-Complex.log (1-u)-u) = Complex.log (1+-u) - -u := by
    rw [← sub_eq_add_neg]
    ring
  rw [← norm_neg (-Complex.log (1-u)-u), hn]
  simp only [norm_neg] at h
  refine h.trans ?_
  have hpos : 0 < 1-ψ := sub_pos.mpr hψ
  have hψn : 0 ≤ ψ := (norm_nonneg u).trans hu
  rw [inv_eq_one_div, mul_one_div, div_div, mul_comm (1-‖u‖)]
  apply div_le_div₀ (by positivity) ?_ (by positivity) (by linarith only [hu])
  rw [pow_two]
  exact mul_le_mul_of_nonneg_left hu (norm_nonneg u)

/-- The first-order logarithmic approximation to `s² - g_r(θ)` on the central arc. -/
theorem saddleG_log_linear_remainder {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hψ : 1-Real.cos θ < 1) :
    let ψ := 1-Real.cos θ
    ‖saddleS r^2-saddleG r θ-2*(r : ℂ)*I*(ψ : ℂ)/(1+(r : ℂ)*I)‖ ≤ r*ψ^2/(1-ψ) := by
  let ψ := 1-Real.cos θ
  let f (y : ℝ) : ℂ := -Complex.log (1-saddleLogPerturbation ψ y)/(y : ℂ)
  let p (y : ℝ) : ℂ := 2*I*(ψ : ℂ)/(1+(y : ℂ)*I)^2
  have hfn : IntervalIntegrable f volume 0 r := by
    apply (intervalIntegrable_congr_uIoo ?_).mpr
      ((intervalIntegrable_saddle_log hr hr₁ 0).sub (intervalIntegrable_saddle_log hr hr₁ θ))
    rw [uIoo_of_le hr.le]
    intro y hy
    dsimp [f]
    rw [← sub_div, saddleLogArgument_perturbation ⟨hy.1, hy.2.trans_le hr₁⟩ hψ]
  have hp : IntervalIntegrable p volume 0 r :=
    (continuous_const.div₀ (by fun_prop) (fun y => pow_ne_zero 2 (saddleLogBase_ne_zero y))).intervalIntegrable ..
  change ‖saddleS r^2-saddleG r θ-2*(r : ℂ)*I*(ψ : ℂ)/(1+(r : ℂ)*I)‖ ≤ r*ψ^2/(1-ψ)
  rw [saddleG_log_perturbation hr hr₁ hψ, ← integral_saddleLog_linear r ψ,
    ← intervalIntegral.integral_sub hfn hp]
  have hpoint (y : ℝ) (hy : 0 < y) : ‖f y-p y‖ ≤ ψ^2/(1-ψ) := by
    let u := saddleLogPerturbation ψ y
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hId : p y = u/(y : ℂ) := by
      unfold p u saddleLogPerturbation
      field_simp [saddleLogBase_ne_zero y]
    rw [hId]
    change ‖-Complex.log (1-u)/(y : ℂ)-u/(y : ℂ)‖ ≤ _
    rw [← sub_div, norm_div, Complex.norm_of_nonneg hy.le, div_le_iff₀ hy]
    have hψ₀ : 0 ≤ ψ := sub_nonneg.mpr (Real.cos_le_one θ)
    obtain ⟨hu, hu'⟩ := saddleLogPerturbation_norm_bounds hψ₀ hy.le
    calc
      _ ≤ ‖u‖*ψ/(2*(1-ψ)) := log_perturbation_remainder hψ hu
      _ ≤ (2*y*ψ)*ψ/(2*(1-ψ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu' hψ₀) (by linarith)
      _ = _ := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := r) (f := fun y => f y-p y) (C := ψ^2/(1-ψ)) (by
      rw [uIoc_of_le hr.le]
      exact fun y hy => hpoint y hy.1)
  rw [sub_zero, abs_of_pos hr] at h
  exact h.trans_eq (by ring)

private theorem norm_log_one_sub_le_on_central {u : ℂ} (hu : ‖u‖ ≤ 0.3) :
    ‖Complex.log (1-u)‖ ≤ 1.19*‖u‖ := by
  let t := ‖u‖
  have ht : 0 ≤ t := norm_nonneg u
  have ht₁ : t ≤ 0.3 := hu
  have h := Complex.norm_log_sub_logTaylor_le 3 (z := -u) (by simpa using hu.trans_lt (by norm_num))
  have hTaylor : Complex.logTaylor 4 (-u) = -(u+u^2/2+u^3/3) := by
    norm_num [Complex.logTaylor, Finset.sum_range_succ]
    ring
  rw [hTaylor, sub_neg_eq_add] at h
  rw [sub_eq_add_neg 1 u]
  have h₁ : ‖Complex.log (1+-u) + (u+u^2/2+u^3/3)‖ ≤ t^4*(1-t)⁻¹/4 := by
    norm_num at h ⊢
    exact h
  have h₂ := mul_le_mul_of_nonneg_left ht₁ ht
  have h₃ := mul_le_mul_of_nonneg_left (show t^2 ≤ 0.3*t by nlinarith only [h₂]) ht
  have h₄ := mul_le_mul_of_nonneg_left (show t^3 ≤ 0.09*t by nlinarith only [h₂,h₃]) ht
  have hInv : (1-t)⁻¹ ≤ 10/7 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith only [ht₁])]
    linarith only [ht₁]
  have h₅ : t^4*(1-t)⁻¹/4 ≤ (0.027*t)*(10/7)/4 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul (by nlinarith only [h₄,h₂]) hInv (by
      exact inv_nonneg.mpr (by linarith only [ht₁])) (by positivity)
  calc
    ‖Complex.log (1+-u)‖ = ‖(Complex.log (1+-u)+(u+u^2/2+u^3/3))-(u+u^2/2+u^3/3)‖ := by
      rw [add_sub_cancel_right]
    _ ≤ ‖Complex.log (1+-u)+(u+u^2/2+u^3/3)‖ + (‖u‖ + ‖u^2/2‖ + ‖u^3/3‖) := by
      linarith only [norm_add_le (u+u^2/2) (u^3/3), norm_add_le u (u^2/2),
        norm_sub_le (Complex.log (1+-u)+(u+u^2/2+u^3/3)) (u+u^2/2+u^3/3)]
    _ ≤ t^4*(1-t)⁻¹/4 + (t+t^2/2+t^3/3) := by
      simpa [t, norm_div, norm_pow] using add_le_add_right h₁ (‖u‖ + ‖u‖^2/2 + ‖u‖^3/3)
    _ ≤ 1.19*t := by nlinarith only [h₅, h₂, h₃, ht]

/-- The normalized central displacement, with both constants from the proof of (33). -/
theorem saddleG_normalized_displacement {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hψ : 1-Real.cos θ ≤ 0.3) :
    let ψ := 1-Real.cos θ
    let w := saddleG r θ / saddleS r^2 - 1
    ‖w‖ ≤ 1.34*ψ ∧ ‖w‖ ≤ 0.402 := by
  let ψ := 1-Real.cos θ
  let s := saddleS r
  let w := saddleG r θ / s^2 - 1
  have hψ₀ : 0 ≤ ψ := sub_nonneg.mpr (Real.cos_le_one θ)
  have hψ₁ : ψ < 1 := hψ.trans_lt (by norm_num)
  have hsN : 16*r/9 ≤ ‖s‖^2 := (firstSaddle_coordinates_bounds hr hr₁).2.2.2.2
  have hsN₀ : 0 < ‖s‖^2 := (by positivity : 0 < 16*r/9).trans_le hsN
  have hs : s ≠ 0 := by intro he; simp [he] at hsN₀
  have hchange : ‖w‖ = ‖s^2-saddleG r θ‖/‖s‖^2 := by
    unfold w
    rw [← div_self (pow_ne_zero 2 hs), ← sub_div, norm_div, norm_pow, norm_sub_rev]
  let f (y : ℝ) : ℂ := -Complex.log (1-saddleLogPerturbation ψ y)/(y : ℂ)
  have hpoint (y : ℝ) (hy : 0 < y) : ‖f y‖ ≤ 2*1.19*ψ := by
    let u := saddleLogPerturbation ψ y
    obtain ⟨hu, hu'⟩ := saddleLogPerturbation_norm_bounds hψ₀ hy.le
    change ‖-Complex.log (1-u)/(y : ℂ)‖ ≤ _
    rw [norm_div, norm_neg, Complex.norm_of_nonneg hy.le, div_le_iff₀ hy]
    calc
      _ ≤ 1.19*‖u‖ := norm_log_one_sub_le_on_central (hu.trans hψ)
      _ ≤ 1.19*(2*y*ψ) := mul_le_mul_of_nonneg_left hu' (by norm_num)
      _ = _ := by ring
  have h : ‖s^2-saddleG r θ‖ ≤ r*(2*1.19*ψ) := by
    rw [saddleG_log_perturbation hr hr₁ hψ₁]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := r) (f := f) (C := 2*1.19*ψ) (by
        rw [uIoc_of_le hr.le]
        exact fun y hy => hpoint y hy.1)
    simpa [abs_of_pos hr, mul_comm] using h
  have hfinal : ‖w‖ ≤ 1.34*ψ := by
    rw [hchange, div_le_iff₀ hsN₀]
    have hmul := mul_le_mul_of_nonneg_left hsN (show 0 ≤ 1.34*ψ by positivity)
    nlinarith only [h, hmul, mul_nonneg hr.le hψ₀]
  exact ⟨hfinal, hfinal.trans (by linarith only [hψ])⟩

private theorem norm_log_sub_le_scaled_real {u : ℂ} {ψ c : ℝ} (hψ : ψ < 1)
    (hu : ‖u‖ ≤ ψ) (hu' : ‖u‖ ≤ c*ψ) :
    ‖-Complex.log (1-u)‖ ≤ c*(-Real.log (1-ψ)) := by
  have hψ₀ := (norm_nonneg u).trans hu
  let f (j : ℕ) : ℝ := ψ^(j+1)/((j : ℝ)+1)
  have hsumC := Complex.hasSum_taylorSeries_neg_log' (z := (ψ : ℂ)) (by
    rwa [Complex.norm_of_nonneg hψ₀])
  have hsumR : HasSum f (-Real.log (1-ψ)) := by
    have he : (1 : ℂ)-(ψ : ℂ) = ((1-ψ : ℝ) : ℂ) := by push_cast; ring
    rw [he, ← Complex.ofReal_log (sub_nonneg.mpr hψ.le), ← Complex.ofReal_neg] at hsumC
    have hf (j : ℕ) : (ψ : ℂ)^(j+1)/((j : ℂ)+1) = (f j : ℂ) := by
      unfold f
      push_cast
      rfl
    simpa only [Nat.cast_add, Nat.cast_one, hf, Function.comp_apply, Complex.reCLM_apply,
      Complex.ofReal_re] using Complex.reCLM.hasSum hsumC
  let g (j : ℕ) : ℂ := u^(j+1)/((j : ℂ)+1)
  have hsumG : HasSum g (-Complex.log (1-u)) := by
    simpa only [g, Nat.cast_add, Nat.cast_one] using Complex.hasSum_taylorSeries_neg_log' (hu.trans_lt hψ)
  have hpoint (j : ℕ) : ‖g j‖ ≤ c*f j := by
    have hn : 0 ≤ (j : ℝ)+1 := by positivity
    have hnorm : ‖((j : ℂ)+1)‖ = (j : ℝ)+1 := by
      rw [show (j : ℂ)+1 = (((j : ℝ)+1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_of_nonneg hn]
    simp only [g, f, norm_div, norm_pow, hnorm, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hn
    rw [pow_succ, pow_succ, ← mul_assoc]
    have hb := pow_le_pow_left₀ (norm_nonneg u) hu j
    nlinarith only [mul_le_mul hb hu' (norm_nonneg _) (show 0 ≤ ψ^j by positivity)]
  have hScale := hsumR.mul_left c
  have hAbs := Summable.of_nonneg_of_le (fun j => norm_nonneg (g j)) hpoint hScale.summable
  have h := norm_tsum_le_tsum_norm hAbs
  rw [hsumG.tsum_eq] at h
  exact h.trans ((hAbs.tsum_le_tsum hpoint hScale.summable).trans_eq hScale.tsum_eq)

/-- The logarithmic bound for the central perturbation preceding (33). -/
theorem saddleG_normalized_displacement_log {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hψ : 1-Real.cos θ < 1) :
    let w := saddleG r θ / saddleS r^2 - 1
    ‖w‖ ≤ (9/8)*(-Real.log (Real.cos θ)) := by
  let ψ := 1-Real.cos θ
  let s := saddleS r
  let w := saddleG r θ/s^2-1
  let f (y : ℝ) : ℂ := -Complex.log (1-saddleLogPerturbation ψ y)/(y : ℂ)
  have hψ₀ : 0 ≤ ψ := sub_nonneg.mpr (Real.cos_le_one θ)
  have hL₀ : 0 ≤ -Real.log (1-ψ) := neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have hsN : 16*r/9 ≤ ‖s‖^2 := (firstSaddle_coordinates_bounds hr hr₁).2.2.2.2
  have hsN₀ : 0 < ‖s‖^2 := (by positivity : 0 < 16*r/9).trans_le hsN
  have hs : s ≠ 0 := by intro he; simp [he] at hsN₀
  have hchange : ‖w‖ = ‖s^2-saddleG r θ‖/‖s‖^2 := by
    unfold w
    rw [← div_self (pow_ne_zero 2 hs), ← sub_div, norm_div, norm_pow, norm_sub_rev]
  have hpoint (y : ℝ) (hy : 0 < y) : ‖f y‖ ≤ 2*(-Real.log (1-ψ)) := by
    let u := saddleLogPerturbation ψ y
    obtain ⟨hu, hu'⟩ := saddleLogPerturbation_norm_bounds hψ₀ hy.le
    change ‖-Complex.log (1-u)/(y : ℂ)‖ ≤ _
    rw [norm_div, Complex.norm_of_nonneg hy.le, div_le_iff₀ hy]
    have h := norm_log_sub_le_scaled_real (c := 2*y) hψ hu (by simpa [mul_assoc] using hu')
    exact h.trans_eq (by ring)
  have h : ‖s^2-saddleG r θ‖ ≤ r*(2*(-Real.log (1-ψ))) := by
    rw [saddleG_log_perturbation hr hr₁ hψ]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := r) (f := f) (C := 2*(-Real.log (1-ψ))) (by
        rw [uIoc_of_le hr.le]
        exact fun y hy => hpoint y hy.1)
    simpa [abs_of_pos hr, mul_comm] using h
  change ‖w‖ ≤ (9/8)*(-Real.log (Real.cos θ))
  rw [show Real.cos θ = 1-ψ by unfold ψ; ring, hchange, div_le_iff₀ hsN₀]
  have hmul := mul_le_mul_of_nonneg_left hsN (show 0 ≤ (9/8)*(-Real.log (1-ψ)) by positivity)
  nlinarith only [h, hmul]

end DurfeeCCS.Step08
