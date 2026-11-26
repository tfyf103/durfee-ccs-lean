module

public import DurfeeCCS.Step09.MidOtherPhase
public import DurfeeCCS.Step09.MidPhaseShape
public import DurfeeCCS.Step09.MidOtherDecay

meta import DurfeeCCS.Step07.ThetaBoundsIntervals
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The first ten finite logarithm bounds and their high-radius continuation. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex Real Set DurfeeCCS.Step06 DurfeeCCS.Step07

def midModeGap (r β : ℝ) : ℝ :=
  ((saddleS r).re ^ 2 - Real.log r ^ 2 - modeShiftedSquare (Real.log r) β) / (saddleS r).re

theorem midRe_exponent_nonprincipal {n : ℕ} (hn : 0 < n) {r η χ : ℝ} (hr : 1 ≤ r)
    (hη : |η| ≤ 8) (p : ℤ) :
    ((n : ℂ) * midEtaPoint n r η + midPhase r p χ / midEtaPoint n r η).re ≤
      2 * midOmega n r - Real.sqrt n * midModeGap r |midFrequency p| -
        Real.sqrt n * χ ^ 2 / (130 * (saddleS r).re) := by
  let t := Real.log r
  let β := |midFrequency p|
  let w := modeSquare t (modeRealOffset t) (modeImagOffset t) β
  have hrp : 0 < r := by linarith
  have hR : modeRealOffset t = Real.pi ^ 2 / 3 - (saddleG r⁻¹ 0).re := by
    have hexp : Real.exp (2 * Real.log r) = r^2 := by
      rw [← Real.exp_log hrp, ← Real.exp_nat_mul]
      norm_num
    unfold t modeRealOffset
    rw [show -2 * Real.log r = -(2 * Real.log r) by ring, Real.exp_neg,
      hexp, ← inv_pow,
      saddleG_zero, saddleS_sq, saddlePhaseSquare, Complex.mul_re, principalDilog_negImag_re]
    push_cast
    simp
    ring
  have hI : modeImagOffset t = (saddleG r⁻¹ 0).im := by
    unfold t modeImagOffset
    rw [Real.exp_neg, Real.exp_log hrp, saddleG_zero, saddleS_sq, saddlePhaseSquare]
    push_cast
    simp
  have hW : w.re = t ^ 2 - β^2 + modeRealOffset t ∧ w.im = 2*β*t + modeImagOffset t := by
    simp [w,modeSquare,Complex.mul_re,Complex.mul_im, ← Complex.ofReal_pow]
  obtain ⟨hRe,hIm⟩ := midPhase_component_bounds hr p χ
  have hRe' : (midPhase r p χ).re ≤ w.re - χ ^ 2 / (1 + r⁻¹ ^ 2) := by
    rw [hW.1,hR]
    unfold β t
    rw [sq_abs]
    linarith only [hRe]
  have hIm' : |(midPhase r p χ).im| ≤ w.im := by
    rw [hW.2,hI]
    unfold β t
    linarith only [hIm]
  refine (midRe_exponent_le_modeGap hn hr hη hRe' hIm').trans_eq ?_
  unfold midModeGap modeShiftedSquare w β t
  ring

theorem midModeGap_on_log_interval (wide : Bool) (i : Fin 5) {r β : ℝ} (hr : 1 ≤ r)
    (htl : (i.val : ℝ) ≤ Real.log r) (hth : Real.log r ≤ (i.val : ℝ) + 1)
    (hβ : modeMultiplier wide * π / 2 ≤ β) : modeGapTarget wide i < midModeGap r β := by
  have h := modeGap_on_log_interval wide i htl hth hβ
  rw [Real.exp_log (by linarith : 0 < r)] at h
  exact h

theorem midModeGap_low_log {r β : ℝ} (hr : 1 ≤ r)
    (ht : Real.log r ≤ 1) (hβ : 3*π/2 ≤ β) : 0.44 < midModeGap r β := by
  exact midModeGap_on_log_interval false 0 hr
    (by simpa using Real.log_nonneg hr) (by simpa using ht) hβ

theorem midModeGap_middle_log (wide : Bool) {r β : ℝ} (hr : 1 ≤ r)
    (ht₀ : 1 ≤ Real.log r) (ht₁ : Real.log r ≤ 5)
    (hβ : modeMultiplier wide * π / 2 ≤ β) :
    (if wide then 0.36 else 0.21) < midModeGap r β := by
  let t := Real.log r
  have hh : ∃ i : Fin 5, i.val ≠ 0 ∧ (i.val : ℝ) ≤ t ∧ t ≤ (i.val : ℝ)+1 := by
    by_cases h₂ : t ≤ 2
    · exact ⟨1, by decide, by simpa using ht₀, by norm_num; exact h₂⟩
    by_cases h₃ : t ≤ 3
    · exact ⟨2, by decide, by norm_num; linarith, by norm_num; exact h₃⟩
    by_cases h₄ : t ≤ 4
    · exact ⟨3, by decide, by norm_num; linarith, by norm_num; exact h₄⟩
    · exact ⟨4, by decide, by norm_num; linarith, by norm_num; exact ht₁⟩
  obtain ⟨i,_,hiL,hiR⟩ := hh
  refine lt_of_le_of_lt ?_ (midModeGap_on_log_interval wide i hr hiL hiR hβ)
  cases wide <;> fin_cases i <;> norm_num [modeGapTarget]

def midModeHighNumerator (wide : Bool) : ℝ := if wide then 178 else 59.5

def midModeHighDenominator (wide : Bool) : ℝ := if wide then 65 else 25.5

theorem midModeGap_high_log (wide : Bool) {r β : ℝ} (hr : 1 ≤ r) (ht₀ : 5 ≤ Real.log r)
    (hβ : modeMultiplier wide * π / 2 ≤ β) :
    midModeHighNumerator wide /
      ((saddleS r).re * (Real.log r ^ 2 + midModeHighDenominator wide)) ≤ midModeGap r β := by
  let t := Real.log r
  let a := (saddleS r).re
  let c := modeRealOffset t
  let v := modeImagOffset t
  let D := a ^ 2 - t ^ 2
  let y := modeShiftedSquare t β
  let β₀ := modeMultiplier wide * π / 2
  have ha : 0 < a := (saddleS_components (by linarith : 0 < r)).1.trans
    (saddleS_components (by linarith : 0 < r)).2
  have ht : 0 ≤ t := by linarith
  have hm : 3 ≤ modeMultiplier wide := by cases wide <;> norm_num [modeMultiplier]
  have hβ₀ : 3 * π / 2 ≤ β₀ := by unfold β₀; gcongr
  have hβ' : 3 * π / 2 ≤ β := hβ₀.trans hβ
  have hc := modeRealOffset_bounds ht
  have hv := modeImagOffset_bounds ht
  have hv₂ : v ≤ 2 := hv.2.trans (by
    have h := exp_le_one_iff.mpr (show -t ≤ 0 by linarith)
    linarith only [h])
  have htv : t * v ≤ 0.0674 := by
    have hh := mul_le_mul_of_nonneg_left hv.2 ht
    have h1 : t * v ≤ modeImagCorrection t := by unfold modeImagCorrection; linarith only [hh]
    have h2 := modeImagCorrection_anti (by norm_num : (5 : ℝ) ∈ Ici 1)
      (show t ∈ Ici 1 from (by norm_num : (1 : ℝ) ≤ 5).trans ht₀) ht₀
    have h3 : modeImagCorrection 5 ≤ 0.0674 := by
      unfold modeImagCorrection
      dyadic_interval +kernel [prec := 45]
    exact h1.trans (h2.trans h3)
  have hD₀ : 3.02712 < D := by
    have H := minorArcSaddleGap_mono (show (5 : ℝ) ∈ Ici 0 by norm_num) (show t ∈ Ici 0 from ht) ht₀
    have h5 : 3.02712 < minorArcSaddleGap 5 := by
      simpa [minorArcSaddleGap,saddleEndpointData,Rat.cast_ofScientific] using
        (saddleEndpointData_bounds (19 : Fin 21)).gap_lower
    unfold minorArcSaddleGap at H
    change (saddleS (Real.exp 5)).re^2 - 5^2 ≤ (saddleS (Real.exp t)).re^2 - t^2 at H
    have htr : Real.exp t = r := Real.exp_log (by linarith)
    rw [htr] at H
    exact h5.trans_le H
  have hy := modePolynomial_of_shifted_square t β
  have hD := modePolynomial_of_saddle ht
  have htr : Real.exp t = r := Real.exp_log (by linarith)
  rw [htr] at hD
  have hDpoly : modePolynomial t c v (π/2) D = 0 := hD
  have hD_c : D ≤ c := (modePolynomial_root_lt_offset hc.1 hv.1 hv₂
    (htv.trans (by norm_num)) (by linarith [pi_gt_d6]) hDpoly).le
  have hy_c : y ≤ c := (modePolynomial_root_lt_offset hc.1 hv.1 hv₂
    (htv.trans (by norm_num)) (by linarith [pi_gt_d6]) hy).le
  have hy0 : 0 ≤ y := modeSquare_shift_nonneg ht (by linarith [hc.1]) hv.1
    (by linarith [pi_gt_d6])
  have hβsq : (3*π/2)^2 ≤ β^2 := pow_le_pow_left₀ (by positivity) hβ' 2
  let B := D + y + t^2 + β^2 - c
  have hB : 0 < B := by
    have hpi2 := pow_le_pow_left₀ (by norm_num : 0 ≤ (3.141592 : ℝ)) Real.pi_gt_d6.le 2
    have hpi3 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2
    unfold B
    nlinarith only [hβsq,hD₀,hy0,hc.2,hpi2,hpi3,sq_nonneg t]
  have hb : B ≤ t^2 + β^2 + π^2/3 := by unfold B; linarith only [hD_c,hy_c,hc.2]
  have hden : 0 < β+π/2 := by linarith [pi_pos]
  have htv' : t*v/(β+π/2) ≤ 0.01074 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [htv,hβ',pi_gt_d6]
  have hW : 3.016 ≤ D - t*v/(β+π/2) := by linarith only [hD₀,htv']
  have hstar : (β^2 - π^2/4) * 3.016 / (t^2 + β^2 + π^2/3) ≤ D-y := by
    have h := modePolynomial_gap hy hDpoly (by linarith [pi_pos] : π/2 ≤ β)
    change (D-y)*B = _ at h
    have hco : 0 ≤ β^2 - π^2/4 := by nlinarith only [hβsq,sq_nonneg π]
    have hge := mul_le_mul_of_nonneg_left hW hco
    calc
      _ ≤ (β^2 - π^2/4) * 3.016 / B := div_le_div_of_nonneg_left (by positivity) hB hb
      _ ≤ _ := by apply (div_le_iff₀ hB).mpr; rw [h]; exact hge
  have hpref := modePrefactor_mono_beta (t := t) (show 0 ≤ β₀ by linarith [pi_pos]) hβ
  have hImprove : (β₀^2-π^2/4)*3.016/(t^2+β₀^2+π^2/3) ≤ D-y := by
    refine le_trans ?_ hstar
    have h := mul_le_mul_of_nonneg_right hpref (by norm_num : 0 ≤ (3.016 : ℝ))
    simpa only [div_mul_eq_mul_div] using h
  have hNum : midModeHighNumerator wide ≤ (β₀^2-π^2/4)*3.016 := by
    have hpi := pow_le_pow_left₀ (by norm_num : 0 ≤ (3.141592 : ℝ)) Real.pi_gt_d6.le 2
    cases wide <;> dsimp [midModeHighNumerator,β₀,modeMultiplier] <;> nlinarith only [hpi]
  have hDen : β₀^2+π^2/3 ≤ midModeHighDenominator wide := by
    have hpi := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2
    cases wide <;> dsimp [midModeHighDenominator,β₀,modeMultiplier] <;> nlinarith only [hpi]
  have hNum0 : 0 ≤ midModeHighNumerator wide := by cases wide <;> norm_num [midModeHighNumerator]
  have hRatio : midModeHighNumerator wide / (t^2+midModeHighDenominator wide) ≤ D-y := by
    refine le_trans ?_ hImprove
    exact div_le_div₀ (hNum0.trans hNum) hNum (by positivity) (by linarith only [hDen])
  have H := div_le_div_of_nonneg_right hRatio ha.le
  change midModeHighNumerator wide/(a*(t^2+midModeHighDenominator wide)) ≤ (D-y)/a
  rw [mul_comm a, ← div_div]
  exact H

end DurfeeCCS.Step09
