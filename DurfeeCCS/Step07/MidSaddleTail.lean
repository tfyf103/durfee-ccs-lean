module

public import DurfeeCCS.Step07.MidSaddleTableGrid
public import DurfeeCCS.Step07.SaddleEndpoints
public import DurfeeCCS.Step07.SaddleGlobalMonotone
public import DurfeeCCS.Step07.PowerDecay
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-! Scalar transfers from the page 34 table to the exponential error bounds. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open Set DurfeeCCS.Step06

private theorem phaseReal_eq (r : ℝ) :
    (saddlePhaseSquare r).re = (saddleS r).re ^ 2 - (saddleS r).im ^ 2 := by
  rw [← saddleS_sq r, pow_two, Complex.mul_re, ← pow_two, ← pow_two]

private theorem phaseImag_eq (r : ℝ) :
    (saddlePhaseSquare r).im = 2 * (saddleS r).re * (saddleS r).im := by
  rw [← saddleS_sq r, pow_two, Complex.mul_im]
  ring

private theorem antitoneOn_negRealDilog :
    AntitoneOn (fun x : ℝ => (principalDilog (-(x : ℂ))).re) (Ioi 0) := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x : ℝ => (principalDilog (-(x : ℂ))).re)
        (-Real.log (1 + x) / x) x := by
    have hz : -(x : ℂ) ∈ dilogCut := by
      apply mem_dilogCut_iff.mpr
      left
      simp only [Complex.neg_re, Complex.ofReal_re]
      linarith
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have h := hasDerivAt_principalDilog hz
    rw [ite_eq_right (neg_ne_zero.mpr hxC), div_neg, neg_div, neg_neg,
      sub_neg_eq_add, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_log (by positivity : 0 ≤ 1 + x), ← Complex.ofReal_div] at h
    have hc := h.comp (x : ℂ) (hasDerivAt_id (x : ℂ)).neg
    simpa only [Function.comp_apply, id_eq, mul_neg_one, ← Complex.ofReal_neg,
      Complex.ofReal_re, neg_div] using hc.real_of_complex
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx0 : 0 < x := interior_subset hx
    rw [(hd x hx0).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.log_nonneg (by linarith))) hx0.le

theorem monotone_saddlePhaseRealDiff :
    Monotone (fun t : ℝ => (saddlePhaseSquare (Real.exp t)).re - t ^ 2) := by
  intro a b hab
  have he : Real.exp (-2 * b) ≤ Real.exp (-2 * a) := Real.exp_le_exp.mpr (by linarith)
  have hd := antitoneOn_negRealDilog (Real.exp_pos _) (Real.exp_pos _) he
  dsimp only at hd ⊢
  rw [phaseSquare_re_exp, phaseSquare_re_exp]
  linarith

/-- The gap term appearing in the Lemma 3.9 comparison. -/
def minorArcSaddleGap (t : ℝ) : ℝ := (saddleS (Real.exp t)).re ^ 2 - t ^ 2

/-- Monotonicity of the gap follows from monotonicity of the imaginary saddle component. -/
theorem monotoneOn_minorArcSaddleGap
    (hb : MonotoneOn (fun r : ℝ => (saddleS r).im) (Ici 1)) :
    MonotoneOn minorArcSaddleGap (Ici 0) := by
  intro x hx y hy hxy
  have hx' : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hy' : (1 : ℝ) ≤ Real.exp y := Real.one_le_exp_iff.mpr hy
  have h := hb hx' hy' (Real.exp_le_exp.mpr hxy)
  have hsq := pow_le_pow_left₀ ((saddleS_components (Real.exp_pos x)).1.le) h 2
  have hphase := monotone_saddlePhaseRealDiff hxy
  dsimp only at hphase
  rw [phaseReal_eq, phaseReal_eq] at hphase
  unfold minorArcSaddleGap
  linarith

theorem minorArcSaddleGap_mono : MonotoneOn minorArcSaddleGap (Ici 0) :=
  monotoneOn_minorArcSaddleGap monotoneOn_saddleS_im

/-- Left endpoint gap lower bounds printed in the finite rows, with the last entry for the tail. -/
def minorArcGapLower : Fin 18 → ℚ
  | 0 => 1.14437
  | 1 => 1.19123
  | 2 => 1.23674
  | 3 => 1.28095
  | 4 => 1.32390
  | 5 => 1.36563
  | 6 => 1.41614
  | 7 => 1.48394
  | 8 => 1.55750
  | 9 => 1.64399
  | 10 => 1.76345
  | 11 => 1.90601
  | 12 => 2.00209
  | 13 => 2.26877
  | 14 => 2.55570
  | 15 => 2.92097
  | 16 => 3.02712
  | _ => 3.09568

theorem minorArc_row_gap_check (i : Fin 18) :
    (minorArcData i).target + (0.17 : ℚ) * (minorArcData i).amplitude < minorArcGapLower i := by
  fin_cases i <;> norm_num [minorArcData, minorArcGapLower]

/-- Transfer the certified numerical endpoints and the frequency bound to the interior gap. -/
theorem minorArc_gap_of_endpoints (i : Fin 18) {t q : ℝ}
    (hl : ((minorArcData i).left : ℝ) ≤ t) (hh : t ≤ ((minorArcData i).right : ℝ))
    (hGap : (minorArcGapLower i : ℝ) < minorArcSaddleGap (minorArcData i).left)
    (hAmp : (saddleS (Real.exp (minorArcData i).right)).re ≤ ((minorArcData i).amplitude : ℝ))
    (hq : q < ((minorArcData i).target : ℝ)) :
    0.17 * (saddleS (Real.exp t)).re < minorArcSaddleGap t - q := by
  have hl0 : (0 : ℝ) ≤ ((minorArcData i).left : ℝ) := by fin_cases i <;> norm_num [minorArcData]
  have hLg := minorArcSaddleGap_mono hl0 (hl0.trans hl) hl
  have hUa := monotoneOn_saddleS_re (Real.exp_pos _) (Real.exp_pos _)
    (Real.exp_le_exp.mpr hh)
  have hrat :
      ((minorArcData i).target : ℝ) + (0.17 : ℝ) * ((minorArcData i).amplitude : ℝ) <
        (minorArcGapLower i : ℝ) := by
    have h : (((minorArcData i).target + (0.17 : ℚ) * (minorArcData i).amplitude : ℚ) : ℝ) <
        (minorArcGapLower i : ℝ) := Rat.cast_lt.mpr (minorArc_row_gap_check i)
    norm_num [Rat.cast_add, Rat.cast_mul] at h ⊢
    exact h
  linarith

private theorem re01_at_six :
    (36.8224639 : ℝ) < (saddlePhaseSquare (Real.exp 6)).re := by
  have hexp : Real.exp (-12) < (0.000006144213 : ℝ) := by
    dyadic_interval +kernel [prec := 54]
  have hx : Real.exp (-12) ≤ ((0.000006144213 : ℚ) : ℝ) := by norm_num at hexp ⊢; exact hexp.le
  have h := (saddlePartial_bounds_re 0 (p := 0) (q := 0.000006144213)
    (by norm_num) (by norm_num; exact Real.exp_nonneg (-12)) hx (by norm_num)).2
  norm_num [saddlePartialUpper, saddlePartial] at h
  have hpi₂ := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d20.le 2
  rw [phaseSquare_re_exp]
  norm_num
  linarith only [h, hpi₂]

private theorem im01_at_six :
    (18.8545134 : ℝ) < (saddlePhaseSquare (Real.exp 6)).im := by
  have hlo : (0.0024787521 : ℝ) < Real.exp (-6) := by
    dyadic_interval +kernel [prec := 48]
  have hhi : Real.exp (-6) < (0.0024787523 : ℝ) := by
    dyadic_interval +kernel [prec := 48]
  have hp : ((0.0024787521 : ℚ) : ℝ) ≤ Real.exp (-6) := by norm_num at hlo ⊢; exact hlo.le
  have hq : Real.exp (-6) ≤ ((0.0024787523 : ℚ) : ℝ) := by norm_num at hhi ⊢; exact hhi.le
  have h := (saddlePartial_bounds_im 1 (p := 0.0024787521) (q := 0.0024787523)
    (by norm_num) hp hq (by norm_num)).1
  norm_num [saddlePartial, Finset.sum_range_succ] at h
  rw [phaseSquare_im_exp (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num
  linarith only [h, Real.pi_gt_d20]

/-- Strict left endpoint inequality for the unbounded portion of the page 34 estimate. -/
theorem minorArc_gap_at_six : 3.09568 < minorArcSaddleGap 6 := by
  let a := (saddleS (Real.exp 6)).re
  let b := (saddleS (Real.exp 6)).im
  let Y := (saddlePhaseSquare (Real.exp 6)).im
  have hX : (36.8224639 : ℝ) < a ^ 2 - b ^ 2 := by
    simpa only [a, b, phaseReal_eq] using re01_at_six
  have hY : (18.8545134 : ℝ) < Y := im01_at_six
  have hYsq := pow_lt_pow_left₀ hY (by norm_num) (by decide : 2 ≠ 0)
  have hprod : Y ^ 2 = 4 * a ^ 2 * b ^ 2 := by
    dsimp only [Y, a, b]
    rw [phaseImag_eq]
    ring
  change (3.09568 : ℝ) < a ^ 2 - 6 ^ 2
  by_contra! h
  have ha : a ^ 2 ≤ 39.09568 := by nlinarith
  have hb : b ^ 2 ≤ 39.09568 - 36.8224639 := by linarith
  have hm := mul_le_mul ha hb (sq_nonneg b) (by norm_num : (0 : ℝ) ≤ 39.09568)
  rw [hprod] at hYsq
  nlinarith only [hm, hYsq]

theorem minorArc_tail_gap {t q : ℝ} (ht : 6 ≤ t) (hq : q < 1.593) :
    1.50 < minorArcSaddleGap t - q := by
  have hm := minorArcSaddleGap_mono (show (6 : ℝ) ∈ Ici 0 by norm_num)
    (show t ∈ Ici 0 from (by norm_num : (0 : ℝ) ≤ 6).trans ht) ht
  linarith only [hm, minorArc_gap_at_six, hq]

private theorem logEightyLower : (4.38 : ℝ) < Real.log 80 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  dyadic_interval +kernel [prec := 30]

private theorem logEightyUpper : Real.log (80 : ℝ) < 4.3821 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  dyadic_interval +kernel [prec := 35]

private def arcGrowth (x : ℝ) : ℝ := Real.sqrt ((Real.log x + 1) ^ 2 + 3.3)

private theorem arcGrowth_pos (x : ℝ) : 0 < arcGrowth x := by
  unfold arcGrowth
  positivity

private theorem arcGrowth_sq (x : ℝ) : arcGrowth x ^ 2 = (Real.log x + 1) ^ 2 + 3.3 := by
  unfold arcGrowth
  apply Real.sq_sqrt
  positivity

private theorem arcGrowth_eighty_lt : arcGrowth 80 < 5.681 := by
  unfold arcGrowth
  apply (Real.sqrt_lt' (by norm_num)).2
  have hlo : 0 ≤ Real.log (80 : ℝ) + 1 := by linarith [logEightyLower]
  have hhi : Real.log (80 : ℝ) + 1 ≤ 5.3821 := by linarith [logEightyUpper]
  have hs := pow_le_pow_left₀ hlo hhi 2
  nlinarith only [hs]

private theorem arcGrowth_log_ratio_lt {x : ℝ} (hx : 80 ≤ x) :
    (Real.log x + 1) / arcGrowth x ^ 2 < 0.168 := by
  let k := Real.log x + 1
  have hk : 5.38 ≤ k := by
    have h := logEightyLower.trans_le (Real.log_le_log (by norm_num) hx)
    dsimp [k]
    linarith
  apply (div_lt_iff₀ (pow_pos (arcGrowth_pos x) 2)).2
  rw [arcGrowth_sq]
  change k < 0.168 * (k ^ 2 + 3.3)
  have h1 : 0 ≤ (0.168 : ℝ) * (k + 5.38) - 1 := by linarith
  nlinarith only [mul_nonneg (sub_nonneg.mpr hk) h1]

private theorem arcGrowth_relative_le {x : ℝ} (hx : 80 ≤ x) :
    (Real.log x + 1) / arcGrowth x ^ 2 ≤ 0.168 :=
  (arcGrowth_log_ratio_lt hx).le

private theorem hasDerivAt_arcGrowth {x : ℝ} (hx : 0 < x) :
    HasDerivAt arcGrowth ((Real.log x + 1) / (x * arcGrowth x)) x := by
  have hd := (((Real.hasDerivAt_log hx.ne').add_const 1).pow 2).add_const 3.3
  have hs := (Real.hasDerivAt_sqrt (show (Real.log x + 1) ^ 2 + 3.3 ≠ 0 by positivity)).comp x hd
  change HasDerivAt arcGrowth _ x at hs
  convert hs using 1
  have hA := (arcGrowth_pos x).ne'
  dsimp only [arcGrowth] at hA ⊢
  norm_num
  field_simp

/-- The logarithmic derivative of the amplitude envelope on page 31. -/
theorem arcGrowth_relative_lt {x : ℝ} (hx : 80 ≤ x) :
    let A (t : ℝ) := Real.sqrt ((Real.log t + 1) ^ 2 + 3.3)
    x * deriv A x / A x = (Real.log x + 1) / ((Real.log x + 1) ^ 2 + 3.3) ∧
      x * deriv A x / A x < 0.168 := by
  have hx₀ : 0 < x := by linarith
  have h : x * deriv arcGrowth x / arcGrowth x = (Real.log x + 1) / arcGrowth x ^ 2 := by
    rw [(hasDerivAt_arcGrowth hx₀).deriv]
    field_simp [hx₀.ne', (arcGrowth_pos x).ne']
  change x * deriv arcGrowth x / arcGrowth x = _ ∧ x * deriv arcGrowth x / arcGrowth x < _
  exact ⟨h.trans (by rw [arcGrowth_sq]), h ▸ arcGrowth_log_ratio_lt hx⟩

private theorem hasDerivAt_arcGrowthRatio {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => x / arcGrowth x)
      ((1 - (Real.log x + 1) / arcGrowth x ^ 2) / arcGrowth x) x := by
  have hA := (arcGrowth_pos x).ne'
  have h := (hasDerivAt_id x).div (hasDerivAt_arcGrowth hx) hA
  change HasDerivAt (fun x : ℝ => x / arcGrowth x) _ x at h
  convert h using 1
  dsimp only [id]
  field_simp

private theorem mono_arcGrowthRatio : MonotoneOn (fun x : ℝ => x / arcGrowth x) (Ici 80) := by
  have hd (x : ℝ) (hx : x ∈ Ici 80) :=
    hasDerivAt_arcGrowthRatio (show 0 < x from (by norm_num : (0 : ℝ) < 80).trans_le hx)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 80 ≤ x := interior_subset hx
    rw [(hd x hx').deriv]
    exact div_nonneg (by linarith [arcGrowth_relative_le hx']) (arcGrowth_pos x).le

private theorem arcGrowthRatio_lower {x : ℝ} (hx : 80 ≤ x) : 13.8 ≤ x / arcGrowth x := by
  calc
    _ ≤ 80 / arcGrowth 80 := by
      apply (le_div_iff₀ (arcGrowth_pos 80)).2
      linarith [arcGrowth_eighty_lt]
    _ ≤ _ := mono_arcGrowthRatio (show (80 : ℝ) ∈ Ici 80 from le_rfl) hx hx

private theorem antitone_midArcGrowthDecay :
    AntitoneOn (fun x : ℝ => x ^ 2 * Real.exp (-1.50 * (x / arcGrowth x))) (Ici 80) := by
  let f := fun x : ℝ => x ^ 2 * Real.exp (-1.50 * (x / arcGrowth x))
  have hd (x : ℝ) (hx : x ∈ Ici 80) : HasDerivAt f
      (x * Real.exp (-1.50 * (x / arcGrowth x)) *
        (2 - 1.50 * (x / arcGrowth x) * (1 - (Real.log x + 1) / arcGrowth x ^ 2))) x := by
    have hx0 : 0 < x := (by norm_num : (0 : ℝ) < 80).trans_le hx
    have h := (hasDerivAt_pow 2 x).mul
      (((hasDerivAt_arcGrowthRatio hx0).const_mul (-1.50)).exp)
    change HasDerivAt f _ x at h
    convert h using 1
    norm_num
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 80 ≤ x := interior_subset hx
    have hRatio := arcGrowthRatio_lower hx'
    have hRel := arcGrowth_relative_le hx'
    have hd' : 2 ≤ 1.50 * (x / arcGrowth x) * (1 - (Real.log x + 1) / arcGrowth x ^ 2) := by
      calc
        _ ≤ (1.50 : ℝ) * 13.8 * (1 - 0.168) := by norm_num
        _ ≤ _ := by gcongr
    have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 80).trans hx'
    rw [(hd x hx').deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hd')

private theorem minorArc_first_at_eighty :
    2 * Real.pi * (80 : ℝ) ^ 2 * Real.exp (-0.17 * 80) < 0.049884 := by
  have hpi := Real.pi_lt_d20
  dyadic_interval +kernel [prec := 52]

private theorem minorArc_second_at_eighty :
    2 * Real.pi * (80 : ℝ) ^ 2 * Real.exp (-1.50 * (80 / arcGrowth 80)) < 0.000027 := by
  have h : 21.122 ≤ 1.50 * (80 / arcGrowth 80) := by
    rw [← mul_div_assoc, le_div_iff₀ (arcGrowth_pos 80)]
    linarith [arcGrowth_eighty_lt]
  calc
    _ ≤ 2 * Real.pi * (80 : ℝ) ^ 2 * Real.exp (-21.122) := by
      gcongr
      linarith
    _ < _ := by
      have hpi := Real.pi_lt_d20
      dyadic_interval +kernel [prec := 60]

/-- First normalized exponential error on the full range `√n ≥ 80`. -/
theorem minorArc_first_exp_bound {x : ℝ} (hx : 80 ≤ x) :
    2 * Real.pi * x ^ 2 * Real.exp (-0.17 * x) < 0.049884 := by
  have hm := power_mul_exp_antitoneOn (x₀ := 80) (a := 0.17) (b := 0) 2 1
    (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
  have hh := hm (show (80 : ℝ) ∈ Ici 80 from le_rfl) hx hx
  simp only [pow_one, add_zero] at hh
  calc
    _ = (2 * Real.pi) * (x ^ 2 * Real.exp (-0.17 * x)) := by ring
    _ ≤ (2 * Real.pi) * ((80 : ℝ) ^ 2 * Real.exp (-0.17 * 80)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ < _ := by simpa only [← mul_assoc] using minorArc_first_at_eighty

/-- Second normalized exponential error on the full range `√n ≥ 80`. -/
theorem minorArc_second_exp_bound {x : ℝ} (hx : 80 ≤ x) :
    2 * Real.pi * x ^ 2 * Real.exp (-1.50 * (x / Real.sqrt ((Real.log x + 1) ^ 2 + 3.3))) <
      0.000027 := by
  change 2 * Real.pi * x ^ 2 * Real.exp (-1.50 * (x / arcGrowth x)) < _
  have h := antitone_midArcGrowthDecay (show (80 : ℝ) ∈ Ici 80 from le_rfl) hx hx
  calc
    _ = (2 * Real.pi) * (x ^ 2 * Real.exp (-1.50 * (x / arcGrowth x))) := by ring
    _ ≤ (2 * Real.pi) * ((80 : ℝ) ^ 2 * Real.exp (-1.50 * (80 / arcGrowth 80))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ < _ := by simpa only [← mul_assoc] using minorArc_second_at_eighty

/-- Bounding the imaginary saddle term by its limiting scale on the logarithmic ray. -/
theorem saddleS_exp_im_lt_pi_half {t : ℝ} (ht : 0 ≤ t) :
    (saddleS (Real.exp t)).im < Real.pi / 2 := by
  let X := (saddlePhaseSquare (Real.exp t)).re
  let Y := (saddlePhaseSquare (Real.exp t)).im
  let a := (saddleS (Real.exp t)).re
  let b := (saddleS (Real.exp t)).im
  let r := Real.exp (-t)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have htr : t * r ≤ 1 := (Real.mul_exp_neg_le_exp_neg_one t).trans
    (Real.exp_le_one_iff.mpr (by norm_num))
  have hX : t ^ 2 + Real.pi ^ 2 / 24 ≤ X := by
    have hh := monotone_saddlePhaseRealDiff ht
    dsimp only at hh
    rw [Real.exp_zero, phaseSquare_re_one] at hh
    dsimp only [X]
    linarith
  have hY : Y ≤ Real.pi * t + 2 * r := by
    dsimp only [Y]
    rw [phaseSquare_im_exp ht]
    linarith only [dilog_negImag_le_self hr.le hr1]
  have hY0 : 0 ≤ Y := ((saddlePhaseSquare_quadrant (Real.exp_pos _)).2).le
  have hp4 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d2.le 4
  have hc : 4 * Real.pi + 4 < 7 * Real.pi ^ 4 / 24 := by
    linarith only [hp4, Real.pi_lt_d2]
  have hbnd : Y ^ 2 < Real.pi ^ 2 * (X + Real.pi ^ 2 / 4) := by
    calc
      _ ≤ (Real.pi * t + 2 * r) ^ 2 := pow_le_pow_left₀ hY0 hY 2
      _ = Real.pi ^ 2 * t ^ 2 + 4 * Real.pi * (t * r) + 4 * r ^ 2 := by ring
      _ ≤ Real.pi ^ 2 * t ^ 2 + 4 * Real.pi + 4 := by
        have h := mul_le_mul_of_nonneg_left htr (by positivity : 0 ≤ 4 * Real.pi)
        have hs := pow_le_pow_left₀ hr.le hr1 2
        linarith
      _ < Real.pi ^ 2 * t ^ 2 + 7 * Real.pi ^ 4 / 24 := by linarith only [hc]
      _ = Real.pi ^ 2 * (t ^ 2 + 7 * Real.pi ^ 2 / 24) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hX]) (sq_nonneg Real.pi)
  change b < Real.pi / 2
  by_contra! h
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi / 2) h 2
  have ha : 0 < a := (saddleS_components (Real.exp_pos t)).1.trans
    (saddleS_components (Real.exp_pos t)).2
  have heX : X = a ^ 2 - b ^ 2 := phaseReal_eq _
  have heY : Y = 2 * a * b := phaseImag_eq _
  have hh1 := mul_le_mul_of_nonneg_left hs (sq_nonneg a)
  have hh2 : X + Real.pi ^ 2 / 4 ≤ a ^ 2 := by linarith only [hs, heX]
  have hh3 := mul_le_mul_of_nonneg_left hh2 (sq_nonneg Real.pi)
  rw [heY] at hbnd
  nlinarith only [hh1, hh3, hbnd]

/-- The sharp elementary amplitude majorant before rounding its constant outward. -/
theorem saddleS_exp_re_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (saddleS (Real.exp t)).re ^ 2 ≤ t ^ 2 + Real.pi ^ 2 / 3 := by
  have hb := (saddleS_exp_im_lt_pi_half ht).le
  have hab := saddleS_components (Real.exp_pos t)
  have hbsq := pow_le_pow_left₀ hab.1.le hb 2
  have hneg := dilog_neg_real_re_nonpos (Real.exp_nonneg (-2 * t))
    (Real.exp_le_one_iff.mpr (by linarith : -2 * t ≤ 0))
  have hA := phaseReal_eq (Real.exp t)
  rw [phaseSquare_re_exp] at hA
  nlinarith only [hA, hneg, hbsq]

/-- Saddle amplitude bound used in the unbounded range of Lemma 3.9. -/
theorem saddleS_exp_re_lt_growth {t : ℝ} (ht : 0 ≤ t) :
    (saddleS (Real.exp t)).re < Real.sqrt (t ^ 2 + 3.3) := by
  let a := (saddleS (Real.exp t)).re
  have hab := saddleS_components (Real.exp_pos t)
  have hπ := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 2
  have hA := saddleS_exp_re_sq_le ht
  have hs : a ^ 2 < t ^ 2 + 3.3 := by
    dsimp only [a]
    linarith only [hA, hπ]
  change a < Real.sqrt _
  have hp : 0 ≤ a := (hab.1.trans hab.2).le
  rw [← Real.sqrt_sq hp]
  exact Real.sqrt_lt_sqrt (sq_nonneg a) hs

/-- Transfer a nonnegative logarithmic radius up to `1 + log x` to the growth bound. -/
theorem saddleS_exp_re_le_arcGrowth {x t : ℝ} (ht : 0 ≤ t) (htx : t ≤ Real.log x + 1) :
    (saddleS (Real.exp t)).re ≤ Real.sqrt ((Real.log x + 1) ^ 2 + 3.3) := by
  apply (saddleS_exp_re_lt_growth ht).le.trans
  exact Real.sqrt_le_sqrt (by linarith only [pow_le_pow_left₀ ht htx 2])

/-- Transfer a small-radius gap bound and the normalized exponential estimate to the printed error. -/
theorem minorArc_first_error_of_gap {x t q E : ℝ} (hx : 80 ≤ x)
    (hGap : 0.17 * (saddleS (Real.exp t)).re ≤ minorArcSaddleGap t - q)
    (hE : E ≤ 2 * Real.pi * x ^ 2 *
      Real.exp (-x * (minorArcSaddleGap t - q) / (saddleS (Real.exp t)).re)) :
    E < 0.049884 := by
  have hx0 : 0 ≤ x := by linarith
  have hab := saddleS_components (Real.exp_pos t)
  have ha := hab.1.trans hab.2
  have hdiv : (0.17 : ℝ) ≤ (minorArcSaddleGap t - q) / (saddleS (Real.exp t)).re :=
    (le_div_iff₀ ha).2 hGap
  refine hE.trans_lt ?_
  refine lt_of_le_of_lt ?_ (minorArc_first_exp_bound hx)
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
  rw [mul_div_assoc]
  have hh := mul_le_mul_of_nonneg_right hdiv hx0
  linarith only [hh, show -(x : ℝ) * ((minorArcSaddleGap t - q) / (saddleS (Real.exp t)).re) =
    -((minorArcSaddleGap t - q) / (saddleS (Real.exp t)).re * x) by ring]

/-- Transfer the far-tail gap and the normalized exponential estimate to the printed error. -/
theorem minorArc_second_error_of_gap {x t q E : ℝ} (hx : 80 ≤ x) (ht : 6 ≤ t)
    (htx : t ≤ Real.log x + 1) (hq : q < 1.593)
    (hE : E ≤ 2 * Real.pi * x ^ 2 *
      Real.exp (-x * (minorArcSaddleGap t - q) / (saddleS (Real.exp t)).re)) :
    E < 0.000027 := by
  have hx0 : 0 ≤ x := by linarith
  have hab := saddleS_components (Real.exp_pos t)
  have ha := hab.1.trans hab.2
  have hA : (saddleS (Real.exp t)).re ≤ arcGrowth x := saddleS_exp_re_le_arcGrowth (by linarith) htx
  have hG := (minorArc_tail_gap ht hq).le
  have Hd : 1.50 / arcGrowth x ≤ (minorArcSaddleGap t - q) / (saddleS (Real.exp t)).re :=
    div_le_div₀ (by linarith) hG ha hA
  refine hE.trans_lt ?_
  refine lt_of_le_of_lt ?_ (minorArc_second_exp_bound hx)
  change 2 * Real.pi * x ^ 2 *
      Real.exp (-x * (minorArcSaddleGap t - q) / (saddleS (Real.exp t)).re) ≤
    2 * Real.pi * x ^ 2 * Real.exp (-1.50 * (x / arcGrowth x))
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
  rw [mul_div_assoc]
  have hh := mul_le_mul_of_nonneg_right Hd hx0
  linarith only [hh, show -(x : ℝ) * ((minorArcSaddleGap t - q) / (saddleS (Real.exp t)).re) =
    -((minorArcSaddleGap t - q) / (saddleS (Real.exp t)).re * x) by ring,
    show -1.50 * (x / arcGrowth x) = -(1.50 / arcGrowth x * x) by ring]

end DurfeeCCS.Step07
