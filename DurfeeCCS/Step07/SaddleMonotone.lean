module

public import DurfeeCCS.Step06.Saddle
public import DurfeeCCS.Step07.ElementaryBounds

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Monotonicity of the saddle components on the first radius interval. -/

@[expose] public section

namespace DurfeeCCS.Step07

open Complex Set DurfeeCCS.Step06

private noncomputable def squareExt (z : ℂ) : ℂ :=
  -2 * principalDilog (-z * I)

private theorem hasDerivAt_squareExt {r : ℝ} (hr : 0 < r) :
    HasDerivAt squareExt (2 * Complex.log (1 + (r : ℂ) * I) / (r : ℂ)) (r : ℂ) := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hz : -(r : ℂ) * I ∈ dilogCut := mem_dilogCut_iff.mpr (Or.inl (by simp))
  have hn : -(r : ℂ) * I ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hrC) I_ne_zero
  have h := hasDerivAt_principalDilog hz
  rw [ite_eq_right hn, show 1 - -(r : ℂ) * I = 1 + (r : ℂ) * I by ring] at h
  have hl := (hasDerivAt_id (r : ℂ)).neg.mul_const I
  have hs := (h.comp (r : ℂ) hl).const_mul (-2)
  convert hs using 1
  · rfl
  · field_simp [hrC, I_ne_zero]

theorem hasDerivAt_saddlePhaseSquare {r : ℝ} (hr : 0 < r) :
    HasDerivAt saddlePhaseSquare (2 * Complex.log (1 + (r : ℂ) * I) / (r : ℂ)) r :=
  (hasDerivAt_squareExt hr).comp_ofReal

private theorem arg_one_add_mul_I (r : ℝ) : (1 + (r : ℂ) * I).arg = Real.arctan r := by
  let z : ℂ := 1 + (r : ℂ) * I
  have hre : z.re = 1 := by simp [z, Complex.mul_re]
  have him : z.im = r := by simp [z, Complex.mul_im]
  have hrange := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; norm_num)))
  change z.arg = Real.arctan r
  rw [← Real.arctan_tan hrange.1 hrange.2, Complex.tan_arg, hre, him, div_one]

private theorem hasDerivAt_phaseSquare_re {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => (saddlePhaseSquare r).re)
      (2 * Real.log ‖1 + (r : ℂ) * I‖ / r) r := by
  simpa only [squareExt, saddlePhaseSquare, Complex.div_ofReal_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, Complex.log_re] using
    (hasDerivAt_squareExt hr).real_of_complex

private theorem hasDerivAt_phaseSquare_im {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => (saddlePhaseSquare r).im) (2 * Real.arctan r / r) r := by
  simpa only [squareExt, saddlePhaseSquare, Complex.mul_re, Complex.div_ofReal_im,
    Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, I_re, I_im, Complex.neg_re,
    Complex.neg_im, neg_zero, zero_mul, neg_one_mul, sub_neg_eq_add, zero_add,
    add_zero, Complex.log_im, arg_one_add_mul_I] using
    ((hasDerivAt_squareExt hr).const_mul (-I)).real_of_complex

private theorem log_norm_one_add_mul_I_nonneg (r : ℝ) : 0 ≤ Real.log ‖1 + (r : ℂ) * I‖ := by
  apply Real.log_nonneg
  simpa [Complex.mul_re] using Complex.re_le_norm (1 + (r : ℂ) * I)

private theorem monotoneOn_phaseSquare_re :
    MonotoneOn (fun r : ℝ => (saddlePhaseSquare r).re) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · exact fun _ h => (hasDerivAt_phaseSquare_re h).continuousAt.continuousWithinAt
  · exact fun _ h => (hasDerivAt_phaseSquare_re (interior_subset h)).differentiableAt.differentiableWithinAt
  · intro r h
    have hr := interior_subset h
    rw [(hasDerivAt_phaseSquare_re hr).deriv]
    exact div_nonneg (mul_nonneg (by norm_num) (log_norm_one_add_mul_I_nonneg r)) hr.le

private theorem monotoneOn_phaseSquare_im :
    MonotoneOn (fun r : ℝ => (saddlePhaseSquare r).im) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · exact fun _ h => (hasDerivAt_phaseSquare_im h).continuousAt.continuousWithinAt
  · exact fun _ h => (hasDerivAt_phaseSquare_im (interior_subset h)).differentiableAt.differentiableWithinAt
  · intro r h
    have hr := interior_subset h
    rw [(hasDerivAt_phaseSquare_im hr).deriv]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.arctan_nonneg.mpr hr.le)) hr.le

private theorem phaseSquare_re_eq (r : ℝ) :
    (saddlePhaseSquare r).re = (saddleS r).re ^ 2 - (saddleS r).im ^ 2 := by
  rw [← saddleS_sq r, pow_two, Complex.mul_re, ← pow_two, ← pow_two]

private theorem phaseSquare_im_eq (r : ℝ) :
    (saddlePhaseSquare r).im = 2 * (saddleS r).re * (saddleS r).im := by
  rw [← saddleS_sq r, pow_two, Complex.mul_im]
  ring

/-- The real component of the principal saddle is increasing on the positive axis. -/
theorem monotoneOn_saddleS_re : MonotoneOn (fun r => (saddleS r).re) (Ioi 0) := by
  intro r hr s hs hrs
  obtain ⟨hbr, har⟩ := saddleS_components hr
  obtain ⟨hbs, has⟩ := saddleS_components hs
  have hX := monotoneOn_phaseSquare_re hr hs hrs
  have hY := monotoneOn_phaseSquare_im hr hs hrs
  dsimp only at hX hY ⊢
  rw [phaseSquare_re_eq r, phaseSquare_re_eq s] at hX
  rw [phaseSquare_im_eq r, phaseSquare_im_eq s] at hY
  by_contra! h
  have ha₂ := pow_lt_pow_left₀ h (hbs.trans has).le (by decide : 2 ≠ 0)
  have hb₂ : (saddleS s).im ^ 2 < (saddleS r).im ^ 2 := by linarith
  have hb := (sq_lt_sq₀ hbs.le hbr.le).mp hb₂
  have hmul := mul_lt_mul_of_pos_right h hbs
  have hmul' := mul_le_mul_of_nonneg_left hb.le (hbr.trans har).le
  linarith only [hY, hmul.trans_le hmul']

private theorem exp_one_sixteenth_le :
    Real.exp (1 / 16) ≤ (1.1 : ℝ) := by
  refine (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans ?_
  norm_num

private theorem log_norm_le_arctan_on_first {r : ℝ}
    (hr : r ∈ Icc 1 (Real.exp (1 / 16))) :
    Real.log ‖1 + (r : ℂ) * I‖ ≤ Real.arctan r := by
  have hru : r ≤ 1.1 := hr.2.trans exp_one_sixteenth_le
  have hr₀ : 0 < r := zero_lt_one.trans_le hr.1
  have hn : ‖1 + (r : ℂ) * I‖ ≤ 1.5 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    simp [Complex.mul_re, Complex.mul_im]
    nlinarith [mul_nonneg hr₀.le (sub_nonneg.mpr hru)]
  have hn₀ : 0 < ‖1 + (r : ℂ) * I‖ := by
    have h := Complex.re_le_norm (1 + (r : ℂ) * I)
    simp [Complex.mul_re] at h
    linarith
  have hlog := Real.log_le_sub_one_of_pos hn₀
  have ha := Real.arctan_le_arctan_iff.mpr hr.1
  rw [Real.arctan_one] at ha
  linarith [Real.pi_gt_d2]

private theorem monotoneOn_phaseSquare_im_sub_re_first :
    MonotoneOn (fun r : ℝ => (saddlePhaseSquare r).im - (saddlePhaseSquare r).re)
      (Icc 1 (Real.exp (1 / 16))) := by
  have hD (r : ℝ) (hr : r ∈ Icc 1 (Real.exp (1 / 16))) :
      HasDerivAt (fun t => (saddlePhaseSquare t).im - (saddlePhaseSquare t).re)
        (2 * Real.arctan r / r - 2 * Real.log ‖1 + (r : ℂ) * I‖ / r) r :=
    (hasDerivAt_phaseSquare_im (zero_lt_one.trans_le hr.1)).sub
      (hasDerivAt_phaseSquare_re (zero_lt_one.trans_le hr.1))
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun r h => (hD r h).continuousAt.continuousWithinAt
  · exact fun r h => (hD r (interior_subset h)).differentiableAt.differentiableWithinAt
  · intro r h
    have hr := interior_subset h
    rw [(hD r hr).deriv]
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (log_norm_le_arctan_on_first hr) (by norm_num))
      (zero_le_one.trans hr.1)

/-- The imaginary component is increasing over the radius interval of the first row. -/
theorem monotoneOn_saddleS_im_first :
    MonotoneOn (fun r => (saddleS r).im) (Icc 1 (Real.exp (1 / 16))) := by
  intro r hr s hs hrs
  have hr₀ := zero_lt_one.trans_le hr.1
  have hs₀ := zero_lt_one.trans_le hs.1
  have ha := monotoneOn_saddleS_re hr₀ hs₀ hrs
  have hGap := monotoneOn_phaseSquare_im_sub_re_first hr hs hrs
  dsimp only at ha hGap ⊢
  have ⟨hbr, har⟩ := saddleS_components hr₀
  have ⟨hbs, _⟩ := saddleS_components hs₀
  by_contra! hb
  have hB := pow_lt_pow_left₀ hb hbs.le (by decide : 2 ≠ 0)
  have hD : (saddleS r).re - (saddleS r).im < (saddleS s).re - (saddleS s).im := by
    linarith only [ha, hb]
  have hD₂ := pow_lt_pow_left₀ hD (sub_nonneg.mpr har.le) (by decide : 2 ≠ 0)
  rw [phaseSquare_im_eq r, phaseSquare_re_eq r, phaseSquare_im_eq s, phaseSquare_re_eq s] at hGap
  nlinarith only [hB, hD₂, hGap]

end DurfeeCCS.Step07
