module

public import DurfeeCCS.Step07.SaddleGlobalMonotone

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Differentiation and strict increase of the two saddle coordinates. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex Set DurfeeCCS.Step06 DurfeeCCS.Step07

theorem hasDerivAt_saddleS_middle {r : ℝ} (hr : 0 < r) :
    HasDerivAt saddleS
      (Complex.log (1+(r : ℂ)*I) / ((r : ℂ)*saddleS r)) r := by
  have hZ : saddlePhaseSquare r ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (saddlePhaseSquare_quadrant hr).1)
  have hS : saddleS r ≠ 0 := fun h => (saddleS_components hr).1.ne' (by simp [h])
  have hR : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have h := (Complex.hasDerivAt_sqrt hZ).scomp r (hasDerivAt_saddlePhaseSquare hr)
  change HasDerivAt saddleS _ r at h
  convert h using 1
  rw [smul_eq_mul, neg_div, Complex.cpow_neg,
    show saddlePhaseSquare r ^ (1/2 : ℂ) = saddleS r by rw [saddleS,Complex.sqrt,one_div]]
  field_simp [hR,hS]

theorem saddleS_middle_velocity_re_pos {r : ℝ} (hr : 0 < r) :
    0 < (Complex.log (1+(r : ℂ)*I) / ((r : ℂ)*saddleS r)).re := by
  let L := Complex.log (1+(r : ℂ)*I)
  have hLr : 0 < L.re := by
    unfold L
    rw [Complex.log_re, Complex.norm_eq_sqrt_sq_add_sq]
    apply Real.log_pos
    rw [Real.lt_sqrt (by norm_num)]
    simp only [Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,zero_mul,mul_one,sub_zero,add_zero,zero_add]
    linarith only [sq_pos_of_pos hr]
  have hLi : 0 ≤ L.im := by
    unfold L
    rw [Complex.log_im]
    apply Complex.arg_nonneg_iff.mpr
    simpa [Complex.mul_im] using hr.le
  obtain ⟨hb,hab⟩ := saddleS_components hr
  have hS : saddleS r ≠ 0 := fun h => hb.ne' (by simp [h])
  change 0 < (L/((r : ℂ)*saddleS r)).re
  rw [mul_comm (r : ℂ),← div_div,Complex.div_ofReal_re,Complex.div_re,← add_div]
  exact div_pos (div_pos (add_pos_of_pos_of_nonneg (mul_pos hLr (hb.trans hab))
    (mul_nonneg hLi hb.le)) (normSq_pos.mpr hS)) hr

theorem strictMonoOn_saddleS_re_positive :
    StrictMonoOn (fun r : ℝ => (saddleS r).re) (Ioi 0) := by
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt (fun r : ℝ => (saddleS r).re)
      (Complex.log (1+(r : ℂ)*I) / ((r : ℂ)*saddleS r)).re r :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_saddleS_middle hr)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun r hr => (hd r hr).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : 0 < r := interior_subset hr
    rw [(hd r hr').deriv]
    exact saddleS_middle_velocity_re_pos hr'

theorem midSaddle_strictMono :
    StrictMonoOn (fun r : ℝ => (saddleS r).re) (Ici 1) ∧
    StrictMonoOn (fun r : ℝ => (saddleS r).im) (Ici 1) :=
  ⟨strictMonoOn_saddleS_re_positive.mono (fun _ h => zero_lt_one.trans_le h),
    strictMonoOn_saddleS_im.mono (fun _ h => zero_lt_one.trans_le h)⟩

end DurfeeCCS.Step09
