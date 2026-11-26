module

public import DurfeeCCS.Step07.SaddleMonotone
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Landen's identity controls the direction of the derivative of the saddle. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open Complex Set MeasureTheory DurfeeCCS.Step06

private def ell (x : ℝ) : ℝ := Real.log (1 + x ^ 2) / 2
private def L (x : ℝ) : ℂ := Complex.log (1 + (x : ℂ) * I)
private def W (x : ℝ) : ℂ := (x : ℂ) * I / (1 + (x : ℂ) * I)

private theorem one_add_mul_I_ne_zero (x : ℝ) : 1 + (x : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [Complex.mul_re] at this

private theorem L_re (x : ℝ) : (L x).re = ell x := by
  rw [L, Complex.log_re, Complex.norm_eq_sqrt_sq_add_sq]
  simp [ell, Complex.mul_re, Complex.mul_im, Real.log_sqrt (by positivity : 0 ≤ 1 + x ^ 2)]

private theorem L_im (x : ℝ) : (L x).im = Real.arctan x := by
  let z : ℂ := 1 + (x : ℂ) * I
  have hre : z.re = 1 := by simp [z, Complex.mul_re]
  have him : z.im = x := by simp [z, Complex.mul_im]
  have ht := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; norm_num)))
  rw [L, Complex.log_im]
  change z.arg = Real.arctan x
  rw [← Real.arctan_tan ht.1 ht.2, Complex.tan_arg, hre, him, div_one]

private theorem hasDerivAt_ell (x : ℝ) :
    HasDerivAt ell (x / (1 + x ^ 2)) x := by
  have h := (((hasDerivAt_pow 2 x).const_add 1).log (by positivity)).div_const 2
  unfold ell
  convert h using 1
  norm_num
  ring

private theorem ell_strictMono : StrictMonoOn ell (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact fun x _ => (hasDerivAt_ell x).continuousAt.continuousWithinAt
  · intro x hx
    rw [(hasDerivAt_ell x).deriv]
    exact div_pos (by simpa using hx) (by positivity)

private theorem ell_le_mul_arctan {x : ℝ} (hx : 0 ≤ x) : ell x ≤ x * Real.arctan x := by
  let f (t : ℝ) := t * Real.arctan t - ell t
  have hf (t : ℝ) : HasDerivAt f (Real.arctan t) t := by
    convert ((hasDerivAt_id t).mul (Real.hasDerivAt_arctan t)).sub (hasDerivAt_ell t) using 1
    · funext u
      rfl
    · simp only [id_eq, one_mul]
      ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hf t).continuousAt.continuousWithinAt
    · exact fun t _ => (hf t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hf t).deriv]
      exact Real.arctan_nonneg.mpr (interior_subset ht)
  have h := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hx hx
  simpa [f, ell, sub_nonneg] using h

private theorem ell_arctan_cross {y r : ℝ} (hy : 0 ≤ y) (hyr : y ≤ r) (hr : 0 < r) :
    ell y * Real.arctan r ≤ ell r * Real.arctan y := by
  rcases eq_or_lt_of_le hy with rfl | hy'
  · simp [ell]
  · let f (t : ℝ) := ell t / Real.arctan t
    have hf (t : ℝ) (ht : 0 < t) :
        HasDerivAt f ((t * Real.arctan t - ell t) /
          ((1 + t ^ 2) * Real.arctan t ^ 2)) t := by
      have hθ := (Real.arctan_pos.mpr ht).ne'
      convert (hasDerivAt_ell t).div (Real.hasDerivAt_arctan t) hθ using 1
      field_simp [hθ]
    have hm : MonotoneOn f (Ioi 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
      · exact fun t ht => (hf t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' : 0 < t := interior_subset ht
        rw [(hf t ht').deriv]
        exact div_nonneg (sub_nonneg.mpr (ell_le_mul_arctan ht'.le)) (by positivity)
    exact (div_le_div_iff₀ (Real.arctan_pos.mpr hy') (Real.arctan_pos.mpr hr)).mp (hm hy' hr hyr)

private theorem log_quotient (r y : ℝ) (hr : 0 ≤ r) (hy : 0 ≤ y) :
    Complex.log ((1 + (y : ℂ) * I) / (1 + (r : ℂ) * I)) = L y - L r := by
  have hA := one_add_mul_I_ne_zero r
  have hB := one_add_mul_I_ne_zero y
  have he : Complex.exp (L y - L r) = (1 + (y : ℂ) * I) / (1 + (r : ℂ) * I) := by
    rw [Complex.exp_sub, L, L, Complex.exp_log hB, Complex.exp_log hA]
  rw [← he, Complex.log_exp]
  · rw [Complex.sub_im, L_im, L_im]
    linarith [Real.arctan_nonneg.mpr hy, Real.arctan_lt_pi_div_two r, Real.pi_pos]
  · rw [Complex.sub_im, L_im, L_im]
    linarith [Real.arctan_nonneg.mpr hr, Real.arctan_lt_pi_div_two y, Real.pi_pos]

private theorem W_cut (r : ℝ) : W r ∈ dilogCut := by
  have he : 1 - W r = (1 + (r : ℂ) * I)⁻¹ := by
    unfold W
    field_simp [one_add_mul_I_ne_zero]
    ring
  change 1 - W r ∈ slitPlane
  rw [he]
  apply mem_slitPlane_iff.mpr
  left
  rw [Complex.inv_re]
  exact div_pos (by simp [Complex.mul_re]) (normSq_pos.mpr (one_add_mul_I_ne_zero r))

private theorem kernel_coordinates {r u : ℝ} (hr : 0 < r) (hu : u ∈ Ioo 0 1) :
    (dilogKernel (W r) u).re = (ell r - ell (r * (1 - u))) / u ∧
    (dilogKernel (W r) u).im = (Real.arctan r - Real.arctan (r * (1 - u))) / u := by
  have hy : 0 ≤ r * (1 - u) := mul_nonneg hr.le (sub_nonneg.mpr hu.2.le)
  have he : 1 - (u : ℂ) * W r = (1 + ((r * (1 - u) : ℝ) : ℂ) * I) / (1 + (r : ℂ) * I) := by
    unfold W
    push_cast
    field_simp [one_add_mul_I_ne_zero]
    ring
  rw [dilogKernel, ite_eq_right hu.1.ne', he, log_quotient r _ hr.le hy,
    neg_sub]
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
    L_re, L_im, and_self]

private theorem landenDilog_cone {r : ℝ} (hr : 0 < r) :
    let z := principalDilog (W r)
    0 < z.re ∧ 0 ≤ z.im ∧ z.im * ell r ≤ z.re * Real.arctan r := by
  let f := dilogKernel (W r)
  have hf : IntervalIntegrable f volume 0 1 := intervalIntegrable_dilogKernel (W_cut r)
  have hcont : ContinuousOn f (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le zero_le_one] using continuousOn_dilogKernel (W_cut r)
  have hre : IntervalIntegrable (fun u => (f u).re) volume 0 1 :=
    (Complex.continuous_re.comp_continuousOn hcont).intervalIntegrable
  have him : IntervalIntegrable (fun u => (f u).im) volume 0 1 :=
    (Complex.continuous_im.comp_continuousOn hcont).intervalIntegrable
  have hff (u : ℝ) (hu : u ∈ Ioo 0 1) :
      0 < (f u).re ∧ 0 ≤ (f u).im ∧ (f u).im * ell r ≤ (f u).re * Real.arctan r := by
    let y := r * (1 - u)
    have hy : 0 ≤ y := mul_nonneg hr.le (sub_nonneg.mpr hu.2.le)
    have hyr : y < r := mul_lt_of_lt_one_right hr (by linarith [hu.1])
    obtain ⟨he, hi⟩ := kernel_coordinates hr hu
    change (f u).re = (ell r - ell y) / u at he
    change (f u).im = (Real.arctan r - Real.arctan y) / u at hi
    rw [he, hi]
    refine ⟨div_pos (sub_pos.mpr (ell_strictMono hy hr.le hyr)) hu.1,
      div_nonneg (sub_nonneg.mpr (Real.arctan_mono hyr.le)) hu.1.le, ?_⟩
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hu.1]
    nlinarith [ell_arctan_cross hy hyr.le hr]
  have hp := intervalIntegral.intervalIntegral_pos_of_pos_on hre (fun u hu => (hff u hu).1) zero_lt_one
  have hqi := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one intervalIntegrable_const him
    (fun u hu => (hff u hu).2.1)
  have hq := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
    (him.mul_const (ell r)) (hre.mul_const (Real.arctan r)) (fun u hu => (hff u hu).2.2)
  have hre_eq : (∫ u : ℝ in (0 : ℝ)..1, (f u).re) = (∫ u : ℝ in (0 : ℝ)..1, f u).re :=
    intervalIntegral.intervalIntegral_re hf
  have him_eq : (∫ u : ℝ in (0 : ℝ)..1, (f u).im) = (∫ u : ℝ in (0 : ℝ)..1, f u).im :=
    intervalIntegral.intervalIntegral_im hf
  rw [hre_eq] at hp
  rw [him_eq] at hqi
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    him_eq, hre_eq] at hq
  simpa [principalDilog, f] using And.intro hp (And.intro hqi hq)

private theorem saddle_landen (r : ℝ) :
    saddleS r ^ 2 = L r ^ 2 + 2 * principalDilog (W r) := by
  have hz : -(r : ℂ) * I ∈ dilogCut := mem_dilogCut_iff.mpr (Or.inl (by simp))
  have hmap : (-(r : ℂ) * I) / (-(r : ℂ) * I - 1) = W r := by
    unfold W
    rw [show -(r : ℂ) * I - 1 = -(1 + (r : ℂ) * I) by ring, neg_mul, neg_div_neg_eq]
  have he := principalDilog_landen hz
  rw [hmap, show 1 - -(r : ℂ) * I = 1 + (r : ℂ) * I by ring, ← L] at he
  rw [saddleS_sq, saddlePhaseSquare]
  linear_combination -2 * he

private theorem saddle_quotient_im_neg {r : ℝ} (hr : 0 < r) :
    (saddleS r / L r).im < 0 := by
  let Z := principalDilog (W r)
  let Q := Z / L r
  have hLr : 0 < (L r).re := by
    rw [L_re, ell]
    exact div_pos (Real.log_pos (by linarith [sq_pos_of_pos hr])) (by norm_num)
  have hLi : 0 < (L r).im := by rw [L_im]; exact Real.arctan_pos.mpr hr
  have hLne : L r ≠ 0 := fun h => hLi.ne' (by simp [h])
  have hLn : 0 < normSq (L r) := normSq_pos.mpr hLne
  obtain ⟨hZr, hZi, hcross⟩ := landenDilog_cone hr
  have hQr : 0 < Q.re := by
    rw [show Q = Z / L r from rfl, Complex.div_re, ← add_div]
    exact div_pos (add_pos_of_pos_of_nonneg (mul_pos hZr hLr) (mul_nonneg hZi hLi.le)) hLn
  have hQi : Q.im ≤ 0 := by
    rw [show Q = Z / L r from rfl, Complex.div_im, ← sub_div]
    refine div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ?_) hLn.le
    simpa only [L_re, L_im, Z] using hcross
  have hQQ : (Q / L r).im < 0 := by
    rw [Complex.div_im, ← sub_div]
    exact div_neg_of_neg_of_pos
      (sub_neg.mpr ((mul_nonpos_of_nonpos_of_nonneg hQi hLr.le).trans_lt (mul_pos hQr hLi))) hLn
  have hs : (saddleS r / L r)^2 = 1 + 2 * (Q / L r) := by
    rw [div_pow, saddle_landen]
    dsimp only [Q, Z]
    field_simp [hLne]
  have hsre : 0 < (saddleS r / L r).re := by
    obtain ⟨hb, hab⟩ := saddleS_components hr
    rw [Complex.div_re, ← add_div]
    exact div_pos (add_pos (mul_pos (hb.trans hab) hLr) (mul_pos hb hLi)) hLn
  have he := congrArg Complex.im hs
  norm_num [pow_two, Complex.mul_im, Complex.mul_re] at he
  by_contra! h
  have hpos := mul_nonneg hsre.le h
  linarith

private theorem saddle_velocity_im_pos {r : ℝ} (hr : 0 < r) :
    0 < (L r / ((r : ℂ) * saddleS r)).im := by
  rw [mul_comm (r : ℂ), ← div_div, Complex.div_ofReal_im,
    show L r / saddleS r = (saddleS r / L r)⁻¹ by rw [inv_div], Complex.inv_im]
  apply div_pos _ hr
  have h := saddle_quotient_im_neg hr
  have hne : saddleS r / L r ≠ 0 := fun he => h.ne (by simp [he])
  exact div_pos (neg_pos.mpr h) (normSq_pos.mpr hne)

private theorem hasDerivAt_saddleS {r : ℝ} (hr : 0 < r) :
    HasDerivAt saddleS (L r / ((r : ℂ) * saddleS r)) r := by
  have hs : saddlePhaseSquare r ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (saddlePhaseSquare_quadrant hr).1)
  have hn : saddleS r ≠ 0 := fun h => (saddleS_components hr).1.ne' (by simp [h])
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hp : HasDerivAt saddlePhaseSquare (2 * L r / (r : ℂ)) r := hasDerivAt_saddlePhaseSquare hr
  have h := (Complex.hasDerivAt_sqrt hs).scomp r hp
  change HasDerivAt saddleS _ r at h
  convert h using 1
  rw [smul_eq_mul, neg_div, Complex.cpow_neg]
  have hsqrt : saddlePhaseSquare r ^ (1 / 2 : ℂ) = saddleS r := by
    rw [saddleS, Complex.sqrt, one_div]
  rw [hsqrt]
  field_simp [hrc, hn]

/-- The imaginary component of the saddle increases strictly at every positive radius. -/
theorem strictMonoOn_saddleS_im :
    StrictMonoOn (fun r : ℝ => (saddleS r).im) (Ioi 0) := by
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt (fun x => (saddleS x).im)
      (L r / ((r : ℂ) * saddleS r)).im r :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_saddleS hr)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun r hr => (hd r hr).continuousAt.continuousWithinAt
  · intro r hr
    have hr₀ : 0 < r := interior_subset hr
    rw [(hd r hr₀).deriv]
    exact saddle_velocity_im_pos hr₀

/-- The monotonicity used to extend the table's endpoint bounds to radii at least one. -/
theorem monotoneOn_saddleS_im :
    MonotoneOn (fun r : ℝ => (saddleS r).im) (Ici 1) :=
  strictMonoOn_saddleS_im.monotoneOn.mono (fun _ h => zero_lt_one.trans_le h)

end DurfeeCCS.Step07
