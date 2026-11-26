module

public import DurfeeCCS.Step06.Branches
public import DurfeeCCS.Step06.Dilog
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The principal square-root, amplitude and phase used in (6)–(8). -/

@[expose] public section

namespace DurfeeCCS.Step06

open Complex Set MeasureTheory

/-- The symmetric dilogarithm combination in (6). -/
noncomputable def saddleG (r θ : ℝ) : ℂ :=
  -principalDilog (-(r : ℂ) * I * Complex.exp (θ * I)) -
    principalDilog (-(r : ℂ) * I * Complex.exp (-(θ : ℂ) * I))

/-- The argument of the principal square root in (7). -/
noncomputable def saddlePhaseSquare (r : ℝ) : ℂ :=
  -2 * principalDilog (-(r : ℂ) * I)

noncomputable def saddleS (r : ℝ) : ℂ := (saddlePhaseSquare r).sqrt

theorem saddleS_sq (r : ℝ) : saddleS r ^ 2 = saddlePhaseSquare r :=
  principalSqrt_sq _

theorem saddleS_real_imag (r : ℝ) :
    (↑(saddleS r).re : ℂ) + ↑(saddleS r).im * I = saddleS r :=
  Complex.re_add_im _

theorem saddleG_zero (r : ℝ) : saddleG r 0 = saddleS r ^ 2 := by
  rw [saddleS_sq]
  simp [saddleG, saddlePhaseSquare]
  ring

private theorem neg_real_mul_I_mem_dilogCut (r : ℝ) : -(r : ℂ) * I ∈ dilogCut := by
  apply mem_dilogCut_iff.mpr
  left
  simp

theorem continuous_saddlePhaseSquare : Continuous saddlePhaseSquare := by
  have h := continuousOn_principalDilog.comp_continuous
    (show Continuous (fun r : ℝ => -(r : ℂ) * I) by fun_prop)
    neg_real_mul_I_mem_dilogCut
  exact continuous_const.mul h

private theorem kernel_components_neg_real_mul_I (r t : ℝ) (h : 0 < t) :
    (dilogKernel (-(r : ℂ) * I) t).re = -Real.log ‖1 + ((t * r : ℝ) : ℂ) * I‖ / t ∧
      (dilogKernel (-(r : ℂ) * I) t).im = -(1 + ((t * r : ℝ) : ℂ) * I).arg / t := by
  have he : 1 - (t : ℂ) * (-(r : ℂ) * I) = 1 + ((t * r : ℝ) : ℂ) * I := by
    push_cast
    ring
  simp only [dilogKernel, ite_eq_right h.ne', he]
  simp [Complex.log_re, Complex.log_im]

/-- The square-root argument lies in the open first quadrant for every positive radius. -/
theorem saddlePhaseSquare_quadrant {r : ℝ} (hr : 0 < r) :
    0 < (saddlePhaseSquare r).re ∧ 0 < (saddlePhaseSquare r).im := by
  let f := dilogKernel (-(r : ℂ) * I)
  have hf : IntervalIntegrable f volume 0 1 :=
    intervalIntegrable_dilogKernel (neg_real_mul_I_mem_dilogCut r)
  have hfc : ContinuousOn f (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le zero_le_one, f] using
      (continuousOn_dilogKernel (neg_real_mul_I_mem_dilogCut r))
  have hp (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      0 < -(f t).re ∧ 0 < -(f t).im := by
    have ⟨hRe, hIm⟩ := kernel_components_neg_real_mul_I r t ht.1
    change 0 < -(dilogKernel (-(r : ℂ) * I) t).re ∧
      0 < -(dilogKernel (-(r : ℂ) * I) t).im
    rw [hRe, hIm, ← neg_div, ← neg_div, neg_neg, neg_neg]
    constructor
    · apply div_pos (Real.log_pos ?_) ht.1
      rw [Complex.norm_eq_sqrt_sq_add_sq, Real.lt_sqrt (by norm_num)]
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self, add_zero, zero_add]
      have htr := mul_pos ht.1 hr
      nlinarith [sq_pos_of_pos htr]
    · apply div_pos _ ht.1
      have htr : 0 < (1 + ((t * r : ℝ) : ℂ) * I).im := by
        simpa [Complex.mul_im] using mul_pos ht.1 hr
      refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr htr.le) (Ne.symm ?_)
      exact fun hzero => htr.ne' (Complex.arg_eq_zero_iff.mp hzero).2
  have hrInt : 0 < ∫ t in (0 : ℝ)..1, -(f t).re :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (((by fun_prop : Continuous (fun z : ℂ => -z.re)).comp_continuousOn hfc).intervalIntegrable)
      (fun t ht => (hp t ht).1) zero_lt_one
  have hiInt : 0 < ∫ t in (0 : ℝ)..1, -(f t).im :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (((by fun_prop : Continuous (fun z : ℂ => -z.im)).comp_continuousOn hfc).intervalIntegrable)
      (fun t ht => (hp t ht).2) zero_lt_one
  change 0 < (-2 * ∫ t in (0 : ℝ)..1, f t).re ∧ 0 < (-2 * ∫ t in (0 : ℝ)..1, f t).im
  have hre : (∫ t in (0 : ℝ)..1, (f t).re) = (∫ t in (0 : ℝ)..1, f t).re :=
    intervalIntegral.intervalIntegral_re hf
  have him : (∫ t in (0 : ℝ)..1, (f t).im) = (∫ t in (0 : ℝ)..1, f t).im :=
    intervalIntegral.intervalIntegral_im hf
  rw [intervalIntegral.integral_neg, hre] at hrInt
  rw [intervalIntegral.integral_neg, him] at hiInt
  norm_num [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im]
  exact ⟨by linarith, by linarith⟩

/-- The amplitude in (8), with positive real fourth root. -/
noncomputable def saddleAmplitude (n : ℕ) (r : ℝ) : ℝ :=
  ‖saddleS r‖ * (1 + r ^ 2) ^ (1 / 4 : ℝ) *
    Real.exp (2 * (saddleS r).re * Real.sqrt n) / (2 * Real.pi * n * Real.sqrt r)

/-- The real phase in (8), with principal argument. -/
noncomputable def saddlePhase (n : ℕ) (r : ℝ) : ℝ :=
  2 * (saddleS r).im * Real.sqrt n + (saddleS r).arg - Real.pi / 4 + Real.arctan r / 2

theorem saddleAmplitude_pos {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    0 < saddleAmplitude n r := by
  have hs : saddleS r ≠ 0 := by
    intro h
    have hh := saddleS_sq r
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hh
    have hp := (saddlePhaseSquare_quadrant hr).1
    rw [← hh, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  unfold saddleAmplitude
  have hpow : 0 < (1 + r ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  positivity

theorem continuousOn_saddleS : ContinuousOn saddleS (Ioi (0 : ℝ)) := by
  apply Complex.continuousOn_sqrt.comp continuous_saddlePhaseSquare.continuousOn
  intro r hr
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (saddlePhaseSquare_quadrant hr).1)

theorem saddleS_arg {r : ℝ} (hr : 0 < r) :
    0 < (saddleS r).arg ∧ (saddleS r).arg < Real.pi / 4 := by
  obtain ⟨hre, him⟩ := saddlePhaseSquare_quadrant hr
  have hz : saddlePhaseSquare r ≠ 0 := by
    intro h
    simp [h] at hre
  rw [saddleS, principalSqrt_arg hz]
  have h₁ : 0 < (saddlePhaseSquare r).arg := by
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le) (Ne.symm ?_)
    exact fun hzero => him.ne' (Complex.arg_eq_zero_iff.mp hzero).2
  have h₂ : (saddlePhaseSquare r).arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  exact ⟨by linarith, by linarith⟩

theorem saddleS_components {r : ℝ} (hr : 0 < r) :
    0 < (saddleS r).im ∧ (saddleS r).im < (saddleS r).re := by
  obtain ⟨harg, hquarter⟩ := saddleS_arg hr
  have hπ := Real.pi_pos
  have hnz : saddleS r ≠ 0 := by
    intro hz
    simp [hz] at harg
  have hb : 0 < (saddleS r).im := by
    have hs := Real.sin_pos_of_pos_of_lt_pi harg (by linarith)
    rw [Complex.sin_arg] at hs
    exact (div_pos_iff_of_pos_right (norm_pos_iff.mpr hnz)).mp hs
  have ha : 0 < (saddleS r).re := by
    have hc := Real.cos_pos_of_mem_Ioo
      (show (saddleS r).arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith, by linarith⟩)
    rw [Complex.cos_arg hnz] at hc
    exact (div_pos_iff_of_pos_right (norm_pos_iff.mpr hnz)).mp hc
  have hsq : 0 < (saddleS r).re ^ 2 - (saddleS r).im ^ 2 := by
    have hz := (saddlePhaseSquare_quadrant hr).1
    rw [← saddleS_sq r, pow_two, Complex.mul_re, ← pow_two, ← pow_two] at hz
    exact hz
  exact ⟨hb, by nlinarith [mul_nonneg ha.le hb.le]⟩

theorem continuousOn_saddlePhase (n : ℕ) : ContinuousOn (saddlePhase n) (Ioi (0 : ℝ)) := by
  have hb := Complex.continuous_im.comp_continuousOn continuousOn_saddleS
  have ha : ContinuousOn (fun r => (saddleS r).arg) (Ioi (0 : ℝ)) := by
    apply Complex.continuousOn_arg.comp continuousOn_saddleS
    intro r hr
    apply Complex.mem_slitPlane_iff.mpr
    right
    intro h
    exact (saddleS_components hr).1.ne' h
  unfold saddlePhase
  exact (continuousOn_const.mul hb |>.mul continuousOn_const |>.add ha |>.sub
    continuousOn_const).add (Real.continuous_arctan.continuousOn.div_const _)

theorem continuousOn_saddleAmplitude {n : ℕ} (hn : 0 < n) :
    ContinuousOn (saddleAmplitude n) (Ioi (0 : ℝ)) := by
  unfold saddleAmplitude
  apply ContinuousOn.div
  · have hroot : ContinuousOn (fun r : ℝ => (1 + r ^ 2) ^ (1 / 4 : ℝ)) (Ioi 0) :=
      (show ContinuousOn (fun r : ℝ => 1 + r ^ 2) (Ioi 0) by fun_prop).rpow_const
        (fun _ _ => Or.inr (by norm_num))
    have ha := Complex.continuous_re.comp_continuousOn continuousOn_saddleS
    exact (continuousOn_saddleS.norm.mul hroot).mul
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul ha |>.mul continuousOn_const))
  · fun_prop
  · intro r hr
    exact (show 0 < 2 * Real.pi * (n : ℝ) * Real.sqrt r by
      have hr' : 0 < r := hr
      positivity).ne'

end DurfeeCCS.Step06
