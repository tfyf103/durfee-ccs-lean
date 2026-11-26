module

public import DurfeeCCS.Step09.MidMajorContinuity
public import DurfeeCCS.Step09.MidMajorLocal
public import DurfeeCCS.Step09.MidMajorWeight
public import DurfeeCCS.Step09.MidPhaseShape

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Passing from the pointwise phase bounds to central and tail integral estimates. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

def midMajorPrefactor (n : ℕ) (r : ℝ) : ℝ := midU n r / (4 * Real.pi ^ 2)

def midMajorBaseExponent (n : ℕ) (r η : ℝ) : ℝ :=
  2 * midOmega n r - midOmega n r * midMajorGap (midSlope r) η

def midMajorChiIntegral (n : ℕ) (r η : ℝ) : ℂ := ∫ χ : ℝ, midIntegrand n r 0 η χ

def midMajorQuadraticIntegral (n : ℕ) (r η : ℝ) : ℂ :=
  ∫ χ : ℝ, exp (midGaussianExponent n r η χ)

def midMajorQuadraticContribution (n : ℕ) (r l h : ℝ) : ℂ :=
  (midMajorPrefactor n r : ℂ) * ∫ η in l..h, midMajorQuadraticIntegral n r η

theorem midMajor_damping_pos {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    0 < midDamping n r η := by
  have := saddleU_pos hn hr
  unfold midDamping
  positivity

theorem midMajor_inv_damping {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    (midDamping n r η)⁻¹ = midU n r * (1 + η ^ 2) * (1 + r⁻¹ ^ 2) := by
  have hu := saddleU_pos hn hr
  unfold midDamping
  field_simp
  ring

theorem midMajor_weight_identity {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    midMajorPrefactor n r *
      (Real.exp (midMajorBaseExponent n r η) * Real.sqrt (Real.pi / midDamping n r η)) =
        saddleAmplitude n r / 2 * midMajorWeight (midOmega n r) r (midSlope r) η := by
  have hs := midMajor_weight_eq hn hr η
  dsimp only at hs
  have he : (1 / midU n r) * r ^ 2 / ((1 + r ^ 2) * (1 + η ^ 2)) = midDamping n r η := by
    unfold midDamping
    have hu := saddleU_pos hn hr
    field_simp
  rw [he] at hs
  exact hs

private theorem continuous_real_mass {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    Continuous (fun η : ℝ => Real.exp (midMajorBaseExponent n r η) *
        Real.sqrt (Real.pi / midDamping n r η)) := by
  simp only [div_eq_mul_inv, midMajor_inv_damping hn hr]
  unfold midMajorBaseExponent midMajorGap
  fun_prop (disch := intro _; positivity)

theorem continuous_midGaussianExponent {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    Continuous (fun x : ℝ × ℝ => midGaussianExponent n r x.1 x.2) := by
  let ζ (x : ℝ × ℝ) := midEtaPoint n r x.1
  have hζ : Continuous ζ := (continuous_midEtaPoint n r).comp continuous_fst
  have hne (x : ℝ × ℝ) : ζ x ≠ 0 := midEtaPoint_ne_zero hn hr x.1
  change Continuous (fun x : ℝ × ℝ =>
    (n : ℂ) * ζ x + (saddleS r ^ 2 - midCurvature r * (x.2 : ℂ) ^ 2) / ζ x)
  fun_prop (disch := exact hne)

theorem midMajor_inner_norm_le {F : ℝ → ℂ} {C A T : ℝ}
    (hA : 0 < A) (hF : AEStronglyMeasurable F volume)
    (hbound : ∀ x : ℝ, ‖F x‖ ≤ C * (Real.exp T * Real.exp (-A * x ^ 2))) :
    ‖∫ x : ℝ, F x‖ ≤ C * (Real.exp T * Real.sqrt (Real.pi / A)) := by
  let f (x : ℝ) := Real.exp (-A * x ^ 2)
  have hf : Integrable f := integrable_exp_neg_mul_sq hA
  have hg : Integrable (fun x => C * (Real.exp T * f x)) := (hf.const_mul _).const_mul _
  have hFi : Integrable F := hg.mono' hF (ae_of_all _ hbound)
  refine (norm_integral_le_integral_norm F).trans (le_trans
    (integral_mono hFi.norm hg hbound) ?_)
  simp only [integral_const_mul, f, integral_gaussian A, le_refl]

theorem midMajor_chi_integral_norm_le {n : ℕ} (hn : 0 < n) {r η C : ℝ} (hr : 1 ≤ r)
    (hη : 0 ≤ η) (_hC : 0 ≤ C)
    (hB : ∀ χ : ℝ, ‖midMultiplier r 0 (midEtaPoint n r η) χ‖ ≤ C) :
    ‖midMajorChiIntegral n r η‖ ≤ C * (Real.exp (midMajorBaseExponent n r η) *
                                 Real.sqrt (Real.pi / midDamping n r η)) := by
  have hrp : 0 < r := by linarith
  have hcont := (continuous_midIntegrand hn hr 0).comp
    (show Continuous (fun x : ℝ => (η,x)) from continuous_const.prodMk continuous_id)
  apply midMajor_inner_norm_le (F := midIntegrand n r 0 η) (midMajor_damping_pos hn hrp η)
    hcont.aestronglyMeasurable
  intro χ
  unfold midIntegrand
  dsimp only
  rw [norm_mul, Complex.norm_exp]
  rw [mul_comm C, ← Real.exp_add]
  apply mul_le_mul (Real.exp_le_exp.mpr ?_) (hB χ) (norm_nonneg _) (Real.exp_pos _).le
  have h := re_mid_phase_exponent_zero_le hn hr hη χ
  simpa only [midMajorBaseExponent, midMajorGap, mul_div_assoc, sub_eq_add_neg, neg_mul] using h

theorem midMajor_quadratic_integral_norm_le {n : ℕ} (hn : 0 < n) {r η : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) :
    ‖midMajorQuadraticIntegral n r η‖ ≤ Real.exp (midMajorBaseExponent n r η) *
                                 Real.sqrt (Real.pi / midDamping n r η) := by
  have hcont := (Complex.continuous_exp.comp (continuous_midGaussianExponent hn hr)).comp
    (show Continuous (fun x : ℝ => (η,x)) from continuous_const.prodMk continuous_id)
  unfold midMajorQuadraticIntegral
  apply (midMajor_inner_norm_le (F := fun χ => exp (midGaussianExponent n r η χ))
    (C := 1) (midMajor_damping_pos hn hr η) hcont.aestronglyMeasurable ?_).trans_eq
    (one_mul _)
  intro χ
  rw [one_mul, Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := re_midGaussianExponent_le hn hr hη χ
  simpa only [midMajorBaseExponent, midMajorGap, mul_div_assoc, sub_eq_add_neg, neg_mul] using h

private theorem intervalIntegrable_of_gaussian_majorant {f : ℝ → ℂ}
    {n : ℕ} (hn : 0 < n) {r l h C : ℝ} (hr : 0 < r) (hlh : l ≤ h)
    (hf : StronglyMeasurable f)
    (hbound : ∀ η ∈ Icc l h, ‖f η‖ ≤ C * (Real.exp (midMajorBaseExponent n r η) *
                                 Real.sqrt (Real.pi / midDamping n r η))) :
    IntervalIntegrable f volume l h := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlh]
  let b (η : ℝ) := C * (Real.exp (midMajorBaseExponent n r η) *
                                 Real.sqrt (Real.pi / midDamping n r η))
  have hb : Continuous b := continuous_const.mul (continuous_real_mass hn hr)
  change Integrable f (volume.restrict (Icc l h))
  apply (hb.integrableOn_Icc : IntegrableOn b (Icc l h) volume).mono' hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with η hη
  exact hbound η hη

theorem intervalIntegrable_midMajorChiIntegral {n : ℕ} (hn : 0 < n)
    {r l h C : ℝ} (hr : 1 ≤ r) (hl : 0 ≤ l) (hlh : l ≤ h)
    (hC : 0 ≤ C) (hB : ∀ η ∈ Icc l h, ∀ χ : ℝ, ‖midMultiplier r 0 (midEtaPoint n r η) χ‖ ≤ C) :
    IntervalIntegrable (midMajorChiIntegral n r) volume l h := by
  apply intervalIntegrable_of_gaussian_majorant (f := midMajorChiIntegral n r) (C := C)
    hn (by linarith : 0 < r) hlh
    (continuous_midIntegrand hn hr 0).stronglyMeasurable.integral_prod_right'
  intro η hη
  exact midMajor_chi_integral_norm_le hn hr (hl.trans hη.1) hC (hB η hη)

theorem intervalIntegrable_midMajorQuadraticIntegral {n : ℕ} (hn : 0 < n)
    {r l h : ℝ} (hr : 0 < r) (hl : 0 ≤ l) (hlh : l ≤ h) :
    IntervalIntegrable (midMajorQuadraticIntegral n r) volume l h := by
  apply intervalIntegrable_of_gaussian_majorant (f := midMajorQuadraticIntegral n r) (C := 1) hn hr hlh
    (Complex.continuous_exp.comp (continuous_midGaussianExponent hn hr)).stronglyMeasurable.integral_prod_right'
  intro η hη
  simpa only [one_mul] using midMajor_quadratic_integral_norm_le hn hr (hl.trans hη.1)

/-- The comparison of the two inner integrals before replacing the radius by its row data. -/
theorem midMajor_inner_relative_error {n : ℕ} (hn : 0 < n) {r η h z L κ : ℝ}
    (hr : 1 ≤ r) (hη : 0 ≤ η) (hh : 0 < h) (hz : 0 < z)
    (hzA : z ≤ midDamping n r η * h ^ 2) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hB : ∀ χ : ℝ, ‖midMultiplier r 0 (midEtaPoint n r η) χ‖ ≤ 10.9)
    (hnear : ∀ χ ∈ Icc (-h) h, ‖midMultiplier r 0 (midEtaPoint n r η) χ - 1‖ ≤ Real.exp L - 1)
    (hphase : ∀ χ ∈ Icc (-h) h, ‖midPhase r 0 χ - (saddleS r ^ 2 - midCurvature r * (χ : ℂ) ^ 2)‖
      ≤ κ / r * χ ^ 4) :
    ‖midMajorChiIntegral n r η - midMajorQuadraticIntegral n r η‖ ≤
      Real.exp (midMajorBaseExponent n r η) * Real.sqrt (Real.pi / midDamping n r η) *
        ((119 / 10) * (Real.exp (-z) / Real.sqrt (Real.pi * z)) +
          (Real.exp L - 1) + 3 * (κ / r / ‖midEtaPoint n r η‖) / (4 * midDamping n r η ^ 2)) := by
  let ζ := midEtaPoint n r η
  let P (χ : ℝ) := (n : ℂ) * ζ + midPhase r 0 χ / ζ
  let Q (χ : ℝ) := midGaussianExponent n r η χ
  let B (χ : ℝ) := midMultiplier r 0 ζ χ
  have hr' : 0 < r := by linarith
  have hP : Continuous P :=
    continuous_const.add ((continuous_midPhase hr 0).div_const ζ)
  have hQ : Continuous Q := (continuous_midGaussianExponent hn hr').comp
    (show Continuous (fun x : ℝ => (η,x)) from continuous_const.prodMk continuous_id)
  have hB' : Continuous B := by
    have h := (continuous_midIntegrand hn hr 0).comp
      (show Continuous (fun x : ℝ => (η,x)) from continuous_const.prodMk continuous_id)
    change Continuous (fun χ => exp (P χ) * B χ) at h
    have hg : (fun χ => exp (P χ) * B χ / exp (P χ)) = B := by
      ext χ
      rw [mul_comm, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)]
    rw [← hg]
    exact h.div (Complex.continuous_exp.comp hP) (fun χ => Complex.exp_ne_zero _)
  apply midMajor_inner_error (midMajor_damping_pos hn hr' η) hh hz hzA hL (by positivity) hP hQ hB'
  · intro χ
    have h := re_mid_phase_exponent_zero_le hn hr hη χ
    simpa only [P, ζ, midMajorBaseExponent, midMajorGap, mul_div_assoc] using h
  · intro χ
    have h := re_midGaussianExponent_le hn hr' hη χ
    simpa only [Q, midMajorBaseExponent, midMajorGap, mul_div_assoc] using h
  · exact hB
  · exact hnear
  · intro χ hχ
    have he : P χ - Q χ = (midPhase r 0 χ - (saddleS r ^ 2 - midCurvature r * (χ : ℂ)^2)) / ζ := by
      unfold P Q midGaussianExponent ζ
      dsimp only
      rw [sub_div]
      ring
    rw [he, norm_div]
    exact (div_le_div_of_nonneg_right (hphase χ hχ) (norm_nonneg _)).trans_eq (by ring)

end DurfeeCCS.Step09
