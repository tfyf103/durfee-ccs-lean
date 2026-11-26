module

public import DurfeeCCS.Step08.NearOriginArcBasics
public import DurfeeCCS.Step08.NearOriginModelIntegral
public import DurfeeCCS.Step08.VerticalTail

/-! The two infinite tails of the near-origin comparison contour. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex Set MeasureTheory

theorem norm_mul_le_weighted_sq (a b : ℂ) {w : ℝ} (hw : 0 < w) :
    ‖a * b‖ ≤ (w * ‖a‖ ^ 2 + w⁻¹ * ‖b‖ ^ 2) / 2 := by
  rw [norm_mul]
  refine le_of_mul_le_mul_right ?_ hw
  rw [show ((w * ‖a‖ ^ 2 + w⁻¹ * ‖b‖ ^ 2) / 2) * w =
      ((w * ‖a‖) ^ 2 + ‖b‖ ^ 2) / 2 by field_simp [hw.ne']]
  nlinarith [sq_nonneg (w * ‖a‖ - ‖b‖)]

theorem angularMean_add_continuous {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    angularMean (fun t => f t + g t) = angularMean f + angularMean g := by
  simp only [angularMean, intervalIntegral.integral_add (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), mul_add]

theorem angularMean_norm_mul_le_weighted_sq {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) {w : ℝ} (hw : 0 < w) :
    angularMean (fun θ => ‖f θ * g θ‖) ≤
      (w * angularMean (fun θ => ‖f θ‖ ^ 2) + w⁻¹ * angularMean (fun θ => ‖g θ‖ ^ 2)) / 2 := by
  have hR : Continuous (fun θ => (2 : ℝ)⁻¹ * (w * ‖f θ‖ ^ 2 + w⁻¹ * ‖g θ‖ ^ 2)) :=
    (((hf.norm.pow 2).const_mul w).add ((hg.norm.pow 2).const_mul w⁻¹)).const_mul _
  refine (angularMean_mono_on (hf.mul hg).norm hR (fun θ _ => ?_)).trans_eq ?_
  · rw [← div_eq_inv_mul]
    exact norm_mul_le_weighted_sq (f θ) (g θ) hw
  · have hsum := angularMean_add_continuous
      (f := fun θ => w * ‖f θ‖^2) (g := fun θ => w⁻¹ * ‖g θ‖^2)
      ((hf.norm.pow 2).const_mul _) ((hg.norm.pow 2).const_mul _)
    rw [angularMean_const_mul, hsum, angularMean_const_mul, angularMean_const_mul]
    ring

theorem norm_angularAverage_nearOriginBase_le {r u v : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hv : 4 * u ≤ |v|) :
    ‖angularAverage (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) - 1)‖ ≤
      Real.exp (r / u / 2) * r ^ 2 / (u ^ 2 + v ^ 2) := by
  have hf : Continuous (fun θ => nearOriginMainLog r θ (verticalPoint u v)) :=
    (continuous_nearOriginMainLog r hu).comp (continuous_const.prodMk continuous_id)
  have h := norm_angularAverage_exp_sub_one_le hf (angularAverage_nearOriginMainLog r (verticalPoint u v))
    (show 0 ≤ r / u / 2 by positivity) (fun θ _ => nearOriginMainLog_re_vertical_le hr hu hv θ)
  rw [angularMean_nearOriginMainLog_sq] at h
  refine h.trans_eq ?_
  ring

theorem norm_angularAverage_nearOriginCorrection_le {r u v : ℝ}
    (hr : 0 < r) (hu : 0 < u) (hv : 4 * u ≤ |v|) :
    ‖angularAverage (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) *
      nearOriginCorrection r θ (verticalPoint u v))‖ ≤
      Real.exp (r / u / 2) * r ^ 3 / (2 * (u ^ 2 + v ^ 2)) := by
  let f := fun θ => nearOriginMainLog r θ (verticalPoint u v)
  let g := fun θ => nearOriginCorrection r θ (verticalPoint u v)
  have hf : Continuous f :=
    (continuous_nearOriginMainLog r hu).comp (continuous_const.prodMk continuous_id)
  have hg : Continuous g :=
    (continuous_nearOriginCorrection r hu).comp (continuous_const.prodMk continuous_id)
  have he : Continuous (fun θ => (exp (f θ) - 1) * g θ) :=
    ((Complex.continuous_exp.comp hf).sub continuous_const).mul hg
  have hzero : angularAverage g = 0 := angularAverage_nearOriginCorrection r (verticalPoint u v)
  have heq : angularAverage (fun θ => exp (f θ) * g θ) =
      angularAverage (fun θ => (exp (f θ) - 1) * g θ) := by
    have h (θ : ℝ) : exp (f θ) * g θ = (exp (f θ) - 1) * g θ + g θ := by ring
    simp_rw [h]
    rw [angularAverage_add (he.intervalIntegrable _ _) (hg.intervalIntegrable _ _), hzero, add_zero]
  change ‖angularAverage (fun θ => exp (f θ) * g θ)‖ ≤ _
  rw [heq]
  refine (norm_angularAverage_le _).trans ?_
  have hdom : angularMean (fun θ => ‖(exp (f θ) - 1) * g θ‖) ≤
      Real.exp (r / u / 2) * angularMean (fun θ => ‖f θ * g θ‖) := by
    rw [← angularMean_const_mul]
    apply angularMean_mono_on he.norm ((hf.mul hg).norm.const_mul _)
    intro θ _
    change ‖(exp (f θ) - 1) * g θ‖ ≤ Real.exp (r / u / 2) * ‖f θ * g θ‖
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (‖f θ‖ * Real.exp (max 0 (f θ).re)) * ‖g θ‖ :=
        mul_le_mul_of_nonneg_right (norm_exp_sub_one_le _) (norm_nonneg _)
      _ ≤ (‖f θ‖ * Real.exp (r / u / 2)) * ‖g θ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (max_le (by positivity) (nearOriginMainLog_re_vertical_le hr.le hu hv θ)))
            (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  rw [mul_div_assoc]
  refine hdom.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))
  have h := angularMean_norm_mul_le_weighted_sq hf hg (show 0 < r / 4 by positivity)
  change angularMean (fun θ => ‖f θ * g θ‖) ≤
    ((r / 4) * angularMean (fun θ => ‖nearOriginMainLog r θ (verticalPoint u v)‖ ^ 2) +
      (r / 4)⁻¹ * angularMean (fun θ => ‖nearOriginCorrection r θ (verticalPoint u v)‖ ^ 2)) / 2 at h
  rw [angularMean_nearOriginMainLog_sq, angularMean_nearOriginCorrection_sq] at h
  have hden : 0 < u ^ 2 + v ^ 2 := by positivity
  refine h.trans_eq ?_
  field_simp [hr.ne', hden.ne']
  ring

theorem integral_cauchy_density_abs_gt_le {u c : ℝ} (hu : 0 < u) (hc : 0 < c) :
    (∫ v in {v : ℝ | c < |v|}, (u ^ 2 + v ^ 2)⁻¹) ≤ 2 / c := by
  have heq : {v : ℝ | c < |v|} = (Icc (-c) c)ᶜ := by
    ext v
    change c < |v| ↔ ¬(-c ≤ v ∧ v ≤ c)
    simp only [lt_abs, not_and_or, not_le]
    constructor
    · rintro (hv | hv)
      · exact Or.inr hv
      · exact Or.inl (by linarith)
    · rintro (hv | hv)
      · exact Or.inr (by linarith)
      · exact Or.inl hv
  rw [heq]
  exact integral_cauchy_density_tail_le hu hc

/-- The third term of (18), before multiplying by the contour weight. -/
theorem integral_norm_nearOriginBase_outer_le {r u : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hup : 4 * u ≤ Real.pi) :
    (∫ v in {v : ℝ | Real.pi < |v|},
      ‖angularAverage (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) - 1)‖) ≤
      2 * Real.exp (r / u / 2) * r ^ 2 / Real.pi := by
  let C := Real.exp (r / u / 2) * r ^ 2
  let f (v : ℝ) := angularAverage (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) - 1)
  let s := {v : ℝ | Real.pi < |v|}
  have hf : Integrable f := by
    simpa only [f, nearOriginAngleAverage, angularAverage, ofReal_zero, zero_mul, exp_zero, one_mul] using
      integrable_nearOriginAngularBase hu r 0
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (continuous_abs.measurable)
  have hg := (integrable_cauchy_density hu).const_mul C
  change (∫ v in s, ‖f v‖) ≤ _
  calc
    _ ≤ ∫ v in s, C * (u ^ 2 + v ^ 2)⁻¹ := by
      apply setIntegral_mono_on hf.norm.integrableOn hg.integrableOn hs
      intro v hv
      simpa only [C, f, div_eq_mul_inv] using
        norm_angularAverage_nearOriginBase_le hr hu (hup.trans (le_of_lt hv))
    _ ≤ C * (2 / Real.pi) := by
      rw [MeasureTheory.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_cauchy_density_abs_gt_le hu Real.pi_pos) (by
        dsimp only [C]
        positivity)
    _ = _ := by dsimp only [C]; ring

/-- The fourth term of (18), before multiplying by the contour weight. -/
theorem integral_norm_nearOriginCorrection_outer_le {r u : ℝ}
    (hr : 0 < r) (hu : 0 < u) :
    (∫ v in {v : ℝ | 4 * u < |v|}, ‖angularAverage
      (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) *
        nearOriginCorrection r θ (verticalPoint u v))‖) ≤
      Real.pi * Real.exp (r / u / 2) * r ^ 3 / (2 * u) := by
  let C := Real.exp (r / u / 2) * r ^ 3 / 2
  let f (v : ℝ) := angularAverage (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) *
    nearOriginCorrection r θ (verticalPoint u v))
  let s := {v : ℝ | 4 * u < |v|}
  have hf : Integrable f := by
    simpa only [f, nearOriginAngleAverage, angularAverage, ofReal_zero, zero_mul, exp_zero, one_mul] using
      integrable_nearOriginAngularCorrection hu r 0
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (continuous_abs.measurable)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hg := (integrable_cauchy_density hu).const_mul C
  change (∫ v in s, ‖f v‖) ≤ _
  calc
    _ ≤ ∫ v in s, C * (u ^ 2 + v ^ 2)⁻¹ := by
      apply setIntegral_mono_on hf.norm.integrableOn hg.integrableOn hs
      intro v hv
      refine (norm_angularAverage_nearOriginCorrection_le hr hu (le_of_lt hv)).trans_eq ?_
      dsimp only [C]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ ∫ v : ℝ, C * (u ^ 2 + v ^ 2)⁻¹ :=
      setIntegral_le_integral hg (ae_of_all _ fun v => mul_nonneg hC (by positivity))
    _ = _ := by
      rw [MeasureTheory.integral_const_mul, integral_cauchy_density hu]
      dsimp only [C]
      ring

end DurfeeCCS.Step08
