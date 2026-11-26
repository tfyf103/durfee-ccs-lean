module

public import DurfeeCCS.Step08.NearOriginArcBasics

/-! The central arc of the near-origin contour. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Complex Set MeasureTheory

private theorem continuous_angularAverage {F : ℝ → ℝ → ℂ}
    (hf : Continuous (Function.uncurry F)) :
    Continuous (fun v => angularAverage (F v)) := by
  unfold angularAverage
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf _ _).const_mul _

def nearOriginCentralError (r u v : ℝ) : ℂ :=
  angularAverage (fun θ => exp (pairedLog r θ (verticalPoint u v)) -
    exp (nearOriginMainLog r θ (verticalPoint u v)) * (1 + nearOriginCorrection r θ (verticalPoint u v)))

def nearOriginCentralCoefficient (r u : ℝ) : ℝ :=
  let Δ := r ^ 2 / u
  let ε := 0.66 * r * u + 0.228 * r * Δ + 0.35 * r ^ 2 * u
  ε * Real.exp (Δ / 2 + ε) + (Δ ^ 2 / 8) * Real.exp (Δ / 2)

private theorem nearOrigin_vertical_exp_remainder_le {r u v : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1 / 40) (hu₀ : 0 < u) (hu₁ : u ≤ 1 / 40) (hv : |v| ≤ 4 * u) (θ : ℝ) :
    ‖exp (pairedLog r θ (verticalPoint u v)) -
      exp (nearOriginMainLog r θ (verticalPoint u v)) * (1 + nearOriginCorrection r θ (verticalPoint u v))‖ ≤
      nearOriginCentralCoefficient r u * nearOriginInnerWeight (r / u) (v / u) θ := by
  have hRe : 0 < (verticalPoint u v).re := by simpa only [verticalPoint_re] using hu₀
  have hs : ‖nearOriginCorrection r θ (verticalPoint u v)‖ ≤ (r ^ 2 / u) / 2 := by
    simpa only [verticalPoint_re] using norm_nearOriginCorrection_le r θ hRe
  have he := norm_pairedLog_sub_main_sub_correction_le θ hRe hr₀ hr₁
    (by simpa only [verticalPoint_re] using hu₁)
    (by simpa only [verticalPoint_im, verticalPoint_re] using hv)
  rw [verticalPoint_re] at he
  have h := nearOrigin_pointwise_exp_remainder hs he
  refine h.trans_eq ?_
  unfold nearOriginCentralCoefficient
  rw [← nearOrigin_innerWeight_eq hu₀]
  exact mul_comm _ _

theorem continuous_nearOriginCentralError {r u : ℝ} (hr : |r| ≤ 1) (hu : 0 < u) :
    Continuous (nearOriginCentralError r u) := by
  unfold nearOriginCentralError
  apply continuous_angularAverage
  exact ((Complex.continuous_exp.comp (continuous_pairedLog_vertical r hr hu)).sub
    ((Complex.continuous_exp.comp (continuous_nearOriginMainLog r hu)).mul
      ((continuous_nearOriginCorrection r hu).const_add 1)))

theorem norm_nearOriginCentralError_le {r u v : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1 / 40) (hu₀ : 0 < u) (hu₁ : u ≤ 1 / 40) (hv : |v| ≤ 4 * u) :
    ‖nearOriginCentralError r u v‖ ≤ nearOriginCentralCoefficient r u *
      nearOriginInnerAverage (r / u) (v / u) := by
  have hr : |r| ≤ 1 := by rw [abs_of_nonneg hr₀]; linarith
  let f (θ : ℝ) := exp (pairedLog r θ (verticalPoint u v)) -
    exp (nearOriginMainLog r θ (verticalPoint u v)) * (1 + nearOriginCorrection r θ (verticalPoint u v))
  have hP : Continuous (fun θ : ℝ => (v, θ)) := continuous_const.prodMk continuous_id
  have hL := (continuous_pairedLog_vertical r hr hu₀).comp hP
  have hL₀ := (continuous_nearOriginMainLog r hu₀).comp hP
  have hS := (continuous_nearOriginCorrection r hu₀).comp hP
  simp only [Function.comp_def] at hL hL₀ hS
  have hf : Continuous f := (Complex.continuous_exp.comp hL).sub
    ((Complex.continuous_exp.comp hL₀).mul (hS.const_add 1))
  let g := nearOriginInnerWeight (r / u) (v / u)
  let C := nearOriginCentralCoefficient r u
  have hg : Continuous g :=
    Real.continuous_exp.comp
      (((Real.continuous_cos.const_mul (2 * (v / u))).div_const (1 + (v / u) ^ 2)).const_mul (r / u))
  have hpoint (θ : ℝ) : ‖f θ‖ ≤ C * g θ := by
    exact nearOrigin_vertical_exp_remainder_le hr₀ hr₁ hu₀ hu₁ hv θ
  exact (norm_angularAverage_le f).trans
    ((angularMean_mono_on (f := fun θ => ‖f θ‖) (g := fun θ => C * g θ)
      hf.norm (hg.const_mul C) (fun θ _ => hpoint θ)).trans_eq (angularMean_const_mul C g))

/-- The first integral in (18), before the contour normalization. -/
theorem integral_norm_nearOriginCentralError_le {r u : ℝ}
    (hr₀ : 0 < r) (hr₁ : r ≤ 1 / 40) (hu₀ : 0 < u) (hu₁ : u ≤ 1 / 40) :
    (∫ v in Icc (-(4 * u)) (4 * u), ‖nearOriginCentralError r u v‖) ≤
      (15 * u * Real.exp (r / u) / (r / u)) * nearOriginCentralCoefficient r u := by
  let C := nearOriginCentralCoefficient r u
  let σ := r / u
  let g := nearOriginInnerAverage σ
  have hg : Continuous g := continuous_nearOriginInnerAverage σ
  have hCg : Continuous (fun v : ℝ => C * g (v / u)) :=
    (hg.comp (continuous_id.div_const u)).const_mul C
  have hC : 0 ≤ C := by unfold C nearOriginCentralCoefficient; positivity
  have hr : |r| ≤ 1 := by rw [abs_of_pos hr₀]; linarith
  have hi : -(4 * u) ≤ 4 * u := by linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hi]
  calc
    _ ≤ ∫ v in -(4 * u)..(4 * u), C * g (v / u) := by
      apply intervalIntegral.integral_mono_on hi
        ((continuous_nearOriginCentralError hr hu₀).norm.intervalIntegrable _ _)
        (hCg.intervalIntegrable _ _)
      intro v hv
      exact norm_nearOriginCentralError_le hr₀.le hr₁ hu₀ hu₁ (abs_le.mpr hv)
    _ = C * (u * ∫ η in (-4 : ℝ)..4, g η) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div _ hu₀.ne']
      rw [show -(4 * u) / u = -4 by field_simp, show 4 * u / u = 4 by field_simp]
      simp [smul_eq_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (nearOrigin_inner_average_integral_le (show 0 < σ by positivity))
          hu₀.le) hC
      convert h using 1
      ring

end DurfeeCCS.Step08
