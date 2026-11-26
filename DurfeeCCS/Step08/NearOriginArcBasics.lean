module

public import DurfeeCCS.Step08.NearOriginGaussian
public import DurfeeCCS.Step08.LogArcMean
public import DurfeeCCS.Step08.AngularErrors

/-! Angular means and elementary estimates for the near-origin contour. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex Set MeasureTheory

theorem continuous_verticalPoint (u : ℝ) : Continuous (verticalPoint u) := by
  unfold verticalPoint
  fun_prop

theorem continuous_nearOriginMainLog (r : ℝ) {u : ℝ} (hu : 0 < u) :
    Continuous (fun p : ℝ × ℝ => nearOriginMainLog r p.2 (verticalPoint u p.1)) := by
  unfold nearOriginMainLog
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ => 2 * I * (r : ℂ) * (Real.cos p.2 : ℂ))).div
    ((continuous_verticalPoint u).comp continuous_fst) (fun p => verticalPoint_ne_zero hu p.1)

theorem continuous_nearOriginCorrection (r : ℝ) {u : ℝ} (hu : 0 < u) :
    Continuous (fun p : ℝ × ℝ => nearOriginCorrection r p.2 (verticalPoint u p.1)) := by
  unfold nearOriginCorrection
  exact (by fun_prop :
    Continuous (fun p : ℝ × ℝ => (r : ℂ) ^ 2 * (Real.cos (2 * p.2) : ℂ))).div
    (((continuous_verticalPoint u).comp continuous_fst).const_mul _)
    (fun p => mul_ne_zero two_ne_zero (verticalPoint_ne_zero hu p.1))

theorem nearOriginMainLog_re_vertical (r θ u v : ℝ) :
    (nearOriginMainLog r θ (verticalPoint u v)).re =
      2 * r * v * Real.cos θ / (u ^ 2 + v ^ 2) := by
  rw [nearOriginMainLog, Complex.div_re, Complex.normSq_eq_norm_sq, norm_verticalPoint_sq,
    verticalPoint_re, verticalPoint_im]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  ring

theorem nearOriginMainLog_re_vertical_le {r u v : ℝ} (hr : 0 ≤ r) (hu : 0 < u)
    (hv : 4 * u ≤ |v|) (θ : ℝ) :
    (nearOriginMainLog r θ (verticalPoint u v)).re ≤ (r / u) / 2 := by
  have hd : 0 < u ^ 2 + v ^ 2 := by positivity
  rw [nearOriginMainLog_re_vertical]
  apply (div_le_iff₀ hd).2
  have hc : v * Real.cos θ ≤ |v| := by
    calc
      _ ≤ |v * Real.cos θ| := le_abs_self _
      _ = |v| * |Real.cos θ| := abs_mul _ _
      _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hquad : 4 * u * |v| ≤ u ^ 2 + v ^ 2 := by
    rw [← sq_abs v]
    nlinarith [mul_nonneg (sub_nonneg.mpr hv) (abs_nonneg v), sq_nonneg u]
  calc
    _ = 2 * r * (v * Real.cos θ) := by ring
    _ ≤ 2 * r * |v| := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (r / u / 2) * (4 * u * |v|) := by field_simp [hu.ne']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hquad (by positivity)

theorem nearOrigin_innerWeight_eq {r u : ℝ} (hu : 0 < u) (v θ : ℝ) :
    Real.exp (nearOriginMainLog r θ (verticalPoint u v)).re =
      nearOriginInnerWeight (r / u) (v / u) θ := by
  rw [nearOriginMainLog_re_vertical, nearOriginInnerWeight]
  congr 1
  have hd : 0 < u ^ 2 + v ^ 2 := by positivity
  have hden : 0 < 1 + (v / u) ^ 2 := by positivity
  field_simp [hu.ne', hd.ne', hden.ne']

theorem angularMean_mono_on {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ θ ∈ Icc (-Real.pi) Real.pi, f θ ≤ g θ) :
    angularMean f ≤ angularMean g := by
  unfold angularMean
  exact mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on
    (by linarith [Real.pi_pos]) (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) h)
    (by positivity)

theorem angularAverage_single_cosine (a : ℂ) (k : ℕ) :
    angularAverage (fun θ => a * (Real.cos (((k + 1 : ℕ) : ℝ) * θ) : ℂ)) = 0 := by
  let c (n : ℕ) : ℂ := if n = k then a else 0
  have hc : Summable (fun n => ‖c n‖) := by
    exact (hasSum_ite_eq k ‖a‖).summable.congr (fun n => by by_cases h : n = k <;> simp [c,h])
  have he (θ : ℝ) :
      (∑' n : ℕ, c n * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ)) =
      a * (Real.cos (((k + 1 : ℕ) : ℝ) * θ) : ℂ) := by
    rw [← tsum_ite_eq k (fun n => a * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ))]
    exact tsum_congr (fun n => by by_cases h : n = k <;> simp [c,h])
  have h := angularAverage_cosineSeries c hc
  simpa only [he] using h

theorem angularMean_norm_sq_single_cosine (a : ℂ) (k : ℕ) :
    angularMean (fun θ => ‖a * (Real.cos (((k + 1 : ℕ) : ℝ) * θ) : ℂ)‖ ^ 2) =
      ‖a‖ ^ 2 / 2 := by
  let c (n : ℕ) : ℂ := if n = k then a else 0
  have hc : Summable (fun n => ‖c n‖) := by
    exact (hasSum_ite_eq k ‖a‖).summable.congr (fun n => by by_cases h : n = k <;> simp [c,h])
  have he (θ : ℝ) :
      (∑' n : ℕ, c n * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ)) =
      a * (Real.cos (((k + 1 : ℕ) : ℝ) * θ) : ℂ) := by
    rw [← tsum_ite_eq k (fun n => a * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ))]
    exact tsum_congr (fun n => by by_cases h : n = k <;> simp [c,h])
  have hs : (∑' n, ‖c n‖ ^ 2) = ‖a‖ ^ 2 := by
    rw [← tsum_ite_eq k (fun _ => ‖a‖ ^ 2)]
    exact tsum_congr (fun n => by by_cases h : n = k <;> simp [c,h])
  rw [← show (1 / 2 : ℝ) * ‖a‖ ^ 2 = ‖a‖ ^ 2 / 2 by ring]
  simpa only [he, hs] using angularMean_norm_sq_cosineSeries c hc

theorem angularMean_sq_cosine (k : ℕ) :
    angularMean (fun θ => (Real.cos (((k + 1 : ℕ) : ℝ) * θ)) ^ 2) = 1 / 2 := by
  simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_one, one_pow]
    using angularMean_norm_sq_single_cosine 1 k

private theorem nearOriginMainLog_factor (r θ : ℝ) (ζ : ℂ) :
    nearOriginMainLog r θ ζ = (2 * I * (r : ℂ) / ζ) * (Real.cos θ : ℂ) := by
  rw [nearOriginMainLog]
  ring

private theorem nearOriginCorrection_factor (r θ : ℝ) (ζ : ℂ) :
    nearOriginCorrection r θ ζ = ((r : ℂ) ^ 2 / (2 * ζ)) * (Real.cos (2 * θ) : ℂ) := by
  rw [nearOriginCorrection]
  ring

theorem angularAverage_nearOriginMainLog (r : ℝ) (ζ : ℂ) :
    angularAverage (fun θ => nearOriginMainLog r θ ζ) = 0 := by
  simp_rw [nearOriginMainLog_factor]
  simpa only [zero_add, Nat.cast_one, one_mul] using angularAverage_single_cosine (2 * I * (r : ℂ) / ζ) 0

theorem angularAverage_nearOriginCorrection (r : ℝ) (ζ : ℂ) :
    angularAverage (fun θ => nearOriginCorrection r θ ζ) = 0 := by
  simp_rw [nearOriginCorrection_factor]
  simpa only [Nat.reduceAdd, Nat.cast_ofNat] using
    angularAverage_single_cosine ((r : ℂ) ^ 2 / (2 * ζ)) 1

theorem angularMean_nearOriginMainLog_sq (r u v : ℝ) :
    angularMean (fun θ => ‖nearOriginMainLog r θ (verticalPoint u v)‖ ^ 2) =
      2 * r ^ 2 / (u ^ 2 + v ^ 2) := by
  simp_rw [nearOriginMainLog_factor]
  rw [show (fun θ : ℝ => ‖(2 * I * (r : ℂ) / verticalPoint u v) * (Real.cos θ : ℂ)‖ ^ 2) =
      (fun θ : ℝ => ‖(2 * I * (r : ℂ) / verticalPoint u v) *
        (Real.cos (((0 + 1 : ℕ) : ℝ) * θ) : ℂ)‖ ^ 2) by simp only [zero_add, Nat.cast_one, one_mul],
    angularMean_norm_sq_single_cosine, norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, div_pow, mul_pow, sq_abs, norm_verticalPoint_sq]
  ring

theorem angularMean_nearOriginCorrection_sq (r u v : ℝ) :
    angularMean (fun θ => ‖nearOriginCorrection r θ (verticalPoint u v)‖ ^ 2) =
      r ^ 4 / (8 * (u ^ 2 + v ^ 2)) := by
  simp_rw [nearOriginCorrection_factor]
  rw [show (fun θ : ℝ => ‖(((r : ℂ) ^ 2) / (2 * verticalPoint u v)) * (Real.cos (2 * θ) : ℂ)‖ ^ 2) =
      (fun θ : ℝ => ‖(((r : ℂ) ^ 2) / (2 * verticalPoint u v)) *
        (Real.cos (((1 + 1 : ℕ) : ℝ) * θ) : ℂ)‖ ^ 2) by norm_num,
    angularMean_norm_sq_single_cosine, norm_div, norm_pow, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, mul_pow, norm_verticalPoint_sq]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end DurfeeCCS.Step08
