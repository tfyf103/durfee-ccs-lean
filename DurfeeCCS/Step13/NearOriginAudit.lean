module

public import DurfeeCCS.Step08.NearOriginContour

/-! The cancellations and strict numerical bounds in the near-origin argument. -/

public section

namespace DurfeeCCS.Step13

open Complex MeasureTheory DurfeeCCS.Step06 DurfeeCCS.Step08

/-- The three logarithmic terms in (16) have zero angular mean. -/
theorem nearOrigin_angular_means_zero {r : ℝ} (hr : |r| ≤ 1) {ζ : ℂ} (hζ : 0 < ζ.re) :
    angularAverage (fun θ => pairedLog r θ ζ) = 0 ∧
    angularAverage (fun θ => nearOriginMainLog r θ ζ) = 0 ∧
    angularAverage (fun θ => nearOriginCorrection r θ ζ) = 0 := by
  refine ⟨angularAverage_pairedLog r hr hζ, ?_, ?_⟩
  · have h (θ : ℝ) : nearOriginMainLog r θ ζ =
        (2 * I * (r : ℂ) / ζ) * (Real.cos θ : ℂ) := by
      unfold nearOriginMainLog
      ring
    simp_rw [h]
    simpa using angularAverage_single_cosine (2 * I * (r : ℂ) / ζ) 0
  · have h (θ : ℝ) : nearOriginCorrection r θ ζ =
        ((r : ℂ)^2 / (2 * ζ)) * (Real.cos (2 * θ) : ℂ) := by
      unfold nearOriginCorrection
      ring
    simp_rw [h]
    simpa using angularAverage_single_cosine ((r : ℂ)^2 / (2 * ζ)) 1

/-- The first-mode and tail bounds of (19), including the two strict estimates. -/
theorem nearOrigin_log_errors {r u v : ℝ} (hu : 0 < u) (hur : u ≤ r)
    (hr : r ≤ 1 / 40) (hv : |v| ≤ Real.pi) (θ : ℝ) :
    let ζ := verticalPoint u v
    let Δ := r ^ 2 / u
    let S := 2 / u * ∑' m : ℕ, r ^ (m + 2) / (((m + 2 : ℕ) : ℝ) ^ 2)
    ‖nearOriginFirstRemainder r θ ζ‖ ≤ 0.16 * r * ‖ζ‖ * |Real.cos θ| ∧
    ‖nearOriginTailRemainder r θ ζ‖ ≤ S ∧
    S ≤ r ^ 2 / (2 * u * (1 - r)) ∧
    r ^ 2 / (2 * u * (1 - r)) < 0.513 * Δ ∧
    ‖pairedLog r θ ζ - nearOriginMainLog r θ ζ‖ < 1.02 * Δ := by
  let ζ := verticalPoint u v
  have hζ : 0 < ζ.re := by simpa only [ζ, verticalPoint_re] using hu
  have hur' : ζ.re ≤ r := by simpa only [ζ, verticalPoint_re] using hur
  have hv' : |ζ.im| ≤ Real.pi := by simpa only [ζ, verticalPoint_im] using hv
  have hr₀ := hu.trans_le hur
  have hnorm := norm_le_for_nearOrigin_strip hζ.le (hur'.trans hr) hv'
  have hsq : ‖ζ‖ ^ 2 < 10 :=
    (pow_le_pow_left₀ (norm_nonneg ζ) hnorm 2).trans_lt (by norm_num)
  have htail := norm_pairedLogTail_series_bounds θ hr₀.le (by linarith : r < 1) hζ 1
  refine ⟨norm_pairedLogMode_zero_sub_main_le θ hr₀.le hζ hv' hsq,
    ?_, ?_, pairedLogTail_one_geometric_lt hr₀ hr hu, ?_⟩
  · simpa only [nearOriginTailRemainder, ζ, verticalPoint_re, Nat.add_assoc] using htail.1
  · have hb := htail.2
    simp only [ζ, verticalPoint_re, Nat.add_assoc, Nat.reduceAdd, Nat.cast_ofNat] at hb
    convert hb using 1
    have hs : 0 < 1 - r := by linarith
    field_simp [ne_of_gt hu, ne_of_gt hs]
  · simpa only [ζ, verticalPoint_re] using norm_pairedLog_sub_main_lt θ hζ hur' hr hv'

/-- The small-arc inequalities preceding (20), with the strict bound for the reciprocal. -/
theorem nearOrigin_smallArc_bounds {r u v : ℝ} (hu : 0 < u) (hur : u ≤ r)
    (hr : r ≤ 1 / 40) (hv : |v| ≤ 4 * u) (θ : ℝ) :
    let ζ := verticalPoint u v
    ‖ζ‖ ≤ Real.sqrt 17 * u ∧ Real.sqrt 17 * u < 0.104 ∧
    ‖(2 * sinh ζ)⁻¹ - (2 * ζ)⁻¹‖ < 0.084 * ‖ζ‖ ∧
    ‖pairedLog r θ ζ - nearOriginMainLog r θ ζ - nearOriginCorrection r θ ζ‖ ≤
      0.66 * r * u + 0.228 * r * (r ^ 2 / u) + 0.35 * r ^ 2 * u ∧
    ‖nearOriginCorrection r θ ζ‖ ≤ (r ^ 2 / u) / 2 := by
  let ζ := verticalPoint u v
  have hζ : 0 < ζ.re := by simpa only [ζ, verticalPoint_re] using hu
  have hvsq := pow_le_pow_left₀ (abs_nonneg v) hv 2
  rw [sq_abs] at hvsq
  have h17 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have hnorm : ‖ζ‖ ≤ Real.sqrt 17 * u := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [show ‖ζ‖ ^ 2 = u ^ 2 + v ^ 2 from norm_verticalPoint_sq u v, mul_pow, h17]
    nlinarith only [hvsq]
  have hcap : Real.sqrt (17 : ℝ) * u < 0.104 := by
    have hb : Real.sqrt (17 : ℝ) ≤ 4.124 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    calc
      _ ≤ 4.124 * u := mul_le_mul_of_nonneg_right hb hu.le
      _ < _ := by linarith only [hur.trans hr]
  refine ⟨hnorm, hcap, norm_sinh_inv_sub_inv_lt hζ (hnorm.trans hcap.le), ?_, ?_⟩
  · simpa only [ζ, verticalPoint_re] using
      norm_pairedLog_sub_main_sub_correction_le θ hζ (hu.le.trans hur) hr
        (by simpa only [ζ, verticalPoint_re] using hur.trans hr)
        (by simpa only [ζ, verticalPoint_re, verticalPoint_im] using hv)
  · simpa only [ζ, verticalPoint_re] using norm_nearOriginCorrection_le r θ hζ

/-- The exact Parseval integral and its reciprocal bound. -/
theorem nearOrigin_sinh_parseval {u : ℝ} (hu : 0 < u) {k : ℕ} (hk : 0 < k) :
    angularMean (fun v => (‖2 * sinh ((k : ℂ) * verticalPoint u v / 2)‖ ^ 2)⁻¹) =
      (2 * Real.sinh ((k : ℝ) * u))⁻¹ ∧
    (2 * Real.sinh ((k : ℝ) * u))⁻¹ ≤ (2 * (k : ℝ) * u)⁻¹ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨angularMean_inv_norm_sinh_sq hu hk.ne', ?_⟩
  have hs := mul_le_mul_of_nonneg_left
    (Real.self_le_sinh_iff.mpr (mul_nonneg hkR.le hu.le)) (by norm_num : (0 : ℝ) ≤ 2)
  exact inv_anti₀ (by positivity) (by simpa only [mul_assoc] using hs)

/-- The three norms used in the near-origin Parseval estimates on pages 9 and 10. -/
theorem nearOrigin_parseval_bounds {r u : ℝ} (hu : 0 < u) (hur : u ≤ r) (hr : r ≤ 1 / 40) :
    angularMean (fun v => angularMean (fun θ =>
      ‖nearOriginMainLog r θ (verticalPoint u v)‖ ^ 2)) ≤ r ^ 2 / u ∧
    Real.sqrt (angularMean (fun v => angularMean (fun θ =>
      ‖nearOriginFirstRemainder r θ (verticalPoint u v)‖ ^ 2))) < 0.206 * r ∧
    angularMean (fun v => angularMean (fun θ =>
      ‖nearOriginTailRemainder r θ (verticalPoint u v)‖ ^ 2)) < (0.354 * r ^ 2) ^ 2 / u := by
  have hr₀ := hu.trans_le hur
  refine ⟨double_angularMean_nearOriginMainLog_sq_le hu, ?_, ?_⟩
  · apply (Real.sqrt_lt' (show 0 < 0.206 * r by positivity)).mpr
    rw [mul_pow]
    exact double_angularMean_sq_first_remainder_lt hr₀ hu (hur.trans hr)
  · convert double_angularMean_sq_tail_remainder_lt hr₀ hr hu using 1
    ring

/-- The normalized strict bound for the second contour contribution in (18). -/
theorem nearOrigin_middle_error_paper {r u : ℝ} (hu : 0 < u) (hur : u ≤ r)
    (hr : r ≤ 1 / 40) (hΔ : r ^ 2 / u ≤ 1) :
    let σ := r / u
    let Δ := r ^ 2 / u
    Real.exp σ / (2 * Real.pi) * (∫ v in {v : ℝ | 4 * u < |v| ∧ |v| ≤ Real.pi},
      ‖nearOriginMiddleError r u v‖) <
    Real.exp (3 * σ / 2 + 1.02 * Δ) * (0.48 * r ^ 2 + 0.36 * (r ^ 3 / u)) := by
  dsimp only
  let E := ∫ v in {v : ℝ | 4 * u < |v| ∧ |v| ≤ Real.pi}, ‖nearOriginMiddleError r u v‖
  change Real.exp (r / u) / (2 * Real.pi) * E < _
  rw [div_eq_mul_inv (Real.exp _), mul_assoc]
  refine (mul_lt_mul_of_pos_left (integral_norm_nearOriginMiddleError_lt hu hur hr hΔ)
    (Real.exp_pos (r / u))).trans_eq ?_
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end DurfeeCCS.Step13
