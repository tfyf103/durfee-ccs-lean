module

public import DurfeeCCS.Step08.AngularErrors
public import DurfeeCCS.Step08.NearOriginModelIntegral
public import DurfeeCCS.Step08.SaddleExponentialMean
public import DurfeeCCS.Step08.SaddleFourier

/-! The whole vertical contour underlying the saddle model. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06

private def saddlePowerCoeff (r : ℝ) (k : ℕ) : ℂ :=
  angularAverage (fun θ => saddleG r θ ^ (k+2) / ((k+2).factorial : ℂ))

private theorem angularAverage_saddleG_div' {r : ℝ} (hr : |r| ≤ 1) (z : ℂ) :
    angularAverage (fun θ => saddleG r θ / z) = 0 := by
  simp only [div_eq_mul_inv, mul_comm (saddleG r _) _, angularAverage_const_mul,
    angularAverage_saddleG r hr, mul_zero]

private theorem norm_saddlePowerCoeff_le {r : ℝ} (hr : |r| ≤ 1) (k : ℕ) :
    ‖saddlePowerCoeff r k‖ ≤ (Real.pi^2/3 * |r|)^(k+2) / ((k+2).factorial : ℝ) := by
  let f (θ : ℝ) := saddleG r θ ^ (k+2) / ((k+2).factorial : ℂ)
  let b : ℝ := (Real.pi^2/3 * |r|)^(k+2) / ((k+2).factorial : ℝ)
  have hf : Continuous f := ((continuous_saddleG hr).pow _).div_const _
  have hb (θ : ℝ) : ‖f θ‖ ≤ b := by
    simp only [f, b, norm_div, norm_pow, Complex.norm_natCast]
    gcongr
    exact norm_saddleG_le hr θ
  have hc : angularMean (fun _ => b) = b := by
    apply Complex.ofReal_injective
    rw [← angularAverage_ofReal, angularAverage_const]
  change ‖angularAverage f‖ ≤ b
  refine (norm_angularAverage_le f).trans ?_
  rw [← hc]
  unfold angularMean
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (hf.norm.intervalIntegrable _ _) intervalIntegrable_const
  exact fun θ _ => hb θ

private theorem summable_norm_saddlePowerCoeff {r u : ℝ} (hr : |r| ≤ 1) (hu : 0 < u) :
    Summable fun k => ‖saddlePowerCoeff r k‖ / u^(k+2-2) := by
  let A : ℝ := Real.pi^2/3 * |r|
  have h : Summable fun k : ℕ => u^2 * ((A/u)^(k+2)/((k+2).factorial : ℝ)) :=
    ((summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial (A/u))).mul_left _
  apply h.of_nonneg_of_le (fun _ => by positivity)
  intro k
  calc
    _ ≤ (A^(k+2) / ((k+2).factorial : ℝ)) / u^k := by
      rw [Nat.add_sub_cancel_right]
      gcongr
      exact norm_saddlePowerCoeff_le hr k
    _ = _ := by
      rw [div_pow, pow_add u k 2, div_div]
      field_simp [hu.ne']

private theorem exp_sub_one_sub_eq_tsum (z : ℂ) :
    exp z - 1 - z = ∑' k : ℕ, z^(k+2) / ((k+2).factorial : ℂ) := by
  have he : exp z = ∑' k : ℕ, z^k / (k.factorial : ℂ) :=
    congrFun (Complex.exp_eq_exp_ℂ.trans NormedSpace.exp_eq_tsum_div) z
  have hs : Summable fun k : ℕ => z^k / (k.factorial : ℂ) :=
    Summable.of_norm (by simpa only [norm_div, norm_pow, Complex.norm_natCast] using
      Real.summable_pow_div_factorial ‖z‖)
  rw [he, ← hs.sum_add_tsum_nat_add 2]
  norm_num [Finset.sum_range_succ]
  ring

private theorem saddleExponentialMean_eq_series {r u v : ℝ} (hr : |r| ≤ 1) :
    saddleExponentialMean r u v =
      ∑' k, saddlePowerCoeff r k / (verticalPoint u v)^(k+2) := by
  let z := verticalPoint u v
  let g (θ : ℝ) := saddleG r θ / z
  have hg : Continuous g := (continuous_saddleG hr).div_const _
  have he : Continuous (fun θ => exp (g θ) - 1) := (continuous_exp.comp hg).sub continuous_const
  have hzero : angularAverage g = 0 := angularAverage_saddleG_div' hr z
  have hsub : saddleExponentialMean r u v =
      angularAverage (fun θ => exp (g θ) - 1 - g θ) := by
    rw [angularAverage_sub (he.intervalIntegrable _ _) (hg.intervalIntegrable _ _), hzero, sub_zero]
    rfl
  let F (k : ℕ) (θ : ℝ) := g θ ^ (k+2) / ((k+2).factorial : ℂ)
  let A : ℝ := (Real.pi^2/3 * |r|) / ‖z‖
  have hsum : Summable fun k : ℕ => A^(k+2) / ((k+2).factorial : ℝ) :=
    (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial A)
  have hb (k : ℕ) (θ : ℝ) : ‖F k θ‖ ≤ A^(k+2) / ((k+2).factorial : ℝ) := by
    simp only [F, A, g, norm_div, norm_pow, Complex.norm_natCast]
    gcongr
    exact norm_saddleG_le hr θ
  rw [hsub]
  simp_rw [exp_sub_one_sub_eq_tsum]
  change angularAverage (fun θ => ∑' k, F k θ) = _
  have hF (k : ℕ) : Continuous (F k) := by
    dsimp only [F]
    apply Continuous.div_const
    exact hg.pow _
  rw [angularAverage_tsum_uniform hF hsum hb]
  apply tsum_congr
  intro k
  change angularAverage (fun θ => F k θ) = _
  have hpoint (θ : ℝ) :
      F k θ = ((z^(k+2))⁻¹) * (saddleG r θ ^ (k+2) / ((k+2).factorial : ℂ)) := by
    dsimp only [F, g]
    rw [div_pow]
    ring
  simp_rw [hpoint, angularAverage_const_mul, saddlePowerCoeff, div_eq_mul_inv]
  exact mul_comm _ _

private def saddleBesselTerm (n k : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ)^k * z^(k+1) / ((k.factorial : ℂ) * ((k+1).factorial : ℂ))

private theorem norm_saddleBesselTerm_le (n k : ℕ) {A : ℝ} {z : ℂ} (hz : ‖z‖ ≤ A) :
    ‖saddleBesselTerm n k z‖ ≤ A * (((n : ℝ)*A)^k / (k.factorial : ℝ)) := by
  have hA := (norm_nonneg z).trans hz
  have hfac : (1 : ℝ) ≤ (k+1).factorial := by exact_mod_cast Nat.factorial_pos (k+1)
  simp only [saddleBesselTerm, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ)^k * A^(k+1) / ((k.factorial : ℝ) * 1) := by gcongr
    _ = _ := by rw [mul_pow, pow_succ A k]; ring

private theorem saddleBesselAverage_eq_series (n : ℕ) {r : ℝ} (hr : |r| ≤ 1) :
    (saddleBesselAverage n r : ℂ) =
      ∑' k : ℕ, saddlePowerCoeff r k * ((n : ℂ)^(k+1) / ((k+1).factorial : ℂ)) := by
  let g := saddleG r
  let A := Real.pi^2/3 * |r|
  let Q (k : ℕ) (θ : ℝ) := saddleBesselTerm n k (g θ)
  have hg : Continuous g := continuous_saddleG hr
  have hQ (k : ℕ) : Continuous (Q k) := by
    dsimp only [Q, saddleBesselTerm]
    fun_prop
  have hbound : Summable fun k : ℕ => A * (((n : ℝ)*A)^k / (k.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial ((n : ℝ)*A)).mul_left A
  have hb (k : ℕ) (θ : ℝ) : ‖Q k θ‖ ≤ A * (((n : ℝ)*A)^k / (k.factorial : ℝ)) :=
    norm_saddleBesselTerm_le n k (norm_saddleG_le hr θ)
  have hs : Summable fun k => angularAverage (Q k) := by
    have h := hasSum_angular_integral_uniform hQ hbound hb
    exact (h.mul_left ((2 * Real.pi : ℂ)⁻¹)).summable
  rw [saddleBesselAverage_ofReal n hr]
  change angularAverage (fun θ => saddleBesselKernel n (g θ)) = _
  simp_rw [saddleBesselKernel_eq_tsum]
  change angularAverage (fun θ => ∑' k, Q k θ) = _
  rw [angularAverage_tsum_uniform hQ hbound hb, ← hs.sum_add_tsum_nat_add 1]
  have hzero : angularAverage (Q 0) = 0 := by
    simpa only [Q, saddleBesselTerm, pow_zero, zero_add, pow_one, one_mul, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, div_one] using angularAverage_saddleG r hr
  rw [Finset.sum_range_one, hzero, zero_add]
  apply tsum_congr
  intro k
  change angularAverage (fun θ => Q (k+1) θ) = _
  have hpoint (θ : ℝ) : Q (k+1) θ =
      ((n : ℂ)^(k+1) / ((k+1).factorial : ℂ)) *
        (g θ ^ (k+2) / ((k+2).factorial : ℂ)) := by
    simp only [Q, saddleBesselTerm, div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hpoint, angularAverage_const_mul]
  exact mul_comm _ _

/-- The vertical saddle integrand is absolutely integrable on the full line. -/
theorem integrable_saddleExponentialMean {r u : ℝ} (hr : |r| ≤ 1) (hu : 0 < u) (x : ℝ) :
    Integrable (fun v : ℝ => exp ((x : ℂ) * verticalPoint u v) * saddleExponentialMean r u v) := by
  simp_rw [saddleExponentialMean_eq_series hr]
  exact (integral_vertical_power_series hu (saddlePowerCoeff r) (fun k => k+2)
    (fun _ => by omega) (summable_norm_saddlePowerCoeff hr hu)).1

/-- The whole-line angular average in the saddle model equals the paper's Bessel average. -/
theorem integral_saddleExponentialMean_eq_saddleBesselAverage {r u : ℝ} {n : ℕ}
    (hr : |r| ≤ 1) (hu : 0 < u) (hn : 0 < n) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ v : ℝ, exp ((n : ℂ) * verticalPoint u v) * saddleExponentialMean r u v) =
      (saddleBesselAverage n r : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (integral_vertical_power_series hu (saddlePowerCoeff r) (fun k => k+2)
    (fun _ => by omega) (summable_norm_saddlePowerCoeff hr hu)).2 hnR
  simp_rw [saddleExponentialMean_eq_series hr, saddleBesselAverage_eq_series n hr]
  simpa only [Complex.ofReal_natCast, show ∀ k : ℕ, k+2-1 = k+1 from fun _ => by omega] using h

end DurfeeCCS.Step08
