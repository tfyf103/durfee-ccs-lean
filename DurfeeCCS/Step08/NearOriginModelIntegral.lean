module

public import DurfeeCCS.Step08.ModelAngular
public import DurfeeCCS.Step08.NearOriginLaplace
public import DurfeeCCS.Step08.NearOriginModelSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Evaluation of the angular model on the vertical contour in (17). -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Complex MeasureTheory Filter
open scoped Topology

/-- A summable coefficient bound at the real part of the contour supplies an
integrable majorant for termwise integration on the whole vertical line. -/
theorem integral_vertical_power_series {u x : ℝ} (hu : 0 < u)
    (a : ℕ → ℂ) (j : ℕ → ℕ) (hj : ∀ d, 2 ≤ j d)
    (ha : Summable fun d => ‖a d‖ / u^(j d - 2)) :
    Integrable (fun v : ℝ => exp ((x : ℂ) * verticalPoint u v) *
      ∑' d, a d / (verticalPoint u v)^(j d)) ∧
    (0 < x → ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ v : ℝ, exp ((x : ℂ) * verticalPoint u v) *
      ∑' d, a d / (verticalPoint u v)^(j d)) =
      ∑' d, a d * ((x : ℂ)^(j d-1) / (((j d-1).factorial : ℕ) : ℂ))) := by
  let F (d : ℕ) (v : ℝ) :=
    exp ((x : ℂ) * verticalPoint u v) * (a d / (verticalPoint u v)^(j d))
  let M (d : ℕ) (v : ℝ) :=
    (Real.exp (x*u) * (‖a d‖ / u^(j d-2))) * (u^2 + v^2)⁻¹
  have hF (d : ℕ) : AEStronglyMeasurable (F d) volume := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul (by unfold verticalPoint; fun_prop)
    apply Continuous.div continuous_const (by unfold verticalPoint; fun_prop)
    exact fun v => pow_ne_zero _ (verticalPoint_ne_zero hu v)
  have hM (d : ℕ) (v : ℝ) : ‖F d v‖ ≤ M d v := by
    have hv : u ≤ ‖verticalPoint u v‖ := by
      simpa only [verticalPoint_re] using Complex.re_le_norm (verticalPoint u v)
    have hp : ‖verticalPoint u v‖^(j d) =
        ‖verticalPoint u v‖^(j d-2) * ‖verticalPoint u v‖^2 := by
      rw [← pow_add, Nat.sub_add_cancel (hj d)]
    have hi := inv_anti₀ (pow_pos hu (j d-2)) (pow_le_pow_left₀ hu.le hv (j d-2))
    dsimp only [F, M]
    rw [norm_mul, Complex.norm_exp, show ((x : ℂ) * verticalPoint u v).re = x*u by
      simp [Complex.mul_re],
      norm_div, norm_pow, hp, norm_verticalPoint_sq, div_eq_mul_inv, mul_inv]
    calc
      _ = (Real.exp (x*u) * (‖a d‖ * (‖verticalPoint u v‖^(j d-2))⁻¹)) *
          (u^2 + v^2)⁻¹ := by ring
      _ ≤ _ := by
        rw [div_eq_mul_inv ‖a d‖]
        gcongr
  have hMs (v : ℝ) : Summable fun d => M d v :=
    (ha.mul_left (Real.exp (x*u))).mul_right ((u^2 + v^2)⁻¹)
  have hMi : Integrable fun v : ℝ => ∑' d, M d v := by
    simpa only [M, tsum_mul_right] using
      (integrable_cauchy_density hu).const_mul (∑' d, Real.exp (x*u) * (‖a d‖ / u^(j d-2)))
  have hFs (v : ℝ) : Summable fun d => ‖F d v‖ :=
    (hMs v).of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => hM d v)
  let f (v : ℝ) := exp ((x : ℂ) * verticalPoint u v) *
    ∑' d, a d / (verticalPoint u v)^(j d)
  have hlim (v : ℝ) : HasSum (fun d => F d v) (f v) := by
    change HasSum (fun d => F d v) (_ * ∑' d, _)
    rw [← tsum_mul_left]
    exact (hFs v).of_norm.hasSum
  refine ⟨hMi.mono' ?_ (ae_of_all _ fun v => ?_), ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun k v => ∑ d ∈ Finset.range k, F d v)
      (fun k => by
        have heq : (fun v => ∑ d ∈ Finset.range k, F d v) = ∑ d ∈ Finset.range k, F d := by
          funext v
          exact (Finset.sum_apply _ _ _).symm
        rw [heq]
        exact Finset.aestronglyMeasurable_sum _ fun d _ => hF d) ?_
    exact ae_of_all _ fun v => (hlim v).tendsto_sum_nat
  · change ‖f v‖ ≤ _
    rw [← (hlim v).tsum_eq]
    exact (norm_tsum_le_tsum_norm (hFs v)).trans
      (Summable.tsum_le_tsum (fun d => hM d v) (hFs v) (hMs v))
  · intro hx
    have hInt := hasSum_integral_of_dominated_convergence M hF
      (fun d => ae_of_all _ (hM d)) (ae_of_all _ hMs) hMi (ae_of_all _ hlim)
    change _ * (∫ v, f v) = _
    rw [← hInt.tsum_eq, ← tsum_mul_left]
    apply tsum_congr
    intro d
    have hpoint (v : ℝ) : F d v =
        a d * (exp ((x : ℂ) * verticalPoint u v) / (verticalPoint u v)^(j d)) := by
      dsimp only [F]
      ring
    simp_rw [hpoint, integral_const_mul, mul_left_comm _ (a d),
      integral_vertical_kernel hu hx (hj d)]

private def baseCoeff (r : ℝ) (d : ℕ) : ℂ :=
  (-((r : ℂ)^2))^(d+1) / (((d+1).factorial : ℂ)^2)

private def correctionCoeff (r : ℝ) (d : ℕ) : ℂ :=
  (-((r : ℂ)^2))^d / ((d.factorial : ℂ) * ((d+2).factorial : ℂ))

private theorem summable_norm_baseCoeff (r : ℝ) {u : ℝ} (hu : 0 < u) :
    Summable fun d => ‖baseCoeff r d‖ / u^(2*(d+1)-2) := by
  apply ((Real.summable_pow_div_factorial (r^2/u^2)).mul_left (r^2)).of_nonneg_of_le
    (fun _ => by positivity)
  intro d
  have hfac : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hfac₁ : (d.factorial : ℝ) ≤ (d+1).factorial := by
    exact_mod_cast Nat.factorial_le (show d ≤ d+1 by omega)
  have hfac₂ : (1 : ℝ) ≤ (d+1).factorial := by exact_mod_cast Nat.factorial_pos (d+1)
  simp only [baseCoeff, norm_div, norm_pow, norm_neg, Complex.norm_real, Complex.norm_natCast,
    Real.norm_eq_abs]
  rw [← abs_pow, abs_of_nonneg (sq_nonneg r),
    show 2*(d+1)-2 = 2*d by omega, pow_mul u 2 d]
  calc
    _ = r^2 * ((r^2/u^2)^d / (((d+1).factorial : ℝ)^2)) := by
      rw [div_pow, pow_succ (r^2) d]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by positivity) hfac _) (by positivity)
      rw [pow_two]
      calc
        (d.factorial : ℝ) ≤ ((d+1).factorial : ℝ) * 1 := by simpa using hfac₁
        _ ≤ _ := by gcongr

private theorem summable_norm_correctionCoeff (r : ℝ) {u : ℝ} (hu : 0 < u) :
    Summable fun d => ‖correctionCoeff r d‖ / u^(2*d+3-2) := by
  apply ((Real.summable_pow_div_factorial (r^2/u^2)).mul_left u⁻¹).of_nonneg_of_le
    (fun _ => by positivity)
  intro d
  have hfac : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hfac₂ : (1 : ℝ) ≤ (d+2).factorial := by exact_mod_cast Nat.factorial_pos (d+2)
  simp only [correctionCoeff, norm_div, norm_pow, norm_neg, norm_mul,
    Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs]
  rw [← abs_pow, abs_of_nonneg (sq_nonneg r), show 2*d+3-2 = 2*d+1 by omega,
    pow_succ u (2*d), pow_mul u 2 d]
  calc
    _ = u⁻¹ * ((r^2/u^2)^d / ((d.factorial : ℝ) * ((d+2).factorial : ℝ))) := by
      rw [div_pow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by positivity) hfac _) (by positivity)
      calc
        (d.factorial : ℝ) = ((d.factorial : ℝ) * 1) := by rw [mul_one]
        _ ≤ _ := by gcongr

theorem integrable_nearOriginAngularBase {u : ℝ} (hu : 0 < u) (r x : ℝ) :
    Integrable (fun v : ℝ => exp ((x : ℂ) * verticalPoint u v) *
      nearOriginAngleAverage (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) - 1)) := by
  have hB := (integral_vertical_power_series (x := x) hu (baseCoeff r) (fun d => 2*(d+1))
    (fun d => by omega) (summable_norm_baseCoeff r hu)).1
  simpa only [nearOriginAngularBase_eq_series, nearOriginAngularBaseTerm, baseCoeff, div_div]
    using hB

theorem integrable_nearOriginAngularCorrection {u : ℝ} (hu : 0 < u) (r x : ℝ) :
    Integrable (fun v : ℝ => exp ((x : ℂ) * verticalPoint u v) *
      nearOriginAngleAverage (fun θ =>
        exp (nearOriginMainLog r θ (verticalPoint u v)) *
          nearOriginCorrection r θ (verticalPoint u v))) := by
  have hC := (integral_vertical_power_series (x := x) hu (correctionCoeff r) (fun d => 2*d+3)
    (fun d => by omega) (summable_norm_correctionCoeff r hu)).1.const_mul (-((r : ℂ)^4) / 2)
  apply hC.congr
  exact ae_of_all _ fun v => by
    dsimp only
    rw [nearOriginAngularCorrection_eq_series r (verticalPoint_ne_zero hu v)]
    simp only [nearOriginAngularCorrectionTerm, correctionCoeff, div_div]
    ring

theorem integrable_nearOriginAngularModel {u : ℝ} (hu : 0 < u) (r x : ℝ) :
    Integrable (fun v : ℝ => exp ((x : ℂ) * verticalPoint u v) *
      nearOriginAngularModel r (verticalPoint u v)) := by
  simp_rw [nearOriginAngularModel_eq_add, mul_add]
  exact (integrable_nearOriginAngularBase hu r x).add (integrable_nearOriginAngularCorrection hu r x)

/-- The normalized vertical integral of the near-origin angular model is
the Bessel expression of (17). -/
theorem integral_nearOriginAngularModel_eq_nearOriginModel
    {u r σ : ℝ} {n : ℕ} (hu : 0 < u) (hn : 0 < n) (hσ : σ^2 = (n : ℝ)*r) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ v : ℝ, exp ((n : ℂ) * verticalPoint u v) * nearOriginAngularModel r (verticalPoint u v)) =
        nearOriginModel σ n := by
  let B (v : ℝ) := exp ((n : ℂ) * verticalPoint u v) *
    ∑' d, baseCoeff r d / (verticalPoint u v)^(2*(d+1))
  let C (v : ℝ) := exp ((n : ℂ) * verticalPoint u v) *
    ∑' d, correctionCoeff r d / (verticalPoint u v)^(2*d+3)
  let c : ℂ := (r : ℂ)^4 / 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hσC : (σ : ℂ)^2 = (n : ℂ)*(r : ℂ) := by exact_mod_cast hσ
  have hσpow (m : ℕ) : (σ : ℂ)^(2*m) = (n : ℂ)^m * (r : ℂ)^m := by
    rw [pow_mul, hσC, mul_pow]
  have hB := integral_vertical_power_series (x := (n : ℝ)) hu (baseCoeff r) (fun d => 2*(d+1))
    (fun d => by omega) (summable_norm_baseCoeff r hu)
  have hC := integral_vertical_power_series (x := (n : ℝ)) hu (correctionCoeff r) (fun d => 2*d+3)
    (fun d => by omega) (summable_norm_correctionCoeff r hu)
  have hpoint (v : ℝ) : exp ((n : ℂ) * verticalPoint u v) *
      nearOriginAngularModel r (verticalPoint u v) = B v - c * C v := by
    rw [nearOriginAngularModel_eq_series r (verticalPoint_ne_zero hu v)]
    simp only [B, C, c, nearOriginAngularBaseTerm, nearOriginAngularCorrectionTerm,
      baseCoeff, correctionCoeff, div_div]
    ring
  simp only [Complex.ofReal_natCast] at hB hC
  change Integrable B ∧ (0 < (n : ℝ) → ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ v, B v) = _) at hB
  change Integrable C ∧ (0 < (n : ℝ) → ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ v, C v) = _) at hC
  simp_rw [hpoint]
  rw [integral_sub hB.1 (hC.1.const_mul c), integral_const_mul, mul_sub,
    mul_left_comm _ c, hB.2 hnR, hC.2 hnR, nearOriginModel_eq_series]
  simp only [← tsum_mul_left]
  congr 1
  · apply tsum_congr
    intro d
    rw [baseCoeff, show 2*(d+1)-1 = 2*d+1 by omega, neg_pow, ← pow_mul,
      show 4*(d+1) = 2*(2*(d+1)) by omega, hσpow,
      show 2*(d+1) = (2*d+1)+1 by omega, pow_succ (n : ℂ) (2*d+1)]
    field_simp [hnC]
  · apply tsum_congr
    intro d
    dsimp only [c, correctionCoeff]
    rw [show 2*d+3-1 = 2*d+2 by omega, neg_pow, ← pow_mul,
      show 4*d+4 = 2*(2*d+2) by omega, hσpow,
      show (4 : ℕ) = 2*2 by omega, hσpow, pow_add (r : ℂ) (2*d) 2]
    field_simp [hnC]
    ring

end DurfeeCCS.Step08
