module

public import DurfeeCCS.Step08.DurfeeContour
public import DurfeeCCS.Step08.MidpointSinh
public import DurfeeCCS.Step08.MinorArcSeries

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The minor-arc bound for the first three radius ranges in Proposition 3.5. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07

theorem norm_pairedLog_minor {r u v : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) (hu : 0 < u)
    (hmin : 16 * u ≤ |v|) (hmax : |v| ≤ Real.pi) (θ : ℝ) :
    ‖pairedLog r θ (verticalPoint u v)‖ ≤
      (Real.pi / 16 + r / (2 * (1 - r))) * (r / u) := by
  let ζ := verticalPoint u v
  have hζ : 0 < ζ.re := by simpa [ζ] using hu
  have hr' : |r| ≤ 1 := by simpa [abs_of_nonneg hr] using hr₁.le
  let f := pairedLogMode r θ ζ
  have hsum := summable_norm_pairedLogMode r θ hr' hζ
  have hden : 32 * u / Real.pi ≤ ‖2 * sinh (ζ / 2)‖ := by
    have h := two_div_pi_mul_abs_im_le_norm_two_mul_sinh_half (z := ζ) (by simpa [ζ] using hmax)
    have hv := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 2 / Real.pi by positivity)
    calc
      _ = (2 / Real.pi) * (16 * u) := by ring
      _ ≤ _ := hv
      _ ≤ _ := by simpa [ζ] using h
  have hhead : ‖f 0‖ ≤ Real.pi * r / (16 * u) := by
    have he : ‖pairedLogCoeff r ζ 0‖ = 2 * r / ‖2 * sinh (ζ / 2)‖ := by
      simpa [abs_of_nonneg hr] using norm_pairedLogCoeff_eq r ζ 0
    change ‖pairedLogMode r θ ζ 0‖ ≤ _
    rw [pairedLogMode, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine (mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)).trans ?_
    rw [he]
    calc
      _ ≤ (2 * r) / (32 * u / Real.pi) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp; ring
  have hpoint (k : ℕ) : ‖f (k + 1)‖ ≤ (r ^ 2 / (2 * u)) * r ^ k := by
    have h := norm_pairedLogMode_le_radius hr θ hζ (k + 1)
    change ‖f (k + 1)‖ ≤ _ at h
    rw [show ζ.re = u from verticalPoint_re u v] at h
    have hk : (2 : ℝ) ≤ (((k + 1 + 1 : ℕ)) : ℝ) := by
      exact_mod_cast (show 2 ≤ k + 1 + 1 by omega)
    have hd : 4 * u ≤ u * (((k + 1 + 1 : ℕ)) : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hk 2) hu.le
      nlinarith only [this]
    refine h.trans ((div_le_div_of_nonneg_left (by positivity) (by positivity) hd).trans_eq ?_)
    rw [show k + 1 + 1 = 2 + k by omega, pow_add]
    field_simp
    ring
  have hg := (summable_geometric_of_lt_one hr hr₁).mul_left (r ^ 2 / (2 * u))
  have hs : Summable (fun k => ‖f (k + 1)‖) := hg.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have ht : (∑' k, ‖f (k + 1)‖) ≤ r ^ 2 / (2 * (1 - r) * u) := by
    refine (hs.tsum_le_tsum hpoint hg).trans_eq ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr₁]
    field_simp
  rw [pairedLog_eq_tsum_mode r θ hr' hζ, ← show f = pairedLogMode r θ ζ from rfl]
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  rw [hsum.tsum_eq_zero_add]
  calc
    _ ≤ Real.pi * r / (16 * u) + r ^ 2 / (2 * (1 - r) * u) := add_le_add hhead ht
    _ = _ := by field_simp

theorem norm_durfeeExponentialMean_minor {r r₀ u v ω : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ r₀) (hr₁ : r₀ < 1) (hu : 0 < u) (hω : r / u ≤ ω)
    (hmin : 16 * u ≤ |v|) (hmax : |v| ≤ Real.pi) :
    ‖durfeeExponentialMean r u v‖ ≤
      (Real.exp ((Real.pi / 16 + r₀ / (2 * (1 - r₀))) * ω) / 2) *
        angularMean (fun θ => ‖pairedLog r θ (verticalPoint u v)‖ ^ 2) := by
  have hr₀' : 0 ≤ r₀ := hr.le.trans hr₀
  have hr' : |r| ≤ 1 := by rw [abs_of_pos hr]; linarith
  have hru : 0 ≤ r / u := div_nonneg hr.le hu.le
  have hω' : 0 ≤ ω := hru.trans hω
  have hratio : r / (2 * (1 - r)) ≤ r₀ / (2 * (1 - r₀)) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    linarith only [hr₀]
  have hp : Continuous (fun θ : ℝ => (v, θ)) := continuous_const.prodMk continuous_id
  have hcont : Continuous (fun θ => pairedLog r θ (verticalPoint u v)) := by
    change Continuous ((fun p : ℝ × ℝ => pairedLog r p.2 (verticalPoint u p.1)) ∘ fun θ => (v, θ))
    exact (continuous_pairedLog_vertical r hr' hu).comp hp
  have hζ : 0 < (verticalPoint u v).re := by simpa using hu
  have hR : 0 ≤ 1 - r := by linarith
  have hR₀ : 0 ≤ 1 - r₀ := by linarith
  have hp₁ : 0 ≤ Real.pi / 16 + r₀ / (2 * (1 - r₀)) := by positivity
  unfold durfeeExponentialMean
  apply norm_angularAverage_exp_sub_one_le hcont
    (angularAverage_pairedLog r hr' hζ) (by positivity)
  intro θ _
  exact (Complex.re_le_norm _).trans ((norm_pairedLog_minor hr.le (hr₀.trans_lt hr₁) hu hmin hmax θ).trans
    (mul_le_mul (add_le_add_right hratio _) hω hru hp₁))

/-- The full minor arc for `r ≤ r₀ < 1` using the exact double squared mean. -/
theorem integral_norm_durfeeExponentialMean_minor {r r₀ u ω : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ r₀) (hr₁ : r₀ < 1) (hu : 0 < u) (hω : r / u ≤ ω) :
    let s := Icc (-Real.pi) Real.pi \ Icc (-(16 * u)) (16 * u)
    (∫ v in s, ‖durfeeExponentialMean r u v‖) ≤
      (Real.pi / (1 - r₀ ^ 2)) * r ^ 2 / u *
        Real.exp ((Real.pi / 16 + r₀ / (2 * (1 - r₀))) * ω) := by
  dsimp only
  let t := Icc (-Real.pi) Real.pi
  let s := t \ Icc (-(16 * u)) (16 * u)
  let F (v : ℝ) := angularMean (fun θ => ‖pairedLog r θ (verticalPoint u v)‖ ^ 2)
  let w := (Real.pi / 16 + r₀ / (2 * (1 - r₀))) * ω
  have hr' : |r| ≤ 1 := by rw [abs_of_pos hr]; linarith
  have hpos (v : ℝ) : 0 ≤ F v := by
    unfold F angularMean
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun _ _ => sq_nonneg _)
  have hF : Continuous F := by
    have hc : Continuous (fun p : ℝ × ℝ => ‖pairedLog r p.2 (verticalPoint u p.1)‖ ^ 2) :=
      (continuous_pairedLog_vertical r hr' hu).norm.pow 2
    unfold F angularMean
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun v θ => ‖pairedLog r θ (verticalPoint u v)‖ ^ 2) hc _ _)
  have hD := (continuous_durfeeExponentialMean hr' hu).norm
  have hFt : IntegrableOn F t := hF.integrableOn_Icc
  have hnt : IntegrableOn (fun v => ‖durfeeExponentialMean r u v‖) t := hD.integrableOn_Icc
  have hs : s ⊆ t := sdiff_subset
  have hM := setIntegral_mono_set hFt (Filter.Eventually.of_forall hpos)
    (Filter.Eventually.of_forall hs)
  have havg : (∫ v in t, F v) = (2 * Real.pi) * angularMean F := by
    rw [angularMean, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [show t = Icc (-Real.pi) Real.pi from rfl, integral_Icc_eq_integral_Ioc]
    field_simp
  have hR : 0 ≤ r₀ := hr.le.trans hr₀
  have hR' : 0 < 1 - r₀ ^ 2 := sub_pos.mpr (pow_lt_one₀ hR hr₁ (by decide))
  have hden : 1 - r₀ ^ 2 ≤ 1 - r ^ 2 :=
    sub_le_sub_left (pow_le_pow_left₀ hr.le hr₀ 2) _
  change (∫ v in s, ‖durfeeExponentialMean r u v‖) ≤ _
  calc
    _ ≤ ∫ v in s, (Real.exp w / 2) * F v := by
      refine setIntegral_mono_on (hnt.mono_set hs) ((hFt.mono_set hs).const_mul _)
        (measurableSet_Icc.diff measurableSet_Icc) (fun v hv => ?_)
      exact norm_durfeeExponentialMean_minor hr hr₀ hr₁ hu hω
        (not_lt.mp (fun h => hv.2 (abs_le.mp h.le))) (abs_le.mpr hv.1)
    _ = (Real.exp w / 2) * (∫ v in s, F v) := integral_const_mul _ _
    _ ≤ (Real.exp w / 2) * ((2 * Real.pi) * angularMean F) := by
      rw [← havg]
      exact mul_le_mul_of_nonneg_left hM (by positivity)
    _ ≤ (Real.exp w / 2) * ((2 * Real.pi) * (r ^ 2 / (u * (1 - r ^ 2)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (double_angularMean_norm_sq_pairedLog_le hr.le (hr₀.trans_lt hr₁) hu) (by positivity))
        (by positivity)
    _ ≤ (Real.exp w / 2) * ((2 * Real.pi) * (r ^ 2 / (u * (1 - r₀ ^ 2)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hu hR')
          (mul_le_mul_of_nonneg_left hden hu.le)) (by positivity)) (by positivity)
    _ = _ := by dsimp only [w]; field_simp

theorem durfee_minor_error_le {n : ℕ} (hn : 0 < n) {r r₀ : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ r₀) (hr₁ : r₀ < 1) :
    let ω := saddleOmega n r
    let u := saddleU n r
    Real.exp ω / (2 * Real.pi) *
      (∫ v in Icc (-Real.pi) Real.pi \ Icc (-(16 * u)) (16 * u),
        ‖durfeeExponentialMean r u v‖) ≤
    saddleAmplitude n r * firstSaddleU r₀ ω := by
  dsimp only
  have hrle : r ≤ 1 := (hr₀.trans_lt hr₁).le
  have hu := saddleU_pos hn hr
  have hω := r_div_saddleU_le_saddleOmega hn hr hrle
  have hminor := integral_norm_durfeeExponentialMean_minor hr hr₀ hr₁ hu hω
  have hC : 0 ≤ Real.pi / (1 - r₀ ^ 2) :=
    div_nonneg Real.pi_pos.le (sub_nonneg.mpr (pow_le_one₀ (hr.le.trans hr₀) hr₁.le))
  refine (mul_le_mul_of_nonneg_left hminor (by positivity)).trans ?_
  refine (saddle_scale_weighted_error_le (μ := Real.pi / 16 + r₀ / (2 * (1 - r₀)))
    hn hr hrle hC).trans_eq ?_
  unfold firstSaddleU
  rw [show -(1 - (Real.pi / 16 + r₀ / (2 * (1 - r₀)))) =
    -(1 - Real.pi / 16 - r₀ / (2 * (1 - r₀))) by ring]
  field_simp

end DurfeeCCS.Step08
