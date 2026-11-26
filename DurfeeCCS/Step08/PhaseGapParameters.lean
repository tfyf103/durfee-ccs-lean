module

public import DurfeeCCS.Step07.FirstSaddleRadiusBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The parameter and slope bounds for the first saddle region. -/

@[expose] public section

namespace DurfeeCCS.Step08

open MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07
open scoped Interval Real

/-- The angular decay coefficient used in Lemmas 3.3 and 3.4. -/
noncomputable def saddleGamma (r : ℝ) : ℝ := if r ≤ 0.1 then 0.99 else 0.55

noncomputable def saddleSlope (r : ℝ) : ℝ := (saddleS r).im / (saddleS r).re

noncomputable def saddleCurvature (r : ℝ) : ℝ := r / ((1+r^2) * (saddleS r).re^2)

theorem saddleGamma_bounds (r : ℝ) : 0.55 ≤ saddleGamma r ∧ saddleGamma r ≤ 1 := by
  unfold saddleGamma
  split <;> norm_num

theorem saddlePhaseSquare_re_le_sq_half {r : ℝ} (hr : 0 < r) :
    (saddlePhaseSquare r).re ≤ r^2/2 := by
  let f (y : ℝ) := Real.log (1+y^2)/y
  have hf (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) r) : 0 ≤ f y ∧ f y ≤ y := by
    constructor
    · exact div_nonneg (Real.log_nonneg (le_add_of_nonneg_right (sq_nonneg y))) hy.1.le
    · apply (div_le_iff₀ hy.1).mpr
      have hl := Real.log_le_sub_one_of_pos (show 0 < 1+y^2 by positivity)
      change Real.log (1+y^2) ≤ y*y
      nlinarith only [hl]
  have hfi : IntervalIntegrable f volume 0 r := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
    apply ((continuous_id.intervalIntegrable 0 r).1).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := r))]
      with y hy
    simpa only [Real.norm_of_nonneg (hf y hy).1, id_eq] using (hf y hy).2
  rw [(saddlePhaseSquare_integral_components hr).1]
  apply (intervalIntegral.integral_mono_on_of_le_Ioo hr.le hfi
    (continuous_id.intervalIntegrable 0 r) (fun y hy => (hf y ⟨hy.1, hy.2.le⟩).2)).trans_eq
  simp

private theorem integral_arctan_bounds {r : ℝ} (hr : 0 < r) :
    r-r^3/9 ≤ (∫ y in (0 : ℝ)..r, Real.arctan y/y) ∧
      (∫ y in (0 : ℝ)..r, Real.arctan y/y) ≤ r-r^3/9+r^5/25 ∧
      (∫ y in (0 : ℝ)..r, Real.arctan y/y) ≤ r := by
  let f (y : ℝ) := Real.arctan y/y
  have hf (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) r) : 0 ≤ f y ∧ f y ≤ 1 := by
    constructor
    · exact div_nonneg (Real.arctan_nonneg.mpr hy.1.le) hy.1.le
    · change Real.arctan y/y ≤ 1
      rw [div_le_one hy.1]
      have ht := (arctan_taylor_bounds hy.1.le 1).1
      simpa [arctanTaylor, Finset.sum_range_succ, sub_nonneg] using ht
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 r := intervalIntegrable_const
  have hfi : IntervalIntegrable f volume 0 r := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
    apply hc.1.mono' (Real.continuous_arctan.measurable.div measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := r))]
      with y hy
    change ‖f y‖ ≤ 1
    simpa only [Real.norm_of_nonneg (hf y hy).1] using (hf y hy).2
  let p (y : ℝ) := 1-y^2/3
  let q (y : ℝ) := 1-y^2/3+y^4/5
  have hp : IntervalIntegrable p volume 0 r := (by unfold p; fun_prop : Continuous p).intervalIntegrable ..
  have hq : IntervalIntegrable q volume 0 r := (by unfold q; fun_prop : Continuous q).intervalIntegrable ..
  have hpl := intervalIntegral.integral_mono_on_of_le_Ioo hr.le hp hfi (fun y hy => by
    change p y ≤ Real.arctan y/y
    apply (le_div_iff₀ hy.1).mpr
    have he : p y*y = y-y^3/3 := by unfold p; ring
    rw [he]
    exact arctan_cubic_lower hy.1.le)
  have hqu := intervalIntegral.integral_mono_on_of_le_Ioo hr.le hfi hq (fun y hy => by
    change Real.arctan y/y ≤ q y
    apply (div_le_iff₀ hy.1).mpr
    have he : q y*y = y-y^3/3+y^5/5 := by unfold q; ring
    rw [he]
    have ht := (arctan_taylor_bounds hy.1.le 3).1
    norm_num [arctanTaylor, Finset.sum_range_succ] at ht
    linarith)
  have hcu := intervalIntegral.integral_mono_on_of_le_Ioo hr.le hfi hc (fun y hy =>
    (hf y ⟨hy.1, hy.2.le⟩).2)
  have hpi : (∫ y in (0 : ℝ)..r, p y) = r-r^3/9 := by
    have hd (y : ℝ) : HasDerivAt (fun t : ℝ => t-t^3/9) (p y) y := by
      have h := hasDerivAt_id y
      convert h.sub ((h.pow 3).div_const 9) using 1
      · rfl
      · norm_num [p, id]
        ring
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) hp
  have hqi : (∫ y in (0 : ℝ)..r, q y) = r-r^3/9+r^5/25 := by
    have hd (y : ℝ) : HasDerivAt (fun t : ℝ => t-t^3/9+t^5/25) (q y) y := by
      have h := hasDerivAt_id y
      convert (h.sub ((h.pow 3).div_const 9)).add ((h.pow 5).div_const 25) using 1
      · rfl
      · norm_num [q, id]
        ring
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) hq
  rw [hpi] at hpl
  rw [hqi] at hqu
  exact ⟨hpl, hqu, by simpa using hcu⟩

theorem saddlePhaseSquare_im_le_twice {r : ℝ} (hr : 0 < r) :
    (saddlePhaseSquare r).im ≤ 2*r := by
  rw [(saddlePhaseSquare_integral_components hr).2]
  linarith only [(integral_arctan_bounds hr).2.2]

theorem saddleCurvature_bounds {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    1 / ((1+r^2)*(1+0.282*r)) ≤ saddleCurvature r ∧
      saddleCurvature r ≤ 1 ∧ 0.39 < saddleCurvature r := by
  let a := (saddleS r).re
  have hs : r ≤ a^2 ∧ a^2 ≤ r*(1+0.282*r) ∧ _ := firstSaddle_coordinates_bounds hr hr₁
  have ha2 : 0 < a^2 := hr.trans_le hs.1
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  have h₀ : 0 < (1+r^2)*(1+0.282*r) := by positivity
  have h₁ : 0 < (1+r^2)*a^2 := by positivity
  change 1 / ((1+r^2)*(1+0.282*r)) ≤ r/((1+r^2)*a^2) ∧
    r/((1+r^2)*a^2) ≤ 1 ∧ 0.39 < r/((1+r^2)*a^2)
  have hlow : 1 / ((1+r^2)*(1+0.282*r)) ≤ r/((1+r^2)*a^2) := by
    exact (div_le_div_iff₀ h₀ h₁).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left hs.2.1 (show 0 ≤ 1+r^2 by positivity)])
  refine ⟨hlow, (div_le_one h₁).mpr ?_, lt_of_lt_of_le ?_ hlow⟩
  · exact hs.1.trans (by nlinarith only [mul_nonneg (sq_nonneg r) (sq_nonneg a)])
  · rw [lt_div_iff₀ h₀]
    have hh : (1+r^2)*(1+0.282*r) ≤ 2*1.282 := by
      apply mul_le_mul (by nlinarith only [pow_le_one₀ hr.le hr₁ (n := 2)])
        (by linarith only [hr₁]) (by positivity) (by norm_num)
    linarith only [hh]

/-- The slope inequalities immediately preceding (28). -/
theorem saddleSlope_curvature_bounds {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    1 ≤ saddleSlope r^2+r*saddleCurvature r ∧
      0 ≤ saddleSlope r-saddleCurvature r ∧
      saddleGamma r ≤ 1-saddleSlope r+saddleCurvature r := by
  let a := (saddleS r).re
  let b := (saddleS r).im
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have har : r ≤ a^2 := (firstSaddle_coordinates_bounds hr hr₁).1
  have hD : 0 < 1+r^2 := by positivity
  have hrr := pow_le_one₀ hr.le hr₁ (n := 2)
  have hre : a^2-b^2 ≤ r^2/2 := by
    have hs := congrArg Complex.re (saddleS_sq r)
    rw [pow_two, Complex.mul_re, ← pow_two, ← pow_two] at hs
    change a^2-b^2 = _ at hs
    rw [hs]
    exact saddlePhaseSquare_re_le_sq_half hr
  obtain ⟨_, him⟩ := saddleS_components_eq hr
  change 2*a*b = _ at him
  have hab : a*b = ∫ y in (0 : ℝ)..r, Real.arctan y/y := by linarith only [him]
  obtain ⟨hab₁, hab₂, hab₃⟩ := integral_arctan_bounds hr
  rw [← hab] at hab₁ hab₂ hab₃
  have hρk : saddleSlope r - saddleCurvature r = (a*b-r/(1+r^2))/a^2 := by
    unfold saddleSlope saddleCurvature
    change b/a-r/((1+r^2)*a^2) = _
    field_simp
  have hlo : r/(1+r^2) ≤ a*b := by
    apply (div_le_iff₀ hD).mpr
    have hpol : r ≤ (r-r^3/9)*(1+r^2) := by
      have hh := mul_le_mul_of_nonneg_left hrr (show 0 ≤ r ^ 3 by positivity)
      nlinarith only [hh, show 0 ≤ r^3 by positivity]
    exact hpol.trans (mul_le_mul_of_nonneg_right hab₁ hD.le)
  constructor
  · have H : saddleSlope r^2+r*saddleCurvature r = (b^2+r^2/(1+r^2))/a^2 := by
      unfold saddleSlope saddleCurvature
      change (b/a)^2+r*(r/((1+r^2)*a^2)) = _
      field_simp
    rw [H, le_div_iff₀ ha2, one_mul]
    have hrD := (div_le_div_of_nonneg_left (sq_nonneg r) hD
      (show 1+r^2 ≤ 2 by linarith only [hrr]))
    linarith only [hre, hrD]
  refine ⟨by rw [hρk]; exact div_nonneg (sub_nonneg.mpr hlo) ha2.le, ?_⟩
  have hr1 : 0 ≤ r^2/(1+r^2) - r^2/9+r^4/25 := by
    have h := div_le_div_of_nonneg_left (sq_nonneg r) hD
      (show 1+r^2 ≤ 9 by linarith only [hrr])
    linarith only [h, show 0 ≤ r^4/25 by positivity]
  have hu : saddleSlope r - saddleCurvature r ≤ r^2/(1+r^2)-r^2/9+r^4/25 := by
    rw [hρk, div_le_iff₀ ha2]
    have hp : (r-r^3/9+r^5/25)-r/(1+r^2) =
        r*(r^2/(1+r^2)-r^2/9+r^4/25) := by field_simp; ring
    calc
      _ ≤ _ := sub_le_sub_right hab₂ _
      _ = _ := hp
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_right har hr1
  have H : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t/(1+t)-t/9+t^2/25 ≤ 193/450 := by
    intro t ht ht₁
    have he : 193/450 - (t/(1+t)-t/9+t^2/25) =
      (1-t)*(1/(2*(1+t))-1/9+(1+t)/25) := by field_simp; ring
    have hh : (1 : ℝ)/9 ≤ 1/(2*(1+t)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    linarith only [he, mul_nonneg (sub_nonneg.mpr ht₁)
      (show 0 ≤ 1/(2*(1+t))-1/9+(1+t)/25 by linarith only [hh, show 0 ≤ (1+t)/25 by positivity])]
  unfold saddleGamma
  split_ifs with hs
  · have hR := div_le_self (sq_nonneg r) (le_add_of_nonneg_right (sq_nonneg r))
    have ht := mul_le_mul_of_nonneg_right hrr (sq_nonneg r)
    have hsmall := (sq_le_sq₀ hr.le (by norm_num : (0 : ℝ) ≤ 0.1)).2 hs
    nlinarith only [hu, hR, ht, hsmall, sq_nonneg r]
  · have hh := H (r^2) (sq_nonneg r) hrr
    rw [← pow_mul] at hh
    linarith only [hu, hh]

/-- The frequency and amplitude estimates in (24). -/
theorem saddle_frequency_amplitude_lower {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (hr₁ : r ≤ 1) (hfreq : 4 * Real.pi ≤ Real.sqrt (n*r)) :
    let ω := (saddleS r).re * Real.sqrt n
    4*Real.pi ≤ ω ∧ 2*Real.exp (2*ω)/(3*Real.pi*n) ≤ saddleAmplitude n r := by
  let a := (saddleS r).re
  have hs := firstSaddle_coordinates_bounds hr hr₁
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  have har : r ≤ a^2 := hs.1
  have hnC : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsa : Real.sqrt r ≤ a := by
    rw [Real.sqrt_le_iff]
    exact ⟨ha.le, har⟩
  constructor
  · refine hfreq.trans ?_
    rw [Real.sqrt_mul (by positivity)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsa (Real.sqrt_nonneg n)
  · have hRoot : (4/3 : ℝ)*Real.sqrt r ≤ ‖saddleS r‖ := by
      apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
      rw [mul_pow, Real.sq_sqrt hr.le]
      linarith only [hs.2.2.2.2]
    have hRpow : 1 ≤ (1+r^2)^(1/4 : ℝ) := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
        (le_add_of_nonneg_right (sq_nonneg r)) (by norm_num : (0 : ℝ) ≤ 1/4)
    have hmul : (4/3 : ℝ)*Real.sqrt r ≤ ‖saddleS r‖*(1+r^2)^(1/4 : ℝ) :=
      hRoot.trans (le_mul_of_one_le_right (norm_nonneg _) hRpow)
    change 2*Real.exp (2*(a*Real.sqrt n))/(3*Real.pi*n) ≤ saddleAmplitude n r
    unfold saddleAmplitude
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := mul_le_mul_of_nonneg_right hmul
      (show 0 ≤ 3*Real.pi*n*Real.exp (2*(a*Real.sqrt n)) by positivity)
    change _ ≤ _
    rw [show 2 * (saddleS r).re * Real.sqrt (n : ℝ) = 2*(a*Real.sqrt n) by dsimp [a]; ring]
    linear_combination hh

/-- The prefactor bounds used to start the proof of Lemma 3.4. -/
theorem saddle_norm_prefactor_bounds {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    let s := saddleS r
    let a := s.re
    ‖s‖ < Real.sqrt 2*a ∧ 4*r/3 ≤ a*‖s‖ ∧ r/(a*‖s‖) ≤ 0.75 ∧
      2*r/(a*‖s‖*Real.sqrt (1+r^2)) ≤ 1.5 := by
  let s := saddleS r
  let a := s.re
  change ‖s‖ < Real.sqrt 2*a ∧ 4*r/3 ≤ a*‖s‖ ∧ r/(a*‖s‖) ≤ 0.75 ∧
    2*r/(a*‖s‖*Real.sqrt (1+r^2)) ≤ 1.5
  obtain ⟨hb, hba⟩ := saddleS_components hr
  have ha : 0 < a := hb.trans hba
  have hs : 0 < ‖s‖ := ha.trans_le (Complex.re_le_norm s)
  have hcoord : r ≤ a^2 ∧ a^2 ≤ r*(1+0.282*r) ∧ _ := firstSaddle_coordinates_bounds hr hr₁
  have hab : 4*r/3 ≤ a*‖s‖ := by
    rw [← sq_le_sq₀ (by positivity : 0 ≤ 4*r/3) (by positivity : 0 ≤ a*‖s‖), mul_pow]
    have hsq : 16*r/9 ≤ ‖s‖^2 := hcoord.2.2.2.2
    have h := mul_le_mul hcoord.1 hsq (by positivity : 0 ≤ 16*r/9) (sq_nonneg a)
    nlinarith only [h]
  have hR : 1 ≤ Real.sqrt (1+r^2) := by
    simpa using Real.sqrt_le_sqrt (le_add_of_nonneg_right (a := (1 : ℝ)) (sq_nonneg r))
  refine ⟨?_, hab, (div_le_iff₀ (by positivity)).mpr (by linarith only [hab]), ?_⟩
  · rw [← sq_lt_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (by norm_num)]
    have hba₂ := (sq_lt_sq₀ hb.le ha.le).mpr hba
    linarith only [Complex.sq_norm_sub_sq_re s, hba₂]
  · apply (div_le_iff₀ (by positivity)).mpr
    have h := le_mul_of_one_le_right (show 0 ≤ a*‖s‖ by positivity) hR
    linarith only [hab, h]

/-- The real part and norm of the coefficient in the central exponential model. -/
theorem saddle_model_coefficient_bounds {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    let s := saddleS r
    let A := 2*((r : ℂ)*Complex.I/(1+(r : ℂ)*Complex.I))/((s.re : ℂ)*s)
    saddleGamma r ≤ A.re ∧ ‖A‖ ≤ 1.5 := by
  let s := saddleS r
  let a := s.re
  let b := s.im
  let ρ := saddleSlope r
  let κ := saddleCurvature r
  let A : ℂ := 2*((r : ℂ)*Complex.I/(1+(r : ℂ)*Complex.I))/((a : ℂ)*s)
  obtain ⟨hb, hba⟩ := saddleS_components hr
  have ha : 0 < a := hb.trans hba
  have hκ : 0 ≤ κ := (lt_trans (by norm_num) (saddleCurvature_bounds hr hr₁).2.2).le
  have hbase : Complex.normSq (1+(r : ℂ)*Complex.I) = 1+r^2 := by
    rw [Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hA_re : A.re = 2*κ*(r+ρ)/(1+ρ^2) := by
    unfold A ρ κ saddleSlope saddleCurvature
    change _ = 2*(r/((1+r^2)*a^2))*(r+b/a)/(1+(b/a)^2)
    simp [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, hbase]
    rw [Complex.normSq_apply s]
    change 2*(r*r/(1+r^2))*(a*a)/(a*a*(a*a+b*b))+2*(r/(1+r^2))*(a*b)/(a*a*(a*a+b*b)) = _
    have hρ : (1 + (b/a)^2) ≠ 0 := by positivity
    field_simp
  change saddleGamma r ≤ A.re ∧ ‖A‖ ≤ 1.5
  constructor
  · rw [hA_re, le_div_iff₀ (by positivity)]
    obtain ⟨h₁, h₂, h₃⟩ := saddleSlope_curvature_bounds hr hr₁
    have hθ : 2*ρ ≤ 1+ρ^2 := by nlinarith only [sq_nonneg (ρ-1)]
    have h₄ := mul_le_mul_of_nonneg_left hθ h₂
    have h₅ := mul_le_mul_of_nonneg_right h₃ (show 0 ≤ 1+ρ^2 by positivity)
    nlinarith only [h₁,h₄,h₅,mul_nonneg hr.le hκ]
  · unfold A
    have hNorm : ‖1+(r : ℂ)*Complex.I‖ = Real.sqrt (1+r^2) := by rw [Complex.norm_def, hbase]
    simp only [norm_div, norm_mul, Complex.norm_I, Complex.norm_of_nonneg hr.le,
      Complex.norm_of_nonneg ha.le, hNorm, mul_one]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hR := (saddle_norm_prefactor_bounds hr hr₁).2.2.2
    rw [← mul_div_assoc, div_div, mul_comm (Real.sqrt (1+r^2))]
    exact hR

end DurfeeCCS.Step08
