module

public import DurfeeCCS.Step08.PhaseGap
import DurfeeCCS.Step07.FirstSaddleRadiusBound
import DurfeeCCS.Step07.TrigonometricBounds
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Local lower bounds on the phase gap for the first integral in (41). -/

@[expose] public section

namespace DurfeeCCS.Step08

private theorem saddleSlope_interval {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    0.718 ≤ saddleSlope r ∧ saddleSlope r ≤ 1 := by
  obtain ⟨_, _, hlo, hhi, _⟩ := Step07.firstSaddle_coordinates_bounds hr hr₁
  change 1 - 0.282 * r ≤ saddleSlope r at hlo
  exact ⟨by linarith only [hlo, hr₁], hhi⟩

/-- The quadratic lower bound on the main rectangle when estimating (41). -/
theorem saddleGap_rectangle {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hη₁ : 1 / 4 ≤ η) (hη₂ : η ≤ 2) (hθ : |θ| ≤ Real.pi / 3) :
    0.2 * (η - saddleSlope r) ^ 2 + 0.082 * θ ^ 2 ≤ saddleGap r θ η := by
  let ψ := 1 - Real.cos θ
  let ρ := saddleSlope r
  let κ := saddleCurvature r
  have hη : 0 ≤ η := by linarith only [hη₁]
  have hθ' : |θ| ≤ Real.pi / 2 := by linarith only [hθ, Real.pi_pos]
  have hgap := (saddleG_gap_main hr hr₁ hθ' hη).2
  change ((η - ρ) ^ 2 + r * κ * ψ * (2 - ψ) + 2 * κ * η * ψ) / (1 + η ^ 2) ≤
    saddleGap r θ η at hgap
  have hκ : 0.39 ≤ κ := (saddleCurvature_bounds hr hr₁).2.2.le
  have hκ₀ : 0 ≤ κ := by linarith only [hκ]
  have hψ : 0 ≤ ψ := sub_nonneg.mpr (Real.cos_le_one θ)
  have hψ' : ψ ≤ 1 := by
    have hc := Real.cos_nonneg_of_mem_Icc (abs_le.mp hθ')
    dsimp [ψ]
    linarith only [hc]
  have hden : 0 < 1 + η ^ 2 := by positivity
  have hden₅ : 1 + η ^ 2 ≤ 5 := by
    nlinarith only [pow_le_pow_left₀ hη hη₂ 2]
  have hbase : 0.2 * (η - ρ) ^ 2 ≤ (η - ρ) ^ 2 / (1 + η ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_left hden₅ (show 0 ≤ 0.2 * (η - ρ) ^ 2 by positivity)
    nlinarith only [h]
  have hηratio : 8 / 17 ≤ 2 * η / (1 + η ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    have h := mul_nonneg (show 0 ≤ 4 * η - 1 by linarith only [hη₁])
      (show 0 ≤ 4 - η by linarith only [hη₂])
    nlinarith only [h]
  have hκratio : (0.39 : ℝ) * (8 / 17) ≤ κ * (2 * η / (1 + η ^ 2)) :=
    mul_le_mul hκ hηratio (by norm_num) hκ₀
  have hang : 0.082 * θ ^ 2 ≤ κ * (2 * η / (1 + η ^ 2)) * ψ := by
    have hψθ : (0.45 : ℝ) * θ ^ 2 ≤ ψ := Step07.cosine_gap_on_small_angles hθ
    have h := mul_le_mul hκratio hψθ (by positivity) (by positivity)
    nlinarith only [h, sq_nonneg θ]
  have hmiddle : 0 ≤ r * κ * ψ * (2 - ψ) / (1 + η ^ 2) :=
    div_nonneg (mul_nonneg (by positivity) (by linarith only [hψ'])) hden.le
  have hrearrange : (2 * κ * η * ψ) / (1 + η ^ 2) = κ * (2 * η / (1 + η ^ 2)) * ψ := by
    ring
  refine le_trans ?_ hgap
  rw [add_div, add_div, hrearrange]
  linarith only [hbase, hang, hmiddle]

/-- The gap below the rectangle in the axial direction. -/
theorem saddleGap_small_eta {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hη : 0 ≤ η)
    (hη₁ : η ≤ 1 / 4) : 0.206 ≤ saddleGap r θ η := by
  have hlo := (saddleSlope_interval hr hr₁).1
  have hs : (0.468 : ℝ) ≤ saddleSlope r - η := by linarith only [hlo, hη₁]
  have hsq : (0.468 : ℝ) ^ 2 ≤ (saddleSlope r - η) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hs 2
  have hηsq := pow_le_pow_left₀ hη hη₁ 2
  refine le_trans ?_ (saddleG_gap_all hr hr₁ hη)
  apply (le_div_iff₀ (show 0 < 1 + η ^ 2 by positivity)).mpr
  nlinarith only [hsq, hηsq]

/-- The angular complement of the central rectangle. -/
theorem saddleGap_outer_angles {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hη : 0 ≤ η)
    (hθ₁ : Real.pi / 3 ≤ |θ|) (hθ₂ : |θ| ≤ Real.pi) :
    0.275 ≤ saddleGap r θ η := by
  by_cases hcentral : |θ| ≤ Real.pi / 2
  · have hc : Real.cos θ ≤ 1 / 2 := by
      rw [← Real.cos_abs θ, ← Real.cos_pi_div_three]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hθ₂ hθ₁
    have hψ : (0.5 : ℝ) ≤ 1 - Real.cos θ := by linarith only [hc]
    have hγ := (saddleGamma_bounds r).1
    have h := mul_le_mul hγ hψ (by norm_num) (by positivity : 0 ≤ saddleGamma r)
    calc
      (0.275 : ℝ) = 0.55 * 0.5 := by norm_num
      _ ≤ _ := h.trans ((saddleG_gap_main hr hr₁ hcentral hη).1.trans
        (saddleG_gap_main hr hr₁ hcentral hη).2)
  · have h := saddleG_gap_opposite hr hr₁ (lt_of_not_ge hcentral) hθ₂ hη
    linarith only [h, hr₁]

/-- The slope bound improves the global estimate on all upper axial subregions. -/
theorem saddleGap_one_sub_eta {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hη : 1 ≤ η) :
    (η - 1) ^ 2 / (1 + η ^ 2) ≤ saddleGap r θ η := by
  refine le_trans ?_ (saddleG_gap_all hr hr₁ (by linarith only [hη]))
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine pow_le_pow_left₀ (sub_nonneg.mpr hη) ?_ 2
  exact sub_le_sub_left (saddleSlope_interval hr hr₁).2 η

/-- The lower gap on the axial subregion 2 ≤ η ≤ 4. -/
theorem saddleGap_eta_two_to_four {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hη₁ : 2 ≤ η) (hη₂ : η ≤ 4) : η / 10 ≤ saddleGap r θ η := by
  refine le_trans ?_ (saddleGap_one_sub_eta hr hr₁ (by linarith only [hη₁]))
  apply (le_div_iff₀ (show 0 < 1 + η ^ 2 by positivity)).mpr
  have hηsq := mul_nonneg (show 0 ≤ η by linarith only [hη₁]) (sub_nonneg.mpr hη₂)
  have h := mul_nonneg (show 0 ≤ η - 2 by linarith only [hη₁])
    (show 0 ≤ -η ^ 2 + 8 * η - 5 by nlinarith only [hη₁, hηsq])
  nlinarith only [h]

/-- The lower gap on the axial subregion 4 ≤ η ≤ 8, also valid beyond it. -/
theorem saddleGap_eta_ge_four {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hη : 4 ≤ η) :
    9 / 17 ≤ saddleGap r θ η := by
  refine le_trans ?_ (saddleGap_one_sub_eta hr hr₁ (by linarith only [hη]))
  apply (le_div_iff₀ (show 0 < 1 + η ^ 2 by positivity)).mpr
  have h := mul_nonneg (show 0 ≤ η - 4 by linarith only [hη])
    (show 0 ≤ 4 * η - 1 by linarith only [hη])
  nlinarith only [h]

/-- The lower gap on the axial subregion 8 ≤ η ≤ 16, also valid beyond it. -/
theorem saddleGap_eta_ge_eight {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hη : 8 ≤ η) :
    49 / 65 ≤ saddleGap r θ η := by
  refine le_trans ?_ (saddleGap_one_sub_eta hr hr₁ (by linarith only [hη]))
  apply (le_div_iff₀ (show 0 < 1 + η ^ 2 by positivity)).mpr
  have h := mul_nonneg (show 0 ≤ η - 8 by linarith only [hη])
    (show 0 ≤ 8 * η - 1 by linarith only [hη])
  nlinarith only [h]

/-- The quadratic angular bound obtained from the sine chord bound. -/
theorem cosine_gap_on_semicircle {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    2 * θ ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos θ := by
  have hhalf : |θ| / 2 ≤ Real.pi / 2 := by linarith only [hθ]
  have hsin := Real.mul_le_sin (show 0 ≤ |θ| / 2 by positivity) hhalf
  have hsq := pow_le_pow_left₀ (show 0 ≤ 2 / Real.pi * (|θ| / 2) by positivity) hsin 2
  have hdouble := Real.cos_two_mul (|θ| / 2)
  rw [show 2 * (|θ| / 2) = |θ| by ring, Real.cos_abs] at hdouble
  have hcircle := Real.sin_sq_add_cos_sq (|θ| / 2)
  calc
    _ = 2 * (2 / Real.pi * (|θ| / 2)) ^ 2 := by rw [← sq_abs θ]; ring
    _ ≤ 2 * Real.sin (|θ| / 2) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = _ := by linarith only [hdouble, hcircle]

/-- The Case 1 central-region estimate follows by averaging (25) and (27). -/
theorem saddleGap_central_eta_le_three {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hη : 0 ≤ η) (hη₁ : η ≤ 3) (hθ : |θ| ≤ Real.pi / 2) :
    (η - saddleSlope r) ^ 2 / 20 + 0.55 * θ ^ 2 / Real.pi ^ 2 ≤ saddleGap r θ η := by
  have hden : 1 + η ^ 2 ≤ 10 := by nlinarith only [pow_le_pow_left₀ hη hη₁ 2]
  have hax : 2 * ((η - saddleSlope r) ^ 2 / 20) ≤ saddleGap r θ η := by
    calc
      _ = (η - saddleSlope r) ^ 2 / 10 := by ring
      _ ≤ (η - saddleSlope r) ^ 2 / (1 + η ^ 2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
      _ ≤ _ := saddleG_gap_all hr hr₁ hη
  have hang : 2 * (0.55 * θ ^ 2 / Real.pi ^ 2) ≤ saddleGap r θ η := by
    have hcos := cosine_gap_on_semicircle (show |θ| ≤ Real.pi by linarith only [hθ, Real.pi_pos])
    calc
      _ = 0.55 * (2 * θ ^ 2 / Real.pi ^ 2) := by ring
      _ ≤ 0.55 * (1 - Real.cos θ) := mul_le_mul_of_nonneg_left hcos (by norm_num)
      _ ≤ saddleGamma r * (1 - Real.cos θ) :=
        mul_le_mul_of_nonneg_right (saddleGamma_bounds r).1 (sub_nonneg.mpr (Real.cos_le_one _))
      _ ≤ _ := (saddleG_gap_main hr hr₁ hθ hη).1.trans (saddleG_gap_main hr hr₁ hθ hη).2
  linarith only [hax, hang]

/-- The Case 1 opposite-region estimate with a uniform upper bound on the radius. -/
theorem saddleGap_opposite_of_radius_le {r r₀ θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hr₀ : r ≤ r₀) (hη : 0 ≤ η) (hθ₁ : Real.pi / 2 < |θ|) (hθ₂ : |θ| ≤ Real.pi) :
    1 - r₀ / 2 ≤ saddleGap r θ η := by
  have h := saddleG_gap_opposite hr hr₁ hθ₁ hθ₂ hη
  linarith only [hr₀, h]

/-- The Case 1 lower gap on the large axial interval, including its endpoints. -/
theorem saddleGap_eta_ge_three {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hη : 3 ≤ η) :
    0.4 ≤ saddleGap r θ η := by
  refine le_trans ?_ (saddleGap_one_sub_eta hr hr₁ (by linarith only [hη]))
  apply (le_div_iff₀ (show 0 < 1 + η ^ 2 by positivity)).mpr
  have h := mul_nonneg (show 0 ≤ η - 3 by linarith only [hη])
    (show 0 ≤ 3 * η - 1 by linarith only [hη])
  nlinarith only [h]

private theorem saddle_log_error_on_axial_interval {δ : ℂ} {η η₀ s e C : ℝ}
    (hδ : ‖δ‖ ≤ 0.51 + 0.69 * (1 + Real.sqrt (1 + η ^ 2)))
    (hη : 0 ≤ η) (hη₀ : η ≤ η₀)
    (hs : 0 ≤ s) (hsq₀ : 1 + η₀ ^ 2 ≤ s ^ 2) (he : 0.51 + 0.69 * (1 + s) ≤ e)
    (hC : Real.exp e - 1 < C) : Real.exp ‖δ‖ - 1 < C := by
  have hsq := pow_le_pow_left₀ hη hη₀ 2
  have hS : Real.sqrt (1 + η ^ 2) ≤ s := (Real.sqrt_le_left hs).mpr (by linarith only [hsq, hsq₀])
  have hb : ‖δ‖ ≤ e := by linarith only [hδ, hS, he]
  exact (sub_le_sub_right (Real.exp_le_exp.mpr hb) 1).trans_lt hC

/-- Exponential remainder on the lowest axial interval, using (45). -/
theorem saddle_log_error_small_eta {δ : ℂ} {η : ℝ}
    (hδ : ‖δ‖ ≤ 0.51 + 0.69 * (1 + Real.sqrt (1 + η ^ 2)))
    (hη : 0 ≤ η) (hη₀ : η ≤ 1 / 4) :
    Real.exp ‖δ‖ - 1 < 6 :=
  saddle_log_error_on_axial_interval (s := 1.031) (e := 1.912) hδ hη hη₀
    (by norm_num) (by norm_num) (by norm_num) (by dyadic_interval +kernel [prec := 40])

/-- Exponential remainder on the angular complement of the rectangle, using (45). -/
theorem saddle_log_error_eta_le_two {δ : ℂ} {η : ℝ}
    (hδ : ‖δ‖ ≤ 0.51 + 0.69 * (1 + Real.sqrt (1 + η ^ 2)))
    (hη : 0 ≤ η) (hη₀ : η ≤ 2) :
    Real.exp ‖δ‖ - 1 < 15 :=
  saddle_log_error_on_axial_interval (s := 2.237) (e := 2.744) hδ hη hη₀
    (by norm_num) (by norm_num) (by norm_num) (by dyadic_interval +kernel [prec := 40])

/-- Exponential remainder on the intermediate axial interval, using (45). -/
theorem saddle_log_error_eta_ge_two {δ : ℂ} {η : ℝ}
    (hδ : ‖δ‖ ≤ 0.51 + 0.69 * (1 + Real.sqrt (1 + η ^ 2))) (hη : 2 ≤ η) :
    Real.exp ‖δ‖ - 1 < Real.exp (1.38 + 0.69 * η) := by
  have hs : Real.sqrt (1 + η ^ 2) ≤ η + 1 / 4 := by
    apply (Real.sqrt_le_left (by linarith only [hη] : 0 ≤ η + 1 / 4)).mpr
    nlinarith only [hη]
  have hb : ‖δ‖ ≤ 1.38 + 0.69 * η := by linarith only [hδ, hs]
  calc
    _ < Real.exp ‖δ‖ := by linarith
    _ ≤ _ := Real.exp_le_exp.mpr hb

/-- Exponential remainder through the endpoint eight, using (45). -/
theorem saddle_log_error_eta_le_eight {δ : ℂ} {η : ℝ}
    (hδ : ‖δ‖ ≤ 0.51 + 0.69 * (1 + Real.sqrt (1 + η ^ 2)))
    (hη : 0 ≤ η) (hη₀ : η ≤ 8) :
    Real.exp ‖δ‖ - 1 < 900 :=
  saddle_log_error_on_axial_interval (s := 8.063) (e := 6.764) hδ hη hη₀
    (by norm_num) (by norm_num) (by norm_num) (by dyadic_interval +kernel [prec := 40])

/-- Exponential remainder through the endpoint sixteen, using (45). -/
theorem saddle_log_error_eta_le_sixteen {δ : ℂ} {η : ℝ}
    (hδ : ‖δ‖ ≤ 0.51 + 0.69 * (1 + Real.sqrt (1 + η ^ 2)))
    (hη : 0 ≤ η) (hη₀ : η ≤ 16) :
    Real.exp ‖δ‖ - 1 < 220000 :=
  saddle_log_error_on_axial_interval (s := 16.032) (e := 12.263) hδ hη hη₀
    (by norm_num) (by norm_num) (by norm_num) (by dyadic_interval +kernel [prec := 40])

end DurfeeCCS.Step08
