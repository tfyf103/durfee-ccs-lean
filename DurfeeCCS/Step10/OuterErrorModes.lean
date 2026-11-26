module

public import DurfeeCCS.Step10.OuterRho
public import DurfeeCCS.Step10.OuterErrorEndpoints
public import DurfeeCCS.Step10.OuterErrorLattice
import Mathlib.Tactic

/-! Quantitative estimates of the two leading and other low frequencies. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real

private abbrev scale : ℝ := 4 * π ^ 2 / 3

private theorem scale_pos : 0 < scale := by positivity

private theorem scale_le : scale < 13.16 := by
  dsimp only [scale]
  calc
    _ ≤ 4 * (3.141593 : ℝ) ^ 2 / 3 := by gcongr; exact Real.pi_lt_d6.le
    _ < _ := by norm_num

private theorem outerRhoAt_delta_quadratic {h v a : ℝ} :
    let Δ := (outerRhoAt h v a).re ^ 2 - h ^ 2
    Δ * (h ^ 2 + v ^ 2 - a + Δ) = a * h ^ 2 := by
  let ρ := outerRhoAt h v a
  have him := congrArg (fun z : ℝ => z ^ 2) (outerRhoAt_re_mul_im h v a)
  change (ρ.re * ρ.im) ^ 2 = (h * v) ^ 2 at him
  have hre : ρ.re ^ 2 - ρ.im ^ 2 = h ^ 2 + a - v ^ 2 :=
    outerRhoAt_re_sq_sub_im_sq h v a
  change (ρ.re ^ 2 - h ^ 2) * (h ^ 2 + v ^ 2 - a + (ρ.re ^ 2 - h ^ 2)) = a * h ^ 2
  linear_combination ρ.re ^ 2 * hre + him

private theorem outerRhoAt_delta_bounds {h v a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    let Δ := (outerRhoAt h v a).re ^ 2 - h ^ 2
    0 < Δ ∧ Δ ≤ a := by
  dsimp only
  have hR := outerRhoAt_re_gt (t := v) hh ha
  have hpositive : 0 < (outerRhoAt h v a).re ^ 2 - h ^ 2 := by
    rw [sub_pos]
    exact pow_lt_pow_left₀ hR hh.le two_ne_zero
  have hδ := outerRhoAt_re_sq_sub_im_sq h v a
  have him : |(outerRhoAt h v a).im| ≤ |v| := by
    rw [outerRhoAt_im_eq hh ha, abs_div, abs_mul, abs_of_pos hh, abs_of_pos (hh.trans hR),
      div_le_iff₀ (hh.trans hR)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hR.le (abs_nonneg v)
  have him2 := pow_le_pow_left₀ (abs_nonneg _) him 2
  simp only [sq_abs] at him2
  exact ⟨hpositive, by linarith⟩

private theorem outerRhoAt_norm_sq_le {h v a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    ‖outerRhoAt h v a‖ ^ 2 ≤ h ^ 2 + v ^ 2 + a := by
  let ρ := outerRhoAt h v a
  have hΔ := (outerRhoAt_delta_bounds (v := v) hh ha).2
  have hρ := outerRhoAt_re_gt (t := v) hh ha
  have him : |ρ.im| ≤ |v| := by
    dsimp only [ρ]
    rw [outerRhoAt_im_eq hh ha, abs_div, abs_mul, abs_of_pos hh, abs_of_pos (hh.trans hρ),
      div_le_iff₀ (hh.trans hρ)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hρ.le (abs_nonneg v)
  have him2 := pow_le_pow_left₀ (abs_nonneg _) him 2
  simp only [sq_abs] at him2
  rw [Complex.sq_norm, Complex.normSq_apply]
  change ρ.re * ρ.re + ρ.im * ρ.im ≤ _
  linarith

private theorem outerRhoAt_re_le_sqrt {h v a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    (outerRhoAt h v a).re ≤ sqrt (h ^ 2 + a) :=
  Real.le_sqrt_of_sq_le (by linarith [(outerRhoAt_delta_bounds (v := v) hh ha).2])

private theorem outerRho_delta_pi_lower {h : ℝ} (hh : 0 < h) :
    scale / (1 + π ^ 2 / h ^ 2) ≤ (outerRho h π).re ^ 2 - h ^ 2 := by
  let Δ := (outerRho h π).re ^ 2 - h ^ 2
  have hδ : Δ * (h ^ 2 + π ^ 2 - scale + Δ) = scale * h ^ 2 :=
    outerRhoAt_delta_quadratic
  have hB : 0 < Δ ∧ Δ ≤ scale := outerRhoAt_delta_bounds hh scale_pos
  have hm : scale * h ^ 2 ≤ Δ * (h ^ 2 + π ^ 2) := by
    rw [← hδ]
    exact mul_le_mul_of_nonneg_left (by linarith) hB.1.le
  have hn : scale / (1 + π ^ 2 / h ^ 2) = scale * h ^ 2 / (h ^ 2 + π ^ 2) := by
    field_simp
  rw [hn]
  exact (div_le_iff₀ (by positivity)).2 hm

private theorem outerRho_re_pi_gap_lower {h : ℝ} (hh : 0 < h) :
    scale / (h * ((1 + π ^ 2 / h ^ 2) * (1 + sqrt (1 + scale / h ^ 2)))) ≤
      (outerRho h π).re - h := by
  let x := (outerRho h π).re
  have hx : h < x := outerRho_re_gt hh
  have hd := outerRho_delta_pi_lower hh
  have hs : sqrt (h ^ 2 + scale) = h * sqrt (1 + scale / h ^ 2) := by
    calc
      _ = sqrt (h ^ 2 * (1 + scale / h ^ 2)) := by congr 1; field_simp
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hh.le]
  have hxu : x ≤ h * sqrt (1 + scale / h ^ 2) :=
    (outerRhoAt_re_le_sqrt hh scale_pos).trans_eq hs
  calc
    _ = (scale / (1 + π ^ 2 / h ^ 2)) / (h * (1 + sqrt (1 + scale / h ^ 2))) := by
      exact (congrArg (scale / ·) (mul_left_comm h (1 + π ^ 2 / h ^ 2) _)).trans
        (div_div scale (1 + π ^ 2 / h ^ 2) (h * (1 + sqrt (1 + scale / h ^ 2)))).symm
    _ ≤ (x ^ 2 - h ^ 2) / (x + h) := by
      apply div_le_div₀ (by linarith [div_nonneg scale_pos.le (show 0 ≤ 1 + π ^ 2 / h ^ 2 by positivity)]) hd (by linarith)
      linarith [mul_add h 1 (sqrt (1 + scale / h ^ 2))]
    _ = _ := by
      change (x ^ 2 - h ^ 2) / (x + h) = x - h
      rw [div_eq_iff (by linarith : x + h ≠ 0)]
      ring

/-- Positive separation of the leading square root from its real-axis baseline. -/
theorem outerRho_re_pi_gap {h : ℝ} (hh : 8.76 < h) :
    17 * π ^ 2 / (30 * h) < (outerRho h π).re - h := by
  have hh₀ : 0 < h := by linarith
  have hh₂ : (8.76 : ℝ) ^ 2 ≤ h ^ 2 := by gcongr
  have hp : π ≤ 3.142 := pi_lt_d6.le.trans (by norm_num)
  have hp' : π ^ 2 / h ^ 2 ≤ (3.142 : ℝ) ^ 2 / 8.76 ^ 2 := by gcongr
  have ha : scale / h ^ 2 ≤ (13.16 : ℝ) / 8.76 ^ 2 := by gcongr; exact scale_le.le
  have hs : sqrt (1 + scale / h ^ 2) ≤ 1.083 := (Real.sqrt_le_iff).2 (by constructor <;> linarith)
  have hb : (1 + π ^ 2 / h ^ 2) * (1 + sqrt (1 + scale / h ^ 2)) < 40 / 17 := by
    calc
      _ ≤ (1 + (3.142 : ℝ) ^ 2 / 8.76 ^ 2) * (1 + 1.083) := by gcongr
      _ < _ := by norm_num
  apply lt_of_lt_of_le _ (outerRho_re_pi_gap_lower hh₀)
  rw [show 17 * π ^ 2 / (30 * h) = scale / (h * (40 / 17)) by dsimp [scale]; ring]
  apply div_lt_div_of_pos_left scale_pos (by positivity)
  exact mul_lt_mul_of_pos_left hb hh₀

/-- The norm ratio of the two principal-mode roots. -/
theorem outerRho_norm_pi {h : ℝ} (hh : 8.76 < h) : ‖outerRho h π‖ < 1.142 * h := by
  have hh₀ : 0 < h := by linarith
  have hh₂ : (8.76 : ℝ) ^ 2 ≤ h ^ 2 := by gcongr
  have hp : π ^ 2 ≤ (3.142 : ℝ) ^ 2 := by gcongr; exact pi_lt_d6.le.trans (by norm_num)
  have hm := outerRhoAt_norm_sq_le (v := π) hh₀ scale_pos
  change ‖outerRho h π‖ ^ 2 ≤ _ at hm
  apply (sq_lt_sq₀ (norm_nonneg _) (by positivity)).1
  nlinarith [scale_le]

/-- The norm ratio of each nonprincipal root in the low-frequency range. -/
theorem outerRho_norm_low {h v : ℝ} (hv : 3 * π ≤ |v|) (hh : |v| ≤ h) :
    ‖outerRho h v‖ < 1.47 * h := by
  have hh₀ : 0 < h := lt_of_lt_of_le (by positivity : 0 < 3 * π) (hv.trans hh)
  have hv₂ := pow_le_pow_left₀ (abs_nonneg v) hh 2
  have hh₂ := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * π) (hv.trans hh) 2
  rw [sq_abs] at hv₂
  have hm := outerRhoAt_norm_sq_le (v := v) hh₀ scale_pos
  change ‖outerRho h v‖ ^ 2 ≤ _ at hm
  have ha : scale ≤ (4 / 27 : ℝ) * h ^ 2 := by dsimp [scale]; nlinarith
  apply (sq_lt_sq₀ (norm_nonneg _) (by positivity)).1
  nlinarith

private theorem outerRho_re_low_gap_aux {h v : ℝ} (hv : 3 * π ≤ |v|) (hh : |v| ≤ h) :
    13 * π ^ 2 * (v ^ 2 - π ^ 2) / (50 * h ^ 3) <
      (outerRho h π).re - (outerRho h v).re := by
  let x := (outerRho h π).re
  let z := (outerRho h v).re
  let D := x ^ 2 - h ^ 2
  let E := z ^ 2 - h ^ 2
  let B := h ^ 2 + v ^ 2 - scale + D + E
  have hh₀ : 0 < h := lt_of_lt_of_le (by positivity : 0 < 3 * π) (hv.trans hh)
  have hh₂ := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * π) (hv.trans hh) 2
  have hv₂ := pow_le_pow_left₀ (abs_nonneg _) hh 2
  rw [sq_abs] at hv₂
  have hV := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * π) hv 2
  rw [sq_abs] at hV
  have hV₀ : 0 < v ^ 2 - π ^ 2 := by nlinarith [sq_pos_of_pos pi_pos]
  have hD : 0 < D ∧ D ≤ scale := outerRhoAt_delta_bounds hh₀ scale_pos
  have hE : 0 < E ∧ E ≤ scale := outerRhoAt_delta_bounds hh₀ scale_pos
  have ha : scale ≤ (4 / 27 : ℝ) * h ^ 2 := by dsimp [scale]; nlinarith
  have hB : 0 < B := by dsimp [B]; nlinarith [hD.1, hE.1, sq_nonneg v, sq_pos_of_pos hh₀]
  have hBhi : B ≤ (58 / 27 : ℝ) * h ^ 2 := by dsimp [B]; linarith [hD.2, hE.2]
  have hDq : D * (h ^ 2 + π ^ 2 - scale + D) = scale * h ^ 2 :=
    outerRhoAt_delta_quadratic
  have hEq : E * (h ^ 2 + v ^ 2 - scale + E) = scale * h ^ 2 :=
    outerRhoAt_delta_quadratic
  have hsub : (D - E) * B = (v ^ 2 - π ^ 2) * D := by
    dsimp only [B]
    linear_combination hDq - hEq
  have hx : h < x := outerRho_re_gt hh₀
  have hz : h < z := outerRho_re_gt hh₀
  have hsum : 0 < x + z := by linarith
  have hroot : x + z ≤ 2 * 1.072 * h := by
    have hs : sqrt (h ^ 2 + scale) ≤ 1.072 * h := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith [sq_nonneg h]
    have hx' : x ≤ sqrt (h ^ 2 + scale) := outerRhoAt_re_le_sqrt hh₀ scale_pos
    have hz' : z ≤ sqrt (h ^ 2 + scale) := outerRhoAt_re_le_sqrt hh₀ scale_pos
    linarith
  have hDlo : scale / (10 / 9) ≤ D := by
    apply le_trans _ (outerRho_delta_pi_lower hh₀)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hp : π ^ 2 / h ^ 2 ≤ 1 / 9 := (div_le_iff₀ (by positivity)).2 (by nlinarith)
    linarith
  calc
    _ < ((v ^ 2 - π ^ 2) * (scale / (10 / 9))) /
         (((58 / 27 : ℝ) * h ^ 2) * (2 * 1.072 * h)) := by
      have hc : 13 / 50 < (4 / 3 : ℝ) / (10 / 9) / ((58 / 27) * (2 * 1.072)) := by norm_num
      dsimp [scale]
      rw [show 13 * π ^ 2 * (v ^ 2 - π ^ 2) / (50 * h ^ 3) =
        (13 / 50 : ℝ) * (π ^ 2 * (v ^ 2 - π ^ 2) / h ^ 3) by ring,
        show (v ^ 2 - π ^ 2) * (4 * π ^ 2 / 3 / (10 / 9)) /
          (58 / 27 * h ^ 2 * (2 * 1.072 * h)) =
          ((4 / 3 : ℝ) / (10 / 9) / ((58 / 27) * (2 * 1.072))) *
            (π ^ 2 * (v ^ 2 - π ^ 2) / h ^ 3) by ring]
      exact mul_lt_mul_of_pos_right hc (by positivity)
    _ ≤ ((v ^ 2 - π ^ 2) * D) / (B * (x + z)) := by
      apply div_le_div₀ (mul_nonneg hV₀.le hD.1.le) _ (mul_pos hB hsum)
      · gcongr
      · gcongr
    _ = _ := by
      rw [← hsub, mul_comm B (x + z), mul_div_mul_right _ _ hB.ne']
      change (x ^ 2 - h ^ 2 - (z ^ 2 - h ^ 2)) / (x + z) = _
      rw [div_eq_iff hsum.ne']
      ring

theorem outerRho_re_low_gap {h v : ℝ} (hv : 3 * π ≤ |v|) (hh : |v| ≤ h) :
    13 * π ^ 2 * (v ^ 2 - π ^ 2) / (50 * h ^ 3) <
      (outerRho h π).re - (outerRho h v).re :=
  outerRho_re_low_gap_aux hv hh

private theorem outerRhoAt_re_ge_zero (h v a : ℝ) : 0 ≤ (outerRhoAt h v a).re := by
  unfold outerRhoAt
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, Complex.ofReal_im]
  split_ifs <;> simp <;> positivity

private theorem outerRhoAt_re_zero {h v : ℝ} (hh : 0 < h) :
    (outerRhoAt h v 0).re = h := by
  let ζ : ℂ := h + Complex.I * (v : ℂ)
  have hs : outerRhoAt h v 0 ^ 2 = ζ ^ 2 := by rw [outerRhoAt_sq]; simp [ζ]
  have hx : (outerRhoAt h v 0 - ζ) * (outerRhoAt h v 0 + ζ) = 0 := by
    linear_combination hs
  have hp : 0 < (outerRhoAt h v 0 + ζ).re := by
    have hζ : ζ.re = h := by simp [ζ, Complex.mul_re]
    rw [Complex.add_re, hζ]
    exact add_pos_of_nonneg_of_pos (outerRhoAt_re_ge_zero h v 0) hh
  have he := sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right (fun hz => by simp [hz] at hp))
  rw [he]
  simp [ζ, Complex.mul_re]

private theorem outerRhoAt_re_high_le {h v a : ℝ} (hh : 8.76 < h) (hv : h < |v|)
    (ha : 0 ≤ a) (ha' : a ≤ scale) :
    (outerRhoAt h v a).re - h ≤ scale / (2 * h * (2 - scale / h ^ 2)) := by
  have hh₀ : 0 < h := by linarith
  have hh₂ : (8.76 : ℝ) ^ 2 ≤ h ^ 2 := by gcongr
  have ha₂ : scale < h ^ 2 := by linarith [scale_le]
  have hpos : 0 < 2 - scale / h ^ 2 := by
    have hdiv : scale / h ^ 2 < 1 := (div_lt_one (by positivity)).2 ha₂
    linarith
  by_cases ha₀ : a = 0
  · rw [ha₀, outerRhoAt_re_zero hh₀, sub_self]
    exact div_nonneg scale_pos.le (by positivity)
  have haₚ : 0 < a := lt_of_le_of_ne ha (Ne.symm ha₀)
  let x := (outerRhoAt h v a).re
  let D := x ^ 2 - h ^ 2
  have hx : h < x := outerRhoAt_re_gt hh₀ haₚ
  have hD : 0 < D := (outerRhoAt_delta_bounds (v := v) hh₀ haₚ).1
  have hq : D * (h ^ 2 + v ^ 2 - a + D) = a * h ^ 2 := outerRhoAt_delta_quadratic
  have hv₂ := pow_lt_pow_left₀ hv hh₀.le two_ne_zero
  rw [sq_abs] at hv₂
  have hdenom : 2 * h ^ 2 - scale ≤ h ^ 2 + v ^ 2 - a + D := by linarith
  have hDhi : D ≤ scale / (2 - scale / h ^ 2) := by
    apply (le_div_iff₀ hpos).2
    have H : D * (2 * h ^ 2 - scale) ≤ scale * h ^ 2 := by
      exact (mul_le_mul_of_nonneg_left hdenom hD.le).trans
        (hq.le.trans (mul_le_mul_of_nonneg_right ha' (sq_nonneg _)))
    apply le_of_mul_le_mul_right _ (by positivity : 0 < h ^ 2)
    convert H using 1
    field_simp
  calc
    _ = D / (x + h) := by
      change x - h = (x ^ 2 - h ^ 2) / (x + h)
      rw [eq_div_iff (by linarith : x + h ≠ 0)]
      ring
    _ ≤ (scale / (2 - scale / h ^ 2)) / (2 * h) :=
      div_le_div₀ (div_nonneg scale_pos.le hpos.le) hDhi (by positivity) (by linarith)
    _ = _ := by rw [div_div, mul_comm (2 - scale / h ^ 2)]

private theorem outerHighGap_base {h v a : ℝ} (hh : 8.76 < h) (hv : h < |v|)
    (ha : 0 ≤ a) (ha' : a ≤ scale) :
    let P := π ^ 2 / h ^ 2
    let Q := scale / h ^ 2
    1 / ((1 + P) * (1 + sqrt (1 + Q))) - 1 / (2 * (2 - Q)) ≤
      h / scale * ((outerRho h π).re - (outerRhoAt h v a).re) := by
  dsimp only
  have hh₀ : 0 < h := by linarith
  have hlo := outerRho_re_pi_gap_lower hh₀
  have hhi := outerRhoAt_re_high_le hh hv ha ha'
  have H := mul_le_mul_of_nonneg_left (sub_le_sub hlo hhi) (div_nonneg hh₀.le scale_pos.le)
  have hf : h / scale * ((outerRho h π).re - h - ((outerRhoAt h v a).re - h)) =
      h / scale * ((outerRho h π).re - (outerRhoAt h v a).re) := by ring
  rw [hf] at H
  have hscale : scale ≠ 0 := scale_pos.ne'
  convert H using 1
  field_simp

/-- Uniform square-root gap for the high-frequency part of the transform. -/
theorem outerRho_high_gap {h v a : ℝ} (hh : 8.76 < h) (hv : h < |v|)
    (ha : 0 ≤ a) (ha' : a ≤ 4 * π ^ 2 / 3) :
    max 0.152 (1 / 4 - 8.4 / h ^ 2) <
      (3 * h / (4 * π ^ 2)) * ((outerRho h π).re - (outerRhoAt h v a).re) := by
  let P := π ^ 2 / h ^ 2
  let Q := scale / h ^ 2
  let J := 1 / ((1 + P) * (1 + sqrt (1 + Q))) - 1 / (2 * (2 - Q))
  have hJ : J ≤ h / scale * ((outerRho h π).re - (outerRhoAt h v a).re) :=
    outerHighGap_base hh hv ha ha'
  have hh₀ : 0 < h := by linarith
  have hh₂ : (8.76 : ℝ) ^ 2 ≤ h ^ 2 := by gcongr
  have hp₀ : 0 ≤ P := by dsimp [P]; positivity
  have hq₀ : 0 ≤ Q := by dsimp [Q]; positivity
  have hp : π ^ 2 ≤ (3.141593 : ℝ) ^ 2 := by gcongr; exact pi_lt_d6.le
  have hP : P ≤ 0.128616 := by
    calc
      _ ≤ (3.141593 : ℝ) ^ 2 / 8.76 ^ 2 := by
        dsimp [P]
        exact div_le_div₀ (sq_nonneg _) hp (by norm_num) hh₂
      _ ≤ _ := by norm_num
  have hQ : Q ≤ 0.171488 := by
    change (4 * π ^ 2 / 3) / h ^ 2 ≤ _
    calc
      _ ≤ (4 * (3.141593 : ℝ) ^ 2 / 3) / 8.76 ^ 2 := by gcongr
      _ ≤ _ := by norm_num
  have hs : sqrt (1 + Q) ≤ 1.082354 := (Real.sqrt_le_iff).2 (by constructor <;> linarith)
  have hg₁ : (0.152 : ℝ) < J := by
    have H₁ : (1 : ℝ) / ((1 + 0.128616) * (1 + 1.082354)) ≤
        1 / ((1 + P) * (1 + sqrt (1 + Q))) := by gcongr
    have H₂ : (1 : ℝ) / (2 * (2 - Q)) ≤ 1 / (2 * (2 - 0.171488)) := by
      gcongr
    dsimp only [J]
    linarith
  have hz : sqrt (1 + Q) ≤ 1 + Q / 2 := (Real.sqrt_le_iff).2
    ⟨by linarith, by nlinarith [sq_nonneg Q]⟩
  have hrecip₁ : 1 - P ≤ 1 / (1 + P) := by
    apply (le_div_iff₀ (by linarith)).2
    nlinarith [sq_nonneg P]
  have hrecip₂ : 1 / 2 - Q / 8 ≤ 1 / (1 + sqrt (1 + Q)) := by
    calc
      _ ≤ 1 / (2 + Q / 2) := by
        apply (le_div_iff₀ (by linarith)).2
        nlinarith [sq_nonneg Q]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        linarith
  have hrecip : 1 / 2 - P / 2 - Q / 8 ≤ 1 / ((1 + P) * (1 + sqrt (1 + Q))) := by
    rw [show (1 : ℝ) / ((1 + P) * (1 + sqrt (1 + Q))) =
      (1 / (1 + P)) * (1 / (1 + sqrt (1 + Q))) by simp [div_eq_mul_inv, mul_comm]]
    have H := mul_le_mul hrecip₁ hrecip₂ (show 0 ≤ 1 / 2 - Q / 8 by linarith) (by positivity)
    nlinarith [mul_nonneg hp₀ hq₀]
  have hlinear : 1 / (2 * (2 - Q)) = 1 / 4 + Q / (8 * (1 - Q / 2)) := by
    have hden : 2 - Q ≠ 0 := by linarith
    have hden' : 1 - Q / 2 ≠ 0 := by linarith
    field_simp [hden, hden']
    ring
  have hnegcoef : π ^ 2 / 2 + π ^ 2 / 6 + π ^ 2 / (6 * (1 - Q / 2)) < 8.4 := by
    calc
      _ ≤ (3.141593 : ℝ) ^ 2 / 2 + (3.141593 : ℝ) ^ 2 / 6 +
          (3.141593 : ℝ) ^ 2 / (6 * (1 - 0.171488 / 2)) := by gcongr
      _ < _ := by norm_num
  have hg₂ : (1 / 4 : ℝ) - 8.4 / h ^ 2 < J := by
    dsimp only [J]
    rw [hlinear]
    apply lt_of_lt_of_le _ (sub_le_sub_right hrecip _)
    have H := div_lt_div_of_pos_right hnegcoef (by positivity : 0 < h ^ 2)
    have HR : (π ^ 2 / 2 + π ^ 2 / 6 + π ^ 2 / (6 * (1 - Q / 2))) / h ^ 2 =
        P / 2 + Q / 8 + Q / (8 * (1 - Q / 2)) := by
      dsimp only [P, Q, scale]
      field_simp
      ring
    rw [HR] at H
    linarith
  have hg : max (0.152 : ℝ) (1 / 4 - 8.4 / h ^ 2) < J := max_lt hg₁ hg₂
  have he : h / scale = 3 * h / (4 * π ^ 2) := by dsimp only [scale]; ring
  simpa only [he] using hg.trans_le hJ

end DurfeeCCS.Step10
