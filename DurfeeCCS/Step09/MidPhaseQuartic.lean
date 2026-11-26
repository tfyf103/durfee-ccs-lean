module

public import DurfeeCCS.Step09.MidPhaseSymmetry
public import DurfeeCCS.Step08.PhaseGapExpansion
public import DurfeeCCS.Step08.SaddleBesselModel
public import DurfeeCCS.Step07.TrigonometricBounds

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The fourth-order phase remainder in (57). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08
open scoped ComplexConjugate

def midQuarticConstant (h : ℝ) : ℝ := if h ≤ 3 / 4 then 0.426 else 0.547

theorem norm_midPhase_log_remainder {r χ : ℝ} (hr : 1 ≤ r) (hψ : 1 - Real.cos χ < 1) :
    let ψ := 1 - Real.cos χ
    ‖saddleG (-r⁻¹) 0 - saddleG (-r⁻¹) χ - 2 * (ψ : ℂ) / (1+(r : ℂ)*I)‖ ≤
      ψ^2 / (r*(1-ψ)) := by
  dsimp only
  let ψ := 1 - Real.cos χ
  have hrp : 0 < r := by linarith
  have ht : 0 < r⁻¹ := inv_pos.mpr hrp
  have ht₁ := inv_le_one_of_one_le₀ hr
  have habs : |r⁻¹| ≤ 1 := by simpa [abs_of_pos ht] using ht₁
  have hinv : (1 - (r : ℂ)⁻¹ * I) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    rw [← Complex.ofReal_inv]
    simp [Complex.mul_re]
  have hden : (1 + (r : ℂ) * I) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simp [Complex.mul_re]
  have hcoef : conj (2 * (r⁻¹ : ℝ) * I * (ψ : ℂ) / (1+(r⁻¹ : ℝ)*I)) =
      2 * (ψ : ℂ) / (1+(r : ℂ)*I) := by
    simp only [map_div₀,map_mul,map_ofNat,map_add,map_one,Complex.conj_ofReal,Complex.conj_I,
      Complex.ofReal_inv,map_inv₀]
    have hinv' : (1 + (r⁻¹ : ℝ) * -I) ≠ 0 := by
      rw [Complex.ofReal_inv]
      convert hinv using 1
      ring
    rw [Complex.ofReal_inv] at hinv'
    field_simp [(Complex.ofReal_ne_zero.mpr hrp.ne'), hinv', hden]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    have hri : -I+(r : ℂ) ≠ 0 := by
      apply Complex.ne_zero_of_re_pos
      simpa using hrp
    field_simp [hri]
  have h := saddleG_log_linear_remainder ht ht₁ hψ
  dsimp only at h
  rw [← saddleG_zero] at h
  change ‖saddleG (-r⁻¹) 0 - saddleG (-r⁻¹) χ - 2*(ψ : ℂ)/(1+(r : ℂ)*I)‖ ≤ _
  rw [saddleG_neg_radius_conj habs, saddleG_neg_radius_conj habs, ← hcoef,
    ← map_sub, ← map_sub, Complex.norm_conj]
  refine h.trans_eq ?_
  field_simp

private theorem abs_two_cos_gap_sub_sq {χ : ℝ} (hχ : |χ| ≤ 1) :
    |2*(1-Real.cos χ)-χ^2| ≤ χ^4/12 := by
  have hx := pow_le_pow_left₀ (abs_nonneg χ) hχ 2
  have h := cos_taylor_bounds (abs_nonneg χ) 2 (by
    change |χ| ^ 2 ≤ (5 : ℝ)*6
    exact hx.trans (by norm_num))
  rw [Real.cos_abs, show cosTaylor 2 |χ| = 1-χ^2/2 by
    norm_num [cosTaylor,Finset.sum_range_succ]; ring] at h
  have h4 : |χ|^4 = χ^4 := by rw [show 4 = 2*2 by decide, pow_mul,pow_mul,sq_abs]
  rw [h4] at h
  norm_num at h
  exact abs_le.mpr ⟨by linarith only [h.2], by linarith only [h.1,pow_nonneg (abs_nonneg χ) (n := 4), h4]⟩

private theorem cos_gap_cap {χ h : ℝ} (hχ : |χ| ≤ h) (hh : h = 3/4 ∨ h = 1) :
    1 - Real.cos χ ≤ if h ≤ 3/4 then 0.269 else 0.460 := by
  have hH : h ≤ 1 := by rcases hh with rfl | rfl <;> norm_num
  have hp : h ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨(abs_nonneg χ).trans hχ, hH.trans (by linarith [Real.pi_gt_three])⟩
  have hcos := Real.antitoneOn_cos ⟨abs_nonneg χ,hχ.trans hp.2⟩ hp hχ
  rw [Real.cos_abs] at hcos
  have ht : Real.cos h ≥ 1-h^2/2+h^4/24-h^6/720 := by
    have hcut : h ^ 2 ≤ (((2*3+1 : ℕ) : ℝ)) * (2*3+2 : ℕ) := by
      rcases hh with rfl | rfl <;> norm_num
    have H := (cos_taylor_bounds hp.1 3 hcut).2
    norm_num [cosTaylor,Finset.sum_range_succ] at H
    linarith only [H]
  rcases hh with rfl | rfl <;> norm_num at ht ⊢ <;> linarith only [hcos,ht]

theorem norm_midPhase_quartic {r χ : ℝ} (hr : 1 ≤ r) (hχ : |χ| ≤ 1) :
    let ψ := 1-Real.cos χ
    ‖midPhase r 0 χ - saddleS r^2 + saddleBesselSlope r*(χ : ℂ)^2‖ ≤
      χ^4/r * (1/12 + 1/(4*(1-ψ))) := by
  dsimp only
  let ψ := 1-Real.cos χ
  have hrp : 0 < r := by linarith
  have hp := cos_gap_cap hχ (Or.inr rfl)
  norm_num at hp
  have hψ : ψ < 1 := by dsimp [ψ]; linarith only [hp]
  have hψ₀ : 0 ≤ ψ := sub_nonneg.mpr (Real.cos_le_one χ)
  have hψ₁ : ψ ≤ χ^2/2 := by dsimp [ψ]; linarith only [Real.one_sub_sq_div_two_le_cos (x := χ)]
  have htail := norm_midPhase_log_remainder hr hψ
  dsimp only at htail
  let δ := saddleG (-r⁻¹) 0 - saddleG (-r⁻¹) χ
  let d : ℂ := 1+(r : ℂ)*I
  have hd : d ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simp [d,Complex.mul_re]
  have he : midPhase r 0 χ - saddleS r ^ 2 + saddleBesselSlope r * (χ : ℂ) ^ 2 =
      (δ-2*(ψ : ℂ)/d) + (2*(ψ : ℂ)-(χ : ℂ)^2)/d := by
    rw [← midPhase_zero_value hrp]
    simp only [midPhase,midModeRadius_zero,Complex.ofReal_zero,zero_pow (by decide : 2 ≠ 0),sub_zero]
    have hc : saddleBesselSlope r = 1-d⁻¹ := by
      change (r : ℂ)*I/d = 1-d⁻¹
      rw [show (r : ℂ)*I = d-1 by simp [d], sub_div,div_self hd,one_div]
    rw [hc]
    unfold δ
    ring
  have hnr : r ≤ ‖d‖ := by
    simpa [d, Complex.mul_im, abs_of_pos hrp] using Complex.abs_im_le_norm d
  have hsmall : ‖(2*(ψ : ℂ)-(χ : ℂ)^2)/d‖ ≤ χ^4/(12*r) := by
    rw [norm_div, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (div_le_div₀ (by positivity) (abs_two_cos_gap_sub_sq hχ) hrp hnr).trans_eq ?_
    ring
  have hb : ψ^2/(r*(1-ψ)) ≤ χ^4/(4*r*(1-ψ)) := by
    have h := pow_le_pow_left₀ hψ₀ hψ₁ 2
    rw [show χ^4 = (χ^2)^2 by ring]
    have hd' : 0 < r*(1-ψ) := mul_pos hrp (sub_pos.mpr hψ)
    calc
      _ ≤ (χ^2/2)^2/(r*(1-ψ)) := div_le_div_of_nonneg_right h hd'.le
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ ‖δ-2*(ψ : ℂ)/d‖ + ‖(2*(ψ : ℂ)-(χ : ℂ)^2)/d‖ := norm_add_le _ _
    _ ≤ χ^4/(4*r*(1-ψ)) + χ^4/(12*r) := add_le_add (htail.trans hb) hsmall
    _ = _ := by ring

theorem norm_midPhase_quartic_le {r χ h : ℝ} (hr : 1 ≤ r) (hχ : |χ| ≤ h)
    (hh : h = 3/4 ∨ h = 1) :
    ‖midPhase r 0 χ - saddleS r^2 + saddleBesselSlope r*(χ : ℂ)^2‖ ≤
      midQuarticConstant h * χ^4/r := by
  have hp := cos_gap_cap hχ hh
  have hh' : h ≤ 1 := by rcases hh with rfl | rfl <;> norm_num
  have H := norm_midPhase_quartic hr (hχ.trans hh')
  dsimp only at H
  refine H.trans ?_
  have hrp : 0 ≤ χ^4/r := div_nonneg (by positivity) (by linarith)
  rw [mul_div_assoc, mul_comm (midQuarticConstant h)]
  apply mul_le_mul_of_nonneg_left _ hrp
  have hc {d k : ℝ} (hd : 0 < d) (hgap : d ≤ Real.cos χ)
      (hk : 1/12 + 1/(4*d) ≤ k) : 1/12 + 1/(4*(1-(1-Real.cos χ))) ≤ k := by
    refine le_trans (add_le_add_right ?_ _) hk
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < 4*d)
    linarith only [hgap]
  rcases hh with rfl | rfl
  · norm_num at hp
    rw [midQuarticConstant, ite_eq_left (by norm_num : (3/4 : ℝ) ≤ 3/4)]
    exact hc (d := 0.731) (by norm_num) (by linarith only [hp]) (by norm_num)
  · norm_num at hp
    rw [midQuarticConstant, ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 3/4)]
    exact hc (d := 0.540) (by norm_num) (by linarith only [hp]) (by norm_num)

end DurfeeCCS.Step09
