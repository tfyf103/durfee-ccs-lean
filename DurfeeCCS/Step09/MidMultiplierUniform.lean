module

public import DurfeeCCS.Step09.MidMultiplierEuler
public import DurfeeCCS.Step08.MidpointRay
public import DurfeeCCS.Step08.MidpointUniform
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-! Uniform bounds for the transformed multiplier, including equation (53). -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step08

def midLogMultiplier (r : ℝ) (p : ℤ) (ζ : ℂ) (χ : ℝ) : ℂ :=
  -ζ / 12 + midEulerLog (midEtaTransform ζ) +
    (saddleG (midModeRadius r p) χ / ζ - pairedLog (midModeRadius r p) χ ζ)

theorem re_midEtaTransform_pos {ζ : ℂ} (hζ : 0 < ζ.re) : 0 < (midEtaTransform ζ).re := by
  have hz : ζ ≠ 0 := by intro h; simp [h] at hζ
  rw [midEtaTransform, ← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  exact div_pos (mul_pos (by positivity) hζ) (Complex.normSq_pos.mpr hz)

theorem midMultiplier_eq_exp_log {ζ : ℂ} (hζ : 0 < ζ.re) (r χ : ℝ) (p : ℤ) :
    midMultiplier r p ζ χ = Complex.exp (midLogMultiplier r p ζ χ) := by
  rw [midMultiplier, midLogMultiplier, Complex.exp_add, Complex.exp_add,
    exp_midEulerLog (re_midEtaTransform_pos hζ), div_eq_mul_inv]

private theorem norm_midMultiplier_le_exp {ζ : ℂ} {r χ e L : ℝ} {p : ℤ}
    (hζ : 0 < ζ.re) (hE : ‖midEulerLog (midEtaTransform ζ)‖ ≤ e)
    (hL : ‖pairedLog (midModeRadius r p) χ ζ - saddleG (midModeRadius r p) χ / ζ‖ ≤ L) :
    ‖midMultiplier r p ζ χ‖ ≤ Real.exp (L + e) := by
  rw [midMultiplier_eq_exp_log hζ, Complex.norm_exp, Real.exp_le_exp]
  have h := (Complex.re_le_norm (midEulerLog (midEtaTransform ζ))).trans hE
  have he := Complex.re_le_norm
    (saddleG (midModeRadius r p) χ / ζ - pairedLog (midModeRadius r p) χ ζ)
  rw [norm_sub_rev] at he
  have hf := he.trans hL
  have hz : (-ζ / 12).re ≤ 0 := by
    rw [show (12 : ℂ) = ((12 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re, Complex.neg_re]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hζ.le) (by norm_num)
  simp only [midLogMultiplier, Complex.add_re]
  linarith only [h, hf, hz]

theorem norm_mid_logDiff_le {n : ℕ} {r t χ η : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) (hη : |η| ≤ 8) (ht : |t| ≤ 1) :
    let ζ := midEtaPoint n r η
    ‖pairedLog t χ ζ - saddleG t χ / ζ‖ ≤
      0.51 + (2 / (Real.pi - midU n r * Real.sqrt (1 + η ^ 2))) * (1 + Real.sqrt (1 + η ^ 2)) := by
  let ζ := midEtaPoint n r η
  have hn' : 0 < n := by omega
  have hr' : 0 < r := by linarith
  have hu := saddleU_pos hn' hr'
  have huζ : 0 < ζ.re := by simpa only [ζ, midEtaPoint_re] using hu
  have hζ : ‖ζ‖ < Real.pi :=
    (norm_midEtaPoint_lt hn hr hmax hη).trans (by linarith [Real.pi_gt_d2])
  have hnorm : ‖ζ‖ = midU n r * Real.sqrt (1 + η ^ 2) := norm_midEtaPoint hn' hr' η
  have hratio : ‖ζ‖ / ζ.re = Real.sqrt (1 + η ^ 2) := by
    rw [hnorm, show ζ.re = midU n r from midEtaPoint_re n r η]
    field_simp [hu.ne']
  rw [← hnorm, ← hratio]
  exact norm_pairedLog_sub_saddleG_div_le_pi_cutoff t χ ht huζ hζ

private theorem norm_midMultiplier_lt_of_eta_bound {n : ℕ} {r η L S C : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : |η| ≤ L) (hL : L ≤ 8) (hS : Real.sqrt (1 + L ^ 2) ≤ S)
    (hDen : 0 < 3.14159 - 0.072 * S)
    (hC : Real.exp (0.51 + (2 / (3.14159 - 0.072 * S)) * (1 + S) + 0.0005) < C)
    (p : ℤ) (χ : ℝ) :
    ‖midMultiplier r p (midEtaPoint n r η) χ‖ < C := by
  let ζ := midEtaPoint n r η
  have hu := saddleU_pos (by omega : 0 < n) (by linarith : 0 < r)
  have hζ : 0 < ζ.re := by simpa only [ζ, midEtaPoint_re] using hu
  have h8 := hη.trans hL
  have h2 := pow_le_pow_left₀ (abs_nonneg η) hη 2
  rw [sq_abs] at h2
  have hSη := (Real.sqrt_le_sqrt (by linarith only [h2] :
    1 + η ^ 2 ≤ 1 + L ^ 2)).trans hS
  have hprod := mul_le_mul (midU_lt_072 hn hr hmax).le hSη (Real.sqrt_nonneg _) (by norm_num)
  have hden : 3.14159 - 0.072 * S ≤ Real.pi - midU n r * Real.sqrt (1 + η ^ 2) := by
    linarith [Real.pi_gt_d6]
  have hcoeff := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hDen hden
  have hD := norm_mid_logDiff_le hn hr hmax h8 (midModeRadius_abs_le_one hr p)
    (χ := χ)
  have hS' : 1 + Real.sqrt (1 + η ^ 2) ≤ 1 + S := add_le_add le_rfl hSη
  have hB := hD.trans
    (add_le_add le_rfl (mul_le_mul hcoeff hS' (by positivity) (by positivity)))
  exact (norm_midMultiplier_le_exp hζ (norm_midEulerLog_lt_0005 hn hr hmax h8).le hB).trans_lt hC

theorem norm_midMultiplier_lt_2100 {n : ℕ} {r η : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : |η| ≤ 8) (p : ℤ) (χ : ℝ) :
    ‖midMultiplier r p (midEtaPoint n r η) χ‖ < 2100 := by
  apply norm_midMultiplier_lt_of_eta_bound (S := 8.063) hn hr hmax hη le_rfl
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  · norm_num
  · dyadic_interval +kernel [prec := 38]

theorem norm_midMultiplier_lt_30 {n : ℕ} {r η : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : |η| ≤ 3) (p : ℤ) (χ : ℝ) :
    ‖midMultiplier r p (midEtaPoint n r η) χ‖ < 30 := by
  apply norm_midMultiplier_lt_of_eta_bound (S := 3.163) hn hr hmax hη (by norm_num)
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  · norm_num
  · dyadic_interval +kernel [prec := 38]

theorem norm_midMultiplier_lt_10_9 {n : ℕ} {r η : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : |η| ≤ 3 / 2) (p : ℤ) (χ : ℝ) :
    ‖midMultiplier r p (midEtaPoint n r η) χ‖ < 10.9 := by
  apply norm_midMultiplier_lt_of_eta_bound (S := 1.803) hn hr hmax hη (by norm_num)
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  · norm_num
  · dyadic_interval +kernel [prec := 38]

theorem norm_midMultiplier_lt_two {n : ℕ} {r η : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hlog : 1 ≤ Real.log r) (hη : |η| ≤ 8) (p : ℤ) (χ : ℝ) :
    ‖midMultiplier r p (midEtaPoint n r η) χ‖ < 2 := by
  let ζ := midEtaPoint n r η
  have hr' : 0 < r := by linarith
  have hu := saddleU_pos (by omega : 0 < n) hr'
  have hζ : 0 < ζ.re := by simpa only [ζ, midEtaPoint_re] using hu
  have hρ : r⁻¹ ≤ Real.exp (-1) := by
    rw [← Real.exp_log hr', ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (neg_le_neg hlog)
  have hOne : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hAbs := midModeRadius_abs hr' p
  have hb := norm_pairedLog_sub_saddleG_div_le_signed (midModeRadius r p) χ (midU n r) η
    (by rw [hAbs]; exact hρ.trans_lt hOne) hu
  rw [hAbs] at hb
  have h2 := pow_le_pow_left₀ (abs_nonneg η) hη 2
  rw [sq_abs] at h2
  have hden : 0 < 4 * (1 - Real.exp (-1 : ℝ)) := by linarith
  have hprod := mul_le_mul
    (mul_le_mul (midU_lt_072 hn hr hmax).le (show 1 + η ^ 2 ≤ 65 by linarith)
      (by positivity) (by norm_num)) hρ (inv_nonneg.mpr hr'.le) (by norm_num)
  have hG : ‖pairedLog (midModeRadius r p) χ ζ - saddleG (midModeRadius r p) χ / ζ‖ ≤
      0.072 * 65 * Real.exp (-1) / (4 * (1 - Real.exp (-1))) := hb.trans
    (div_le_div₀ (by positivity) hprod hden (by linarith only [hρ]))
  have hC : Real.exp (0.072 * 65 * Real.exp (-1) / (4 * (1 - Real.exp (-1))) + 0.0005) < 2 := by
    dyadic_interval +kernel [prec := 38]
  exact (norm_midMultiplier_le_exp hζ (norm_midEulerLog_lt_0005 hn hr hmax hη).le hG).trans_lt hC

end DurfeeCCS.Step09
