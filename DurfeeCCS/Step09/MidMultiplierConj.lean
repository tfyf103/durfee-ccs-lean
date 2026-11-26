module

public import DurfeeCCS.Step09.MidMultiplierUniform
public import DurfeeCCS.Step09.MidPhaseSymmetry

import Mathlib.Tactic.Ring

/-! Conjugation of the two main frequency multipliers. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step08
open scoped ComplexConjugate

theorem pairedLog_neg_eq_conj {t : ℝ} (ht : |t| ≤ 1) (χ : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) :
    pairedLog (-t) χ (conj ζ) = conj (pairedLog t χ ζ) := by
  have hζ' : 0 < (conj ζ).re := by simpa using hζ
  have ht' : |-t| ≤ 1 := by simpa only [abs_neg] using ht
  rw [pairedLog_eq_tsum_mode (-t) χ ht' hζ', pairedLog_eq_tsum_mode t χ ht hζ, Complex.conj_tsum]
  apply tsum_congr
  intro n
  simp only [pairedLogMode, pairedLogCoeff, map_mul, map_neg, map_pow, map_div₀, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast, Complex.ofReal_neg, neg_neg,
    ← Complex.sinh_conj]
  simp only [neg_mul, mul_neg, neg_neg]

theorem eulerProduct_conj {ζ : ℂ} (hζ : 0 < ζ.re) :
    eulerProduct (conj ζ) = conj (eulerProduct ζ) := by
  have hs := (eulerProduct_multipliable hζ).map_tprod (starRingEnd ℂ) Complex.continuous_conj
  rw [eulerProduct, eulerProduct, hs]
  apply tprod_congr
  intro j
  simp only [map_sub, map_one, ← Complex.exp_conj, map_mul, map_neg, map_add,
    Complex.conj_natCast]

theorem midEtaTransform_conj (ζ : ℂ) : midEtaTransform (conj ζ) = conj (midEtaTransform ζ) := by
  simp only [midEtaTransform, map_div₀, map_mul, map_pow, map_ofNat, Complex.conj_ofReal]

theorem midEtaPoint_neg_conj (n : ℕ) (r η : ℝ) :
    midEtaPoint n r (-η) = conj (midEtaPoint n r η) := by
  simp [midEtaPoint]

theorem midMultiplier_neg_one_conj {r : ℝ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : 0 < ζ.re) (χ : ℝ) :
    midMultiplier r (-1) (conj ζ) χ = conj (midMultiplier r 0 ζ χ) := by
  have hR : |-(r⁻¹)| ≤ 1 := by simpa only [midModeRadius_zero] using midModeRadius_abs_le_one hr 0
  have h := saddleG_neg_radius_conj hR χ
  have h' := pairedLog_neg_eq_conj hR χ hζ
  rw [neg_neg] at h h'
  have hz := re_midEtaTransform_pos hζ
  unfold midMultiplier
  rw [midModeRadius_neg_one, midModeRadius_zero, midEtaTransform_conj, eulerProduct_conj hz, h, h']
  simp only [map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_sub, ← Complex.exp_conj]

end DurfeeCCS.Step09
