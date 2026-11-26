module

public import DurfeeCCS.Step09.MidPhaseDerivatives
public import DurfeeCCS.Step08.PhaseGapExpansion
public import DurfeeCCS.Step08.SaddleBesselModel
public import DurfeeCCS.Step07.TrigonometricBounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The real phase bound and its central quadratic approximation. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08
open scoped ComplexConjugate

abbrev midCurvature := saddleBesselSlope

def midDamping (n : ℕ) (r η : ℝ) : ℝ :=
  (r ^ 2 / (1 + r ^ 2)) / (midU n r * (1 + η ^ 2))

def midGaussianExponent (n : ℕ) (r η χ : ℝ) : ℂ :=
  let ζ := midEtaPoint n r η
  (n : ℂ) * ζ + (saddleS r ^ 2 - midCurvature r * (χ : ℂ) ^ 2) / ζ

theorem midPhase_components (r : ℝ) (p : ℤ) (χ : ℝ) :
    (midPhase r p χ).re =
      Real.log r ^ 2 - midFrequency p ^ 2 + Real.pi ^ 2 / 3 - χ ^ 2 -
        (saddleG (midModeRadius r p) χ).re ∧
    (midPhase r p χ).im =
      2 * Real.log r * midFrequency p - (saddleG (midModeRadius r p) χ).im := by
  unfold midPhase
  rw [pow_two]
  simp [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im]
  constructor <;> ring

theorem midPhase_component_bounds {r : ℝ} (hr : 1 ≤ r) (p : ℤ) (χ : ℝ) :
    (midPhase r p χ).re ≤ Real.log r ^ 2 - midFrequency p ^ 2 + Real.pi ^ 2 / 3 -
       (saddleG r⁻¹ 0).re - χ ^ 2 / (1 + r⁻¹ ^ 2) ∧
    |(midPhase r p χ).im| ≤ 2 * Real.log r * |midFrequency p| + (saddleG r⁻¹ 0).im := by
  obtain ⟨hRe,hIm⟩ := midPhase_components r p χ
  have hrp : 0 < r := by linarith
  constructor
  · rw [hRe, midModeRadius_phase_re hr]
    have hg := saddleG_re_lower (inv_pos.mpr hrp) (inv_le_one_of_one_le₀ hr) χ
    have he : χ ^ 2 - r⁻¹ ^ 2 / (1 + r⁻¹ ^ 2) * χ ^ 2 =
        χ ^ 2 / (1 + r⁻¹ ^ 2) := by field_simp; ring
    linarith only [hg,he]
  · rw [hIm]
    have hTri : |2 * Real.log r * midFrequency p - (saddleG (midModeRadius r p) χ).im| ≤
        |2 * Real.log r * midFrequency p| + |(saddleG (midModeRadius r p) χ).im| := by
      rw [sub_eq_add_neg, ← abs_neg ((saddleG (midModeRadius r p) χ).im)]
      exact abs_add_le _ _
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.log_nonneg hr),
      abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] at hTri
    exact hTri.trans (add_le_add le_rfl (midModeRadius_phase_im hr p χ))

theorem midPhase_zero_components {r : ℝ} (hr : 1 ≤ r) (χ : ℝ) :
    (midPhase r 0 χ).re ≤ (saddleS r ^ 2).re - r ^ 2 / (1 + r ^ 2) * χ ^ 2 ∧
    |(midPhase r 0 χ).im| ≤ (saddleS r ^ 2).im := by
  have hrp : 0 < r := by linarith
  obtain ⟨hre,him⟩ := midPhase_component_bounds hr 0 χ
  obtain ⟨h0r,h0i⟩ := midPhase_components r 0 0
  rw [midPhase_zero_value hrp, midModeRadius_phase_re hr] at h0r
  have ht : |r⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr hrp.le)]
    exact inv_le_one_of_one_le₀ hr
  rw [midPhase_zero_value hrp, midModeRadius_zero, saddleG_neg_radius_conj ht,
    Complex.conj_im] at h0i
  rw [midFrequency_zero] at h0i him
  rw [abs_of_pos (by positivity : 0 < Real.pi/2)] at him
  have hden : χ ^ 2 / (1 + r⁻¹ ^ 2) = r ^ 2 / (1 + r ^ 2) * χ ^ 2 := by
    field_simp [hrp.ne']
    ring
  rw [hden] at hre
  rw [midFrequency_zero] at hre
  norm_num at h0r
  exact ⟨by linarith only [hre,h0r], by linarith only [him,h0i]⟩

theorem midEtaPoint_ne_zero {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    midEtaPoint n r η ≠ 0 := by
  rw [midEtaPoint_eq_vertical]
  exact verticalPoint_ne_zero (saddleU_pos hn hr) _

theorem re_div_midEtaPoint {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (η : ℝ) (z : ℂ) :
    (z / midEtaPoint n r η).re = (z.re + η * z.im) / (midU n r * (1 + η ^ 2)) := by
  have hu := saddleU_pos hn hr
  rw [Complex.div_re, Complex.normSq_apply, midEtaPoint_re, midEtaPoint_im, ← add_div]
  field_simp [hu.ne', show (1+η^2) ≠ 0 by positivity]

theorem mid_saddle_exponent_identity {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    (n : ℂ) * midEtaPoint n r η + saddleS r ^ 2 / midEtaPoint n r η =
      2 * (Real.sqrt n : ℂ) * saddleS r -
        (midOmega n r * (η-midSlope r)^2 : ℝ) / (1+(η : ℂ)*I) := by
  let a : ℝ := (saddleS r).re
  let x : ℝ := Real.sqrt n
  let z : ℂ := 1 + (η : ℂ) * I
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  have hx : 0 < x := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hz : z ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simp [z, Complex.mul_re]
  have hnC : (n : ℂ) = (x : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [hnC, ← saddleS_real_imag r]
  unfold midEtaPoint midSlope
  change (x : ℂ)^2 * (↑(a/x) * z) +
      ((a : ℂ) + (saddleS r).im * I)^2 / (↑(a/x) * z) =
      2 * (x : ℂ) * ((a : ℂ) + (saddleS r).im * I) -
        (↑(a*x*(η-(saddleS r).im/a)^2) : ℂ) / z
  push_cast
  dsimp only [z]
  have hz' : (1+(η : ℂ)*I) ≠ 0 := hz
  field_simp [(Complex.ofReal_ne_zero.mpr ha.ne'),(Complex.ofReal_ne_zero.mpr hx.ne'),hz']
  ring_nf
  rw [Complex.I_sq]
  ring

theorem re_midSaddle_exponent {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    ((n : ℂ) * midEtaPoint n r η + saddleS r ^ 2 / midEtaPoint n r η).re =
      2*midOmega n r - midOmega n r*(η-midSlope r)^2/(1+η^2) := by
  rw [mid_saddle_exponent_identity hn hr]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_re, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero]
  norm_num [saddleOmega, Complex.mul_re, Complex.mul_im]
  ring

theorem re_midExponent_of_component_bounds {n : ℕ} (hn : 0 < n) {r η χ : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) {G : ℂ}
    (hre : G.re ≤ (saddleS r ^ 2).re - r ^ 2 / (1 + r ^ 2) * χ ^ 2)
    (him : G.im ≤ (saddleS r ^ 2).im) :
    ((n : ℂ) * midEtaPoint n r η + G / midEtaPoint n r η).re ≤
      2*midOmega n r - midOmega n r*(η-midSlope r)^2/(1+η^2) - midDamping n r η * χ^2 := by
  let ζ := midEtaPoint n r η
  let D : ℝ := midU n r * (1+η^2)
  have hD : 0 < D := mul_pos (saddleU_pos hn hr) (by positivity)
  change ((n : ℂ) * ζ + G/ζ).re ≤ _
  have hh := re_midSaddle_exponent hn hr η
  change ((n : ℂ)*ζ + saddleS r^2/ζ).re = _ at hh
  have hsum := add_le_add hre (mul_le_mul_of_nonneg_left him hη)
  have ht := div_le_div_of_nonneg_right hsum hD.le
  have hdiff : (G/ζ).re ≤ (saddleS r^2/ζ).re - midDamping n r η*χ^2 := by
    dsimp only [ζ]
    rw [re_div_midEtaPoint hn hr, re_div_midEtaPoint hn hr]
    refine ht.trans_eq ?_
    dsimp only [midDamping,D]
    ring
  rw [← hh,Complex.add_re,Complex.add_re]
  linarith only [hdiff]

theorem re_mid_phase_exponent_zero_le {n : ℕ} (hn : 0 < n) {r η : ℝ} (hr : 1 ≤ r)
    (hη : 0 ≤ η) (χ : ℝ) :
    ((n : ℂ) * midEtaPoint n r η + midPhase r 0 χ / midEtaPoint n r η).re ≤
      2*midOmega n r - midOmega n r*(η-midSlope r)^2/(1+η^2) - midDamping n r η*χ^2 := by
  obtain ⟨hre,him⟩ := midPhase_zero_components hr χ
  exact re_midExponent_of_component_bounds hn (by linarith) hη hre ((le_abs_self _).trans him)

theorem re_midGaussianExponent_le {n : ℕ} (hn : 0 < n) {r η : ℝ} (hr : 0 < r) (hη : 0 ≤ η)
    (χ : ℝ) :
    (midGaussianExponent n r η χ).re ≤
      2*midOmega n r - midOmega n r*(η-midSlope r)^2/(1+η^2) - midDamping n r η*χ^2 := by
  unfold midGaussianExponent
  dsimp only
  apply re_midExponent_of_component_bounds hn hr hη
  · simp only [Complex.sub_re, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, (saddleBesselSlope_components r).1]
    exact le_rfl
  · simp only [Complex.sub_im, Complex.mul_im, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add, (saddleBesselSlope_components r).2]
    linarith only [show 0 ≤ r / (1+r^2)*χ^2 by positivity]

end DurfeeCCS.Step09
