module

public import DurfeeCCS.Step09.MidMajorIntegral
public import DurfeeCCS.Step09.MidMultiplierUniform

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The three errors in (58), integrated over the central angle interval. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

def midMajorZ (eps q h : ℝ) : ℝ := h ^ 2 / ((13 / 4) * q * (1 + eps ^ 2))

def midMajorLocalLog (eps q h : ℝ) : ℝ :=
  (13 / 16) * theta38K h * eps * q + Real.sqrt (13 / 4) * q / 12 + 1 / 10 ^ 20

def midMajorChiError (eps q h : ℝ) : ℝ :=
  (119 / 10) * thetaFourthRoot ((13 / 4) * (1 + eps ^ 2)) *
    Real.exp (-midMajorZ eps q h) / Real.sqrt (Real.pi * midMajorZ eps q h)

def midMajorMultiplierError (eps q h : ℝ) : ℝ :=
  thetaFourthRoot ((13 / 4) * (1 + eps ^ 2)) * (Real.exp (midMajorLocalLog eps q h) - 1)

def midMajorQuarticError (eps q κ : ℝ) : ℝ :=
  (3 / 4) * κ * eps * q * thetaFourthRoot (13 / 4) ^ 7 * thetaFourthRoot (1 + eps ^ 2) ^ 9

def midMajorLocalError (eps q h κ : ℝ) : ℝ :=
  midMajorQuarticError eps q κ + midMajorMultiplierError eps q h + midMajorChiError eps q h

private theorem midMajor_one_add_sq_le {η : ℝ} (hη : η ∈ Icc (0 : ℝ) (3 / 2)) :
    1 + η ^ 2 ≤ 13 / 4 := by
  nlinarith only [pow_le_pow_left₀ hη.1 hη.2 2]

theorem midMajorZ_le {n : ℕ} (hn : 0 < n) {r η eps q h : ℝ} (hr : 0 < r)
    (heps : r⁻¹ ≤ eps) (hq : midU n r ≤ q) (hη : η ∈ Icc (0 : ℝ) (3 / 2)) :
    midMajorZ eps q h ≤ midDamping n r η * h ^ 2 := by
  have hu := saddleU_pos hn hr
  have hq₀ : 0 ≤ q := hu.le.trans hq
  have hdp := midMajor_damping_pos hn hr η
  have hp := midMajor_one_add_sq_le hη
  have hE : 1 + r⁻¹ ^ 2 ≤ 1 + eps ^ 2 :=
    add_le_add_right (pow_le_pow_left₀ (inv_nonneg.mpr hr.le) heps 2) 1
  have hprod : (midDamping n r η)⁻¹ ≤ (13 / 4) * q * (1 + eps ^ 2) := by
    rw [midMajor_inv_damping hn hr, mul_comm (13 / 4 : ℝ) q]
    gcongr
  have hpos : 0 < (midDamping n r η)⁻¹ := inv_pos.mpr hdp
  have hh := div_le_div_of_nonneg_left (sq_nonneg h) hpos hprod
  rw [div_inv_eq_mul, mul_comm] at hh
  simpa only [midMajorZ, mul_comm] using hh

theorem midMajor_quartic_term_le {n : ℕ} (hn : 0 < n) {r η eps q κ : ℝ}
    (hr : 0 < r) (heps : r⁻¹ ≤ eps) (hq : midU n r ≤ q) (hκ : 0 ≤ κ)
    (hη : η ∈ Icc (0 : ℝ) (3 / 2)) :
    3 * (κ / r / ‖midEtaPoint n r η‖) / (4 * midDamping n r η ^ 2) ≤
      (3 / 4) * κ * eps * q * (Real.sqrt (13 / 4)) ^ 3 * (1 + eps ^ 2) ^ 2 := by
  let u := midU n r
  let Y := Real.sqrt (1 + η ^ 2)
  have hu : 0 < u := saddleU_pos hn hr
  have hq₀ : 0 ≤ q := hu.le.trans hq
  have heps₀ : 0 ≤ eps := (inv_nonneg.mpr hr.le).trans heps
  have hY : 0 < Y := Real.sqrt_pos.mpr (by positivity)
  have hY₂ : Y ^ 2 = 1 + η ^ 2 := Real.sq_sqrt (by positivity)
  have hE : 1 + r⁻¹ ^ 2 ≤ 1 + eps ^ 2 :=
    add_le_add_right (pow_le_pow_left₀ (inv_nonneg.mpr hr.le) heps 2) 1
  rw [norm_midEtaPoint hn hr]
  change 3 * (κ / r / (u * Y)) / (4 * midDamping n r η ^ 2) ≤ _
  calc
    _ = (3 / 4) * κ * r⁻¹ * u * Y ^ 3 * (1 + r⁻¹ ^ 2) ^ 2 := by
      simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, midMajor_inv_damping hn hr]
      rw [← hY₂]
      field_simp
      ring
    _ ≤ _ := by
      have hYle : Y ≤ Real.sqrt (13 / 4) := Real.sqrt_le_sqrt (midMajor_one_add_sq_le hη)
      gcongr

theorem midMajor_local_error_identity (eps q h κ : ℝ) :
    thetaFourthRoot ((13 / 4) * (1 + eps ^ 2)) *
      ((119 / 10) * (Real.exp (-midMajorZ eps q h) / Real.sqrt (Real.pi * midMajorZ eps q h)) +
        (Real.exp (midMajorLocalLog eps q h) - 1) +
        (3 / 4) * κ * eps * q * (Real.sqrt (13 / 4)) ^ 3 * (1 + eps ^ 2) ^ 2) =
      midMajorLocalError eps q h κ := by
  unfold midMajorLocalError midMajorChiError midMajorMultiplierError midMajorQuarticError
  have hQ : (1 + eps ^ 2) ^ 2 = thetaFourthRoot (1 + eps ^ 2) ^ 8 := by
    calc
      _ = (thetaFourthRoot (1 + eps ^ 2) ^ 4) ^ 2 := by rw [thetaFourthRoot_four (by positivity)]
      _ = _ := by ring
  rw [show Real.sqrt (13 / 4) = thetaFourthRoot (13 / 4) ^ 2 from
    (Real.sq_sqrt (Real.sqrt_nonneg _)).symm,
    hQ]
  rw [thetaFourthRoot_mul (x := 13 / 4) (by norm_num)]
  ring

/-- Equation (58) integrated over the central η interval. -/
theorem midMajor_central_error_le {n : ℕ} {r eps q h κ : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (heps : r⁻¹ ≤ eps) (hq : midU n r ≤ q) (hh : 0 < h) (hκ : 0 ≤ κ)
    (hL : 0 ≤ midMajorLocalLog eps q h)
    (hnear : ∀ η ∈ Icc (0 : ℝ) (3 / 2), ∀ χ ∈ Icc (-h) h,
      ‖midMultiplier r 0 (midEtaPoint n r η) χ - 1‖ ≤ Real.exp (midMajorLocalLog eps q h) - 1)
    (hphase : ∀ χ ∈ Icc (-h) h, ‖midPhase r 0 χ - (saddleS r ^ 2 - midCurvature r * (χ : ℂ) ^ 2)‖
      ≤ κ / r * χ ^ 4) :
    ‖midContribution n r 0 0 (3 / 2) - midMajorQuadraticContribution n r 0 (3 / 2)‖ ≤
      saddleAmplitude n r / 2 * ((243 / 100) * midMajorLocalError eps q h κ) := by
  have hnp : 0 < n := by omega
  have hrp : 0 < r := by linarith
  have hu := saddleU_pos hnp hrp
  have ht := saddleOmega_pos hnp hrp
  have hq' := hu.trans_le hq
  have heps' : 0 ≤ eps := (inv_nonneg.mpr hrp.le).trans heps
  have hM := saddleAmplitude_pos hnp hrp
  let z := midMajorZ eps q h
  let L := midMajorLocalLog eps q h
  let C :=
    (119 / 10) * (Real.exp (-z) / Real.sqrt (Real.pi * z)) +
      (Real.exp L - 1) +
      (3 / 4) * κ * eps * q * (Real.sqrt (13 / 4)) ^ 3 * (1 + eps ^ 2) ^ 2
  have hz : 0 < z := by dsimp [z, midMajorZ]; positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hp := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hL)
    positivity
  have hB (η : ℝ) (hη : η ∈ Icc (0 : ℝ) (3 / 2)) (χ : ℝ) :
      ‖midMultiplier r 0 (midEtaPoint n r η) χ‖ ≤ 10.9 :=
    (norm_midMultiplier_lt_10_9 hn hr hmax (by simpa [abs_of_nonneg hη.1] using hη.2) 0 χ).le
  have hf := intervalIntegrable_midMajorChiIntegral hnp hr le_rfl (by norm_num) (by norm_num) hB
  have hg := intervalIntegrable_midMajorQuadraticIntegral hnp hrp le_rfl
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  let W := midMajorWeight (midOmega n r) r (midSlope r)
  have hW : Continuous W := by
    change Continuous (fun η : ℝ => midMajorWeight (midOmega n r) r (midSlope r) η)
    unfold midMajorWeight midMajorGap
    fun_prop (disch := intro _; positivity)
  have hcarea : 0 ≤ midMajorPrefactor n r := by unfold midMajorPrefactor; positivity
  have hpoint (η : ℝ) (hη : η ∈ Icc (0 : ℝ) (3 / 2)) :
      midMajorPrefactor n r * ‖midMajorChiIntegral n r η - midMajorQuadraticIntegral n r η‖ ≤
        saddleAmplitude n r / 2 * C * W η := by
    have h₁' := midMajor_inner_relative_error hnp hr hη.1 hh hz
      (midMajorZ_le hnp hrp heps hq hη) hL hκ (hB η hη) (hnear η hη) hphase
    have h₄ := midMajor_quartic_term_le hnp hrp heps hq hκ hη
    have h₁ := (mul_le_mul_of_nonneg_left h₁' hcarea).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (add_le_add_right h₄ _) (by positivity)) hcarea)
    rw [← mul_assoc, midMajor_weight_identity hnp hrp] at h₁
    change _ ≤ _ * W η * C at h₁
    exact h₁.trans_eq (by ring)
  have hscalar := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 3 / 2)
    ((hf.sub hg).norm.const_mul _) ((continuous_const.mul hW).intervalIntegrable _ _) hpoint
  change (∫ η in (0 : ℝ)..(3 / 2), midMajorPrefactor n r *
      ‖midMajorChiIntegral n r η - midMajorQuadraticIntegral n r η‖) ≤
    (∫ η in (0 : ℝ)..(3 / 2), (saddleAmplitude n r / 2 * C) * W η) at hscalar
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hscalar
  have hWint := midMajor_weight_integral_le (r := r) (ρ := midSlope r) ht
  have hTheta : thetaFourthRoot (1 + r⁻¹ ^ 2) ≤ thetaFourthRoot (1 + eps ^ 2) :=
    thetaFourthRoot_mono (add_le_add_right (pow_le_pow_left₀ (inv_nonneg.mpr hrp.le) heps 2) 1)
  have hfinal : (13 / 4) * thetaFourthRoot (1 + r⁻¹ ^ 2) * C ≤
      (243 / 100) * midMajorLocalError eps q h κ := by
    rw [← midMajor_local_error_identity, thetaFourthRoot_mul (x := 13 / 4) (by norm_num)]
    calc
      _ ≤ (13 / 4) * thetaFourthRoot (1 + eps ^ 2) * C := by gcongr
      _ ≤ ((243 / 100) * thetaFourthRoot (13 / 4)) * thetaFourthRoot (1 + eps ^ 2) * C :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          midMajor_central_constant_le (thetaFourthRoot_nonneg _)) hC
      _ = _ := by ring
  have hscalar' := hscalar.trans (mul_le_mul_of_nonneg_left hWint (by positivity))
  have hcomb : midMajorPrefactor n r * (∫ η in (0 : ℝ)..(3 / 2),
      ‖midMajorChiIntegral n r η - midMajorQuadraticIntegral n r η‖) ≤ _ := calc
    _ ≤ saddleAmplitude n r / 2 * C * ((13 / 4) * thetaFourthRoot (1 + r⁻¹ ^ 2)) := hscalar'
    _ = saddleAmplitude n r / 2 * ((13 / 4) * thetaFourthRoot (1 + r⁻¹ ^ 2) * C) := by ring
    _ ≤ saddleAmplitude n r / 2 * ((243 / 100) * midMajorLocalError eps q h κ) :=
      mul_le_mul_of_nonneg_left hfinal (by positivity)
  change ‖(midMajorPrefactor n r : ℂ) * (∫ η in (0 : ℝ)..(3 / 2), midMajorChiIntegral n r η) -
    (midMajorPrefactor n r : ℂ) * ∫ η in (0 : ℝ)..(3 / 2), midMajorQuadraticIntegral n r η‖ ≤ _
  rw [← mul_sub, ← intervalIntegral.integral_sub hf hg, norm_mul, Complex.norm_of_nonneg hcarea]
  exact (mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 3 / 2))
    hcarea).trans hcomb

end DurfeeCCS.Step09
