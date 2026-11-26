module

public import DurfeeCCS.Step09.MidMajorCentral
public import DurfeeCCS.Step09.MidGaussianModel

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Normalization of the inner errors by the exact complex Gaussian. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

/-- The real Gaussian majorant and the complex Gaussian have the ratio used before (58). -/
theorem midMajor_real_mass_eq_complex_norm {n : ℕ} (hn : 0 < n) {r η : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) :
    Real.exp (midMajorBaseExponent n r η) * Real.sqrt (Real.pi / midDamping n r η) =
      thetaFourthRoot ((1 + η ^ 2) * (1 + r⁻¹ ^ 2)) * ‖midMajorQuadraticIntegral n r η‖ := by
  let u := midU n r
  let Θ := thetaFourthRoot (1 + r⁻¹ ^ 2)
  let Y := thetaFourthRoot (1 + η ^ 2)
  have hu : 0 < u := saddleU_pos hn hr
  have hΘ : 0 < Θ := thetaFourthRoot_pos (by positivity)
  have hY : 0 < Y := thetaFourthRoot_pos (by positivity)
  have hΘ₂ : Θ ^ 2 = Real.sqrt (1 + r⁻¹ ^ 2) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hY₂ : Y ^ 2 = Real.sqrt (1 + η ^ 2) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hnr : ‖midCurvature r‖ = (Θ ^ 2)⁻¹ := by
    rw [norm_saddleBesselSlope hr, hΘ₂]
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [div_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hs : ‖(midCurvature r).sqrt‖ = Θ⁻¹ := by
    rw [norm_principalSqrt, hnr, Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hΘ]
  have hy : ‖(midModelZ η).sqrt‖ = Y := by
    rw [norm_principalSqrt]
    have hz : ‖midModelZ η‖ = Real.sqrt (1 + η ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, verticalPoint_re, verticalPoint_im]
      norm_num
    rw [hz]
    rfl
  have hBase : ((n : ℂ) * midEtaPoint n r η + saddleS r ^ 2 / midEtaPoint n r η).re =
      midMajorBaseExponent n r η := by
    rw [re_midSaddle_exponent hn hr]
    unfold midMajorBaseExponent midMajorGap
    ring
  rw [midMajorQuadraticIntegral, integral_midGaussian_inner hn hr hη, norm_mul, norm_mul, norm_div,
    hs, hy, Complex.norm_exp, Complex.norm_of_nonneg (Real.sqrt_nonneg _), hBase,
    div_eq_mul_inv, midMajor_inv_damping hn hr, thetaFourthRoot_mul (by positivity)]
  change Real.exp (midMajorBaseExponent n r η) *
      Real.sqrt (Real.pi * (u * (1 + η ^ 2) * (1 + r⁻¹ ^ 2))) =
    Y * Θ * (Real.exp (midMajorBaseExponent n r η) * (Real.sqrt (Real.pi * u) / Θ⁻¹) * Y)
  have hroot : Real.sqrt (Real.pi * (u * (1 + η ^ 2) * (1 + r⁻¹ ^ 2))) =
      Real.sqrt (Real.pi * u) * Y ^ 2 * Θ ^ 2 := by
    rw [← mul_assoc Real.pi _ _, ← mul_assoc Real.pi u _, Real.sqrt_mul (by positivity : 0 ≤
      Real.pi * u * (1 + η ^ 2)), Real.sqrt_mul (by positivity : 0 ≤ Real.pi * u), hY₂, hΘ₂]
  rw [hroot, div_inv_eq_mul]
  ring



/-- The three terms in (58) bound the relative error of each inner Gaussian integral. -/
theorem midMajor_inner_error_eq58 {n : ℕ} {r η eps q h κ : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (heps : r⁻¹ ≤ eps) (hq : midU n r ≤ q) (hh : 0 < h) (hκ : 0 ≤ κ)
    (hη : η ∈ Icc (0 : ℝ) (3 / 2)) (hL : 0 ≤ midMajorLocalLog eps q h)
    (hnear : ∀ χ ∈ Icc (-h) h,
      ‖midMultiplier r 0 (midEtaPoint n r η) χ - 1‖ ≤ Real.exp (midMajorLocalLog eps q h) - 1)
    (hphase : ∀ χ ∈ Icc (-h) h, ‖midPhase r 0 χ - (saddleS r ^ 2 - midCurvature r * (χ : ℂ) ^ 2)‖
      ≤ κ / r * χ ^ 4) :
    ‖midMajorChiIntegral n r η - midMajorQuadraticIntegral n r η‖ ≤
      ‖midMajorQuadraticIntegral n r η‖ * midMajorLocalError eps q h κ := by
  have hnp : 0 < n := by omega
  have hrp : 0 < r := by linarith
  have hu := saddleU_pos hnp hrp
  have hq' := hu.trans_le hq
  have heps' : 0 ≤ eps := (inv_nonneg.mpr hrp.le).trans heps
  have hz : 0 < midMajorZ eps q h := by unfold midMajorZ; positivity
  let C := (119 / 10) * (Real.exp (-midMajorZ eps q h) / Real.sqrt (Real.pi * midMajorZ eps q h)) +
    (Real.exp (midMajorLocalLog eps q h) - 1) +
      (3 / 4) * κ * eps * q * (Real.sqrt (13 / 4)) ^ 3 * (1 + eps ^ 2) ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    have := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hL)
    positivity
  have hB (χ : ℝ) : ‖midMultiplier r 0 (midEtaPoint n r η) χ‖ ≤ 10.9 :=
    (norm_midMultiplier_lt_10_9 hn hr hmax (by simpa [abs_of_nonneg hη.1] using hη.2) 0 χ).le
  have hInner := midMajor_inner_relative_error hnp hr hη.1 hh hz
    (midMajorZ_le hnp hrp heps hq hη) hL hκ hB hnear hphase
  have hFour := midMajor_quartic_term_le hnp hrp heps hq hκ hη
  have hDiv := hInner.trans (mul_le_mul_of_nonneg_left (add_le_add_right hFour _) (by positivity))
  have hroot := midMajor_real_mass_eq_complex_norm hnp hrp hη.1
  rw [hroot] at hDiv
  change _ ≤ thetaFourthRoot ((1 + η ^ 2) * (1 + r⁻¹ ^ 2)) * ‖midMajorQuadraticIntegral n r η‖ * C at hDiv
  have hBη : thetaFourthRoot ((1 + η ^ 2) * (1 + r⁻¹ ^ 2)) ≤
      thetaFourthRoot ((13 / 4) * (1 + eps ^ 2)) := by
    apply thetaFourthRoot_mono
    gcongr
    nlinarith only [pow_le_pow_left₀ hη.1 hη.2 2]
  apply hDiv.trans
  calc
    _ ≤ thetaFourthRoot ((13 / 4) * (1 + eps ^ 2)) * ‖midMajorQuadraticIntegral n r η‖ * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBη (norm_nonneg _)) hC
    _ = ‖midMajorQuadraticIntegral n r η‖ *
        (thetaFourthRoot ((13 / 4) * (1 + eps ^ 2)) * C) := by ring
    _ = _ := by rw [midMajor_local_error_identity]


end DurfeeCCS.Step09
