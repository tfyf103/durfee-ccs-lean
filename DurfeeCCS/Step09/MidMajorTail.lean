module

public import DurfeeCCS.Step09.MidMajorIntegral
public import DurfeeCCS.Step09.MidMultiplierUniform

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integral estimates on the remainder of the main positive half-arc. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

private theorem thetaFourthRoot_two_le : thetaFourthRoot 2 ≤ 1.19 := by
  apply (pow_le_pow_iff_left₀ (thetaFourthRoot_nonneg _) (by norm_num) (n := 4) (by decide)).mp
  rw [thetaFourthRoot_four (by norm_num)]
  norm_num

private theorem sqrt_pi_lower : (1.77 : ℝ) ≤ Real.sqrt Real.pi :=
  Real.le_sqrt_of_sq_le (by linarith only [Real.pi_gt_d2, show (1.77 : ℝ) ^ 2 < 3.14 by norm_num])

private theorem midMajor_weight_bound {t r ρ η d S : ℝ} (ht : 0 < t) (hr : 1 ≤ r)
    (hgap : d ≤ midMajorGap ρ η) (hS : Real.sqrt (1 + η ^ 2) ≤ S) :
    midMajorWeight t r ρ η ≤ (1.19 * S / 1.77) * Real.sqrt t * Real.exp (-t * d) := by
  have hr0 : 0 < r := by linarith
  have hr1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  have hSn : 0 ≤ S := (Real.sqrt_nonneg _).trans hS
  have hρ : 1 ≤ Real.sqrt (1 + ρ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ρ])
  have hΘ : thetaFourthRoot (1 + r⁻¹ ^ 2) ≤ 1.19 := by
    refine (thetaFourthRoot_mono ?_).trans thetaFourthRoot_two_le
    have hp := pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) hr1 2
    nlinarith only [hp]
  unfold midMajorWeight
  have hΘ₀ := thetaFourthRoot_nonneg (1 + r⁻¹ ^ 2)
  apply (div_le_self (by positivity) hρ).trans
  rw [Real.sqrt_div ht.le]
  have hRt : Real.sqrt t / Real.sqrt Real.pi ≤ Real.sqrt t / 1.77 :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) sqrt_pi_lower
  have hE : Real.exp (-t * midMajorGap ρ η) ≤ Real.exp (-t * d) :=
    Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hgap ht.le))
  calc
    _ ≤ (Real.sqrt t / 1.77) * 1.19 * S * Real.exp (-t * d) :=
      mul_le_mul (mul_le_mul (mul_le_mul hRt hΘ hΘ₀ (by positivity)) hS
        (Real.sqrt_nonneg _) (by positivity)) hE (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

/-- A one-interval version of the (59) estimate before the two numerical constants are inserted. -/
theorem midMajor_eta_interval_le {n : ℕ} (hn : 0 < n) {r l h ρhi C S : ℝ}
    (hr : 1 ≤ r) (hρ : midSlope r ≤ ρhi) (hρl : ρhi ≤ l) (hlh : l ≤ h)
    (hC : 0 ≤ C) (hS : Real.sqrt (1 + h ^ 2) ≤ S)
    (hB : ∀ η ∈ Icc l h, ∀ χ : ℝ, ‖midMultiplier r 0 (midEtaPoint n r η) χ‖ ≤ C) :
    ‖midContribution n r 0 l h‖ ≤ saddleAmplitude n r / 2 *
      ((h - l) * C * (1.19 * S / 1.77) * Real.sqrt (midOmega n r) *
        Real.exp (-midOmega n r * midMajorGap ρhi l)) := by
  have hrp : 0 < r := by linarith
  have hu := saddleU_pos hn hrp
  have ht := saddleOmega_pos hn hrp
  have hM := saddleAmplitude_pos hn hrp
  have hρp := (midSlope_bounds hrp).1
  have hρhi : 0 ≤ ρhi := hρp.le.trans hρ
  have hl : 0 ≤ l := hρhi.trans hρl
  let T := C * (1.19 * S / 1.77) * Real.sqrt (midOmega n r) *
        Real.exp (-midOmega n r * midMajorGap ρhi l)
  have hA : 0 ≤ midMajorPrefactor n r := by
    unfold midMajorPrefactor
    exact div_nonneg hu.le (by positivity)
  have hc (η : ℝ) (hη : η ∈ Icc l h) :
      ‖(midMajorPrefactor n r : ℂ) * midMajorChiIntegral n r η‖ ≤ saddleAmplitude n r / 2 * T := by
    have hη₀ := hl.trans hη.1
    have hL : midMajorGap ρhi l ≤ midMajorGap (midSlope r) η :=
      ((midMajorGap_monotone hρhi) hρl (hρl.trans hη.1) hη.1).trans
        (midMajorGap_anti_slope hρ (hρl.trans hη.1))
    have hSh := (Real.sqrt_le_sqrt (add_le_add le_rfl (pow_le_pow_left₀ hη₀ hη.2 2))).trans hS
    have hb := midMajor_chi_integral_norm_le hn hr hη₀ hC (hB η hη)
    rw [norm_mul, Complex.norm_of_nonneg hA]
    calc
      _ ≤ midMajorPrefactor n r * (C * (Real.exp (midMajorBaseExponent n r η) *
          Real.sqrt (Real.pi / midDamping n r η))) := mul_le_mul_of_nonneg_left hb hA
      _ = C * (midMajorPrefactor n r * (Real.exp (midMajorBaseExponent n r η) *
          Real.sqrt (Real.pi / midDamping n r η))) := by ring
      _ = C * (saddleAmplitude n r / 2 * midMajorWeight (midOmega n r) r (midSlope r) η) := by
        rw [midMajor_weight_identity hn hrp]
      _ ≤ _ := by
        have hh := midMajor_weight_bound ht hr hL hSh
        exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by positivity)) hC).trans_eq
          (by unfold T; ring)
  change ‖(midMajorPrefactor n r : ℂ) * ∫ η in l..h, midMajorChiIntegral n r η‖ ≤ _
  rw [← intervalIntegral.integral_const_mul]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := h) (f := fun η => (midMajorPrefactor n r : ℂ) * midMajorChiIntegral n r η)
    (fun η hη => by
      rw [uIoc_of_le hlh] at hη
      exact hc η ⟨hη.1.le, hη.2⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr hlh)] at hbound
  apply hbound.trans_eq
  unfold T
  ring

theorem midMajor_eta_tail_le {n : ℕ} {r ρhi : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hρ : midSlope r ≤ ρhi) (hρhi : ρhi ≤ 3 / 2) :
    ‖midContribution n r 0 (3 / 2) 8‖ ≤
      saddleAmplitude n r / 2 * midMajorEtaError (midOmega n r)
        (midMajorGap ρhi (3 / 2)) (midMajorGap ρhi 3) := by
  have hn' : 0 < n := by omega
  have hM : 0 < saddleAmplitude n r := saddleAmplitude_pos hn' (by linarith)
  have hb₁ (η : ℝ) (hη : η ∈ Icc (3 / 2 : ℝ) 3) (χ : ℝ) :
      ‖midMultiplier r 0 (midEtaPoint n r η) χ‖ ≤ 30 :=
    (norm_midMultiplier_lt_30 hn hr hmax (by
      rw [abs_of_nonneg (by linarith only [hη.1])]
      exact hη.2) 0 χ).le
  have hb₂ (η : ℝ) (hη : η ∈ Icc (3 : ℝ) 8) (χ : ℝ) :
      ‖midMultiplier r 0 (midEtaPoint n r η) χ‖ ≤ 2100 :=
    (norm_midMultiplier_lt_2100 hn hr hmax (by
      rw [abs_of_nonneg (by linarith only [hη.1])]
      exact hη.2) 0 χ).le
  have hi₁ := intervalIntegrable_midMajorChiIntegral hn' hr
    (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num) (by norm_num) hb₁
  have hi₂ := intervalIntegrable_midMajorChiIntegral hn' hr
    (by norm_num : (0 : ℝ) ≤ 3) (by norm_num) (by norm_num) hb₂
  have h₁ := midMajor_eta_interval_le (S := 3.163) hn' hr hρ hρhi (by norm_num) (by norm_num)
    ((Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩) hb₁
  have h₂ := midMajor_eta_interval_le (S := 8.063) hn' hr hρ
    (by linarith : ρhi ≤ 3) (by norm_num) (by norm_num)
    ((Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩) hb₂
  have hsplit : midContribution n r 0 (3 / 2) 8 =
      midContribution n r 0 (3 / 2) 3 + midContribution n r 0 3 8 := by
    change (midMajorPrefactor n r : ℂ) * (∫ η in (3 / 2 : ℝ)..8, midMajorChiIntegral n r η) =
      (midMajorPrefactor n r : ℂ) * (∫ η in (3 / 2 : ℝ)..3, midMajorChiIntegral n r η) +
      (midMajorPrefactor n r : ℂ) * (∫ η in (3 : ℝ)..8, midMajorChiIntegral n r η)
    rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans ?_)
  unfold midMajorEtaError
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · gcongr
    norm_num
  · gcongr
    norm_num

end DurfeeCCS.Step09
