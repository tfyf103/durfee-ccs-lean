module

public import DurfeeCCS.Step10.OuterBesselKernel
public import DurfeeCCS.Step10.OuterCoeffData
public import DurfeeCCS.Step10.OuterSigns
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open DurfeeCCS.Step06 Real

/-- The pointwise coefficient error used to replace an integer coefficient by a Bessel value. -/
def OuterCoefficientError : Prop :=
  ∀ t : ℕ, 0 < t →
    |(twoColourPartitionCount t : ℝ) - outerBesselMain (twoColourShift t)| ≤
      π ^ 3 / 36 * exp (π * sqrt ((t : ℝ) / 3))

/-- Extend the two-colour coefficients by zero to negative indices. -/
def clippedTwoColour (t : ℤ) : ℝ :=
  if 0 ≤ t then twoColourPartitionCount t.toNat else 0

/-- The replacement estimate at every integer argument, including the zero endpoint. -/
theorem outerKernelReplacement (hCoeff : OuterCoefficientError) {y x : ℝ} {t : ℤ}
    (hy : 0 ≤ y) (ht : y ^ 2 - x ^ 2 = (t : ℝ) - 1 / 12) :
    |clippedTwoColour t - outerBesselKernel y x| ≤
      π ^ 3 / 18 * exp (π * sqrt ((t.toNat : ℝ) / 3)) := by
  by_cases ht₀ : t ≤ 0
  · have ht₀' : (t : ℝ) ≤ 0 := by exact_mod_cast ht₀
    have hsq : y ^ 2 < x ^ 2 := by linarith only [ht, ht₀']
    rw [outerBesselKernel, ite_eq_right hsq.not_ge, sub_zero, clippedTwoColour]
    have hπ : (1 : ℝ) < π ^ 3 / 18 := by
      have hp := pow_lt_pow_left₀ pi_gt_d2 (by norm_num) (n := 3) (by decide)
      linarith
    rcases lt_or_eq_of_le ht₀ with htneg | rfl
    · simp only [ite_eq_right htneg.not_ge, abs_zero]
      positivity
    · norm_num [twoColourPartitionCount_zero]
      exact hπ.le
  · have ht' : (0 : ℤ) < t := lt_of_not_ge ht₀
    have htN : 0 < t.toNat := by omega
    have htEq : (t.toNat : ℝ) = t := by exact_mod_cast Int.toNat_of_nonneg ht'.le
    have hu : 0 < y ^ 2 - x ^ 2 := by
      have ht1 : (1 : ℝ) ≤ t.toNat := by exact_mod_cast htN
      linarith only [ht, htEq, ht1]
    have hk : ‖x‖ < y := by
      have hp := (sq_lt_sq).mp (show x ^ 2 < y ^ 2 by linarith only [hu])
      rw [Real.norm_eq_abs, ← abs_of_nonneg hy]
      exact hp
    have hY : 0 < y := (norm_nonneg x).trans_lt hk
    rw [clippedTwoColour, ite_eq_left ht'.le, outerBesselKernel_eq_bessel hY
      (by simpa only [Real.norm_eq_abs] using hk)]
    rw [← htEq, ← twoColourShift_sq htN] at ht
    rw [ht, Real.sqrt_sq (twoColourShift_pos htN).le]
    have harg : 2 * π / sqrt 3 * twoColourShift t.toNat = 2 * π * twoColourShift t.toNat / sqrt 3 := by ring
    rw [harg, ← outerBesselMain]
    have hB : 0 ≤ π ^ 3 / 36 := by positivity
    have hE : 1 ≤ exp (π * sqrt ((t.toNat : ℝ) / 3)) := one_le_exp (by positivity)
    calc
      _ = |(twoColourPartitionCount t.toNat : ℝ) - outerBesselMain (twoColourShift t.toNat) +
          π ^ 3 / 36| := by rw [sub_sub_eq_add_sub, add_sub_right_comm]
      _ ≤ |(twoColourPartitionCount t.toNat : ℝ) - outerBesselMain (twoColourShift t.toNat)| +
          π ^ 3 / 36 := by
        have H := abs_add_le ((twoColourPartitionCount t.toNat : ℝ) -
          outerBesselMain (twoColourShift t.toNat)) (π ^ 3 / 36)
        rwa [abs_of_nonneg hB] at H
      _ ≤ _ := by
        have h := hCoeff t.toNat htN
        have h' := mul_le_mul_of_nonneg_left hE hB
        linarith only [h, h']

/-- Compare shifted Bessel amplitudes using the square-radius deficit. -/
theorem outerAmplitude_ratio {y Y h γ : ℝ} (hY : 80 ≤ Y) (hy : Y / 2 ≤ y) (hyY : y ≤ Y)
    (hh : 8.76 < h) (hγ : Y ^ 2 - y ^ 2 = γ) :
    outerTransformAmplitude y h / outerTransformAmplitude Y h ≤
      exp (-((outerRho h π).re - 4 / Y) / (2 * Y) * γ) := by
  let a := (outerRho h π).re
  have hY₀ : 0 < Y := by linarith
  have hy₀ : 0 < y := by linarith
  have hh₀ : 0 < h := by linarith
  have ha : h < a := outerRho_re_gt hh₀
  have hσ : 0 < a - 4 / Y := by
    have h₄ : 4 / Y ≤ 1 / 20 := by
      apply (div_le_iff₀ hY₀).2
      linarith
    linarith only [ha, hh, h₄]
  have hr := Real.log_le_sub_one_of_pos (div_pos hY₀ hy₀)
  have hr' : 2 * log (Y / y) ≤ 4 * (Y - y) / Y := by
    have h₁ : Y / y - 1 = (Y - y) / y := by field_simp
    have h₂ : (Y - y) / y ≤ (Y - y) / (Y / 2) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hyY) (by positivity) hy
    rw [h₁] at hr
    rw [div_div_eq_mul_div] at h₂
    linear_combination 2 * h₂ + 2 * hr
  have hgap : γ / (2 * Y) ≤ Y - y := by
    apply (div_le_iff₀ (by positivity)).2
    rw [← hγ]
    have hp := mul_nonneg (sub_nonneg.mpr hyY) (sub_nonneg.mpr hyY)
    nlinarith only [hp]
  have hA : outerTransformAmplitude y h / outerTransformAmplitude Y h =
      exp (2 * log (Y / y) - a * (Y - y)) := by
    unfold outerTransformAmplitude
    rw [exp_sub, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, exp_nat_mul,
      exp_log (div_pos hY₀ hy₀),
      show a * (Y - y) = Y * a - y * a by ring, exp_sub]
    change h * exp (y * a) / (4 * π * y ^ 2) / (h * exp (Y * a) / (4 * π * Y ^ 2)) = _
    field_simp
  rw [hA]
  apply exp_le_exp.mpr
  have hp := mul_le_mul_of_nonneg_left hgap hσ.le
  calc
    _ ≤ 4 * (Y - y) / Y - a * (Y - y) := by linarith only [hr']
    _ = -(a - 4 / Y) * (Y - y) := by ring
    _ ≤ -(a - 4 / Y) / (2 * Y) * γ := by
      linear_combination hp

end DurfeeCCS.Step10
