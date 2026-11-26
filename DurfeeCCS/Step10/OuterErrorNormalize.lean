module

public import DurfeeCCS.Step10.OuterErrorModes
import Mathlib.Tactic

/-! The normalization and estimates for the finite part of the Poisson transform. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Complex
open scoped ComplexConjugate

/-- The normalizing amplitude A_y(h) in Proposition 4.1. -/
def outerTransformAmplitude (y h : ℝ) : ℝ :=
  h * Real.exp (y * (outerRho h π).re) / (4 * π * y ^ 2)

theorem outerTransformAmplitude_pos {y h : ℝ} (hy : 0 < y) (hh : 0 < h) :
    0 < outerTransformAmplitude y h := by
  unfold outerTransformAmplitude
  positivity

theorem outerRho_conj {h v : ℝ} (hh : 0 < h) :
    outerRho h (-v) = conj (outerRho h v) := by
  have h₁ : outerRho h (-v) ^ 2 = conj (outerRho h v) ^ 2 := by
    rw [← map_pow]
    unfold outerRho
    rw [outerRhoAt_sq, outerRhoAt_sq]
    simp only [map_add, map_pow, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg]
    ring
  have he : (outerRho h (-v) - conj (outerRho h v)) *
      (outerRho h (-v) + conj (outerRho h v)) = 0 := by
    linear_combination h₁
  have hp : 0 < (outerRho h (-v) + conj (outerRho h v)).re := by
    rw [Complex.add_re, Complex.conj_re]
    linarith [outerRho_re_gt (t := -v) hh, outerRho_re_gt (t := v) hh]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (fun hz => by simp [hz] at hp))

theorem outerEndpointMain_conj (y : ℝ) (ρ : ℂ) :
    outerEndpointMain y (conj ρ) = conj (outerEndpointMain y ρ) := by
  unfold outerEndpointMain
  simp only [map_div₀, map_mul, map_pow, Complex.conj_ofReal, map_ofNat, ← Complex.exp_conj]

/-- Comparison of the scales on the reduced outer range. -/
theorem outerError_scale {y₀ y h : ℝ} (hy₀ : 80 ≤ y₀) (hy : (9 / 10 : ℝ) * y₀ ≤ y)
    (hh : 8.76 < h) (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    72 ≤ y ∧ h / y < 0.240 ∧ 1 ≤ y * h := by
  have hy₀' : 0 < y₀ := by linarith
  have hy' : (72 : ℝ) ≤ y := by linarith
  have hypos : 0 < y := by linarith
  have hp : 18.5663553344511 < y₀ ^ (2 / 3 : ℝ) :=
    DurfeeCCS.Step07.outerEightyPow_lo.trans_le
      (Real.rpow_le_rpow (by norm_num) hy₀ (by norm_num))
  have hr : y₀ ^ (1 / 3 : ℝ) * y₀ ^ (2 / 3 : ℝ) = y₀ := by
    rw [← rpow_add hy₀', show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, rpow_one]
  have ht : 0 < y₀ ^ (1 / 3 : ℝ) := rpow_pos_of_pos hy₀' _
  refine ⟨hy', (div_lt_iff₀ hypos).2 ?_, ?_⟩
  · calc
      h ≤ 4 * y₀ ^ (1 / 3 : ℝ) := hcap
      _ < (0.240 * (9 / 10) * (y₀ ^ (2 / 3 : ℝ))) * y₀ ^ (1 / 3 : ℝ) := by
        apply mul_lt_mul_of_pos_right _ ht
        linarith
      _ = 0.240 * ((9 / 10 : ℝ) * y₀) := by
        conv_rhs => rw [← hr]
        ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ (72 : ℝ) * 8.76 := by norm_num
      _ ≤ _ := by gcongr

private theorem norm_pair_relative {y h v : ℝ} (hy : 0 < y) (hh : 0 < h) :
    (‖outerEndpointMain y (outerRho h v)‖ +
      ‖outerEndpointMain y (outerRho h (-v))‖) / outerTransformAmplitude y h =
      ‖outerRho h v‖ / h * Real.exp (y * ((outerRho h v).re - (outerRho h π).re)) := by
  rw [outerRho_conj hh, outerEndpointMain_conj, Complex.norm_conj, norm_outerEndpointMain hy,
    outerTransformAmplitude, mul_sub, Real.exp_sub]
  field_simp
  ring

theorem outerLow_leading_pair {y h : ℝ} (hy : 0 < y) (hh : 8.76 < h) :
    (‖outerEndpointMain y (outerRho h π)‖ +
      ‖outerEndpointMain y (outerRho h (-π))‖) / outerTransformAmplitude y h < 1.142 := by
  have hh₀ : 0 < h := by linarith
  rw [norm_pair_relative hy hh₀, sub_self, mul_zero, Real.exp_zero, mul_one]
  exact (div_lt_iff₀ hh₀).2 (outerRho_norm_pi hh)

theorem outerLow_nonleading_pair {y h : ℝ} (hy : 0 < y) (m : ℕ)
    (hv : outerPositiveFrequency (m + 1) ≤ h) :
    let v := outerPositiveFrequency (m + 1)
    (‖outerEndpointMain y (outerRho h v)‖ +
      ‖outerEndpointMain y (outerRho h (-v))‖) / outerTransformAmplitude y h ≤
      1.47 * Real.exp (-(26 * π ^ 4 * y / (25 * h ^ 3)) * ((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  dsimp only
  let v := outerPositiveFrequency (m + 1)
  have hv₀ : 0 < v := outerPositiveFrequency_pos _
  have hh₀ : 0 < h := hv₀.trans_le hv
  have hv₃ : 3 * π ≤ |v| := by
    rw [abs_of_pos hv₀]
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    simp [v, outerPositiveFrequency, outerFrequency]
    nlinarith [mul_nonneg hm' pi_pos.le]
  have hmax : |v| ≤ h := by rwa [abs_of_pos hv₀]
  rw [norm_pair_relative hy hh₀]
  have hb : ‖outerRho h v‖ / h ≤ 1.47 := (div_le_iff₀ hh₀).2 (outerRho_norm_low hv₃ hmax).le
  have hg := outerRho_re_low_gap hv₃ hmax
  have hV : v ^ 2 - π ^ 2 = 4 * π ^ 2 * ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
    simp [v, outerPositiveFrequency, outerFrequency]
    ring
  have hd : y * ((outerRho h v).re - (outerRho h π).re) ≤
      -(26 * π ^ 4 * y / (25 * h ^ 3)) * ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
    have H := mul_le_mul_of_nonneg_left hg.le hy.le
    rw [hV] at H
    rw [show -(26 * π ^ 4 * y / (25 * h ^ 3)) * ((m : ℝ) + 1) * ((m : ℝ) + 2) =
      -(y * (13 * π ^ 2 * (4 * π ^ 2 * ((m : ℝ) + 1) * ((m : ℝ) + 2)) /
        (50 * h ^ 3))) by ring]
    linarith
  exact mul_le_mul hb (exp_le_exp.mpr hd) (exp_nonneg _) (by norm_num)

/-- Lower bounds on y/h and y/h^3 throughout the reduced outer range. -/
theorem outerError_scale_lower {y₀ y h : ℝ} (hy₀ : 80 ≤ y₀) (hy : (9 / 10 : ℝ) * y₀ ≤ y)
    (hh : 0 < h) (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    9 * y₀ ^ (2 / 3 : ℝ) / 40 ≤ y / h ∧ (9 / 640 : ℝ) ≤ y / h ^ 3 := by
  have hy₀' : 0 < y₀ := by linarith
  have hr : y₀ ^ (2 / 3 : ℝ) * y₀ ^ (1 / 3 : ℝ) = y₀ := by
    rw [← Real.rpow_add hy₀', show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one]
  have hc : (4 * y₀ ^ (1 / 3 : ℝ)) ^ 3 = 64 * y₀ := by
    rw [mul_pow, ← Real.rpow_mul_natCast hy₀'.le,
      show (1 / 3 : ℝ) * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
    norm_num
  constructor
  · apply (le_div_iff₀ hh).2
    calc
      _ ≤ (9 * y₀ ^ (2 / 3 : ℝ) / 40) * (4 * y₀ ^ (1 / 3 : ℝ)) := by gcongr
      _ = (9 / 10 : ℝ) * y₀ := by
        conv_rhs => rw [← hr]
        ring
      _ ≤ _ := hy
  · apply (le_div_iff₀ (pow_pos hh 3)).2
    calc
      _ ≤ (9 / 640 : ℝ) * (4 * y₀ ^ (1 / 3 : ℝ)) ^ 3 := by gcongr
      _ = (9 / 10 : ℝ) * y₀ := by rw [hc]; ring
      _ ≤ _ := hy

end DurfeeCCS.Step10
