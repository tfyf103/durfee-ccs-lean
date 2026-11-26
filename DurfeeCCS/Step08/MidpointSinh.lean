module

public import DurfeeCCS.Step08.MidpointLogSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Bounds for the reciprocal hyperbolic sine in the midpoint estimate. -/

@[expose] public section
namespace DurfeeCCS.Step08

open Complex

theorem norm_two_mul_sinh_sq (z : ℂ) :
    ‖2 * Complex.sinh z‖ ^ 2 =
      4 * Real.sinh z.re ^ 2 + 4 * Real.sin z.im ^ 2 := by
  have he : Complex.sinh z =
      (Real.sinh z.re * Real.cos z.im : ℝ) +
        (Real.cosh z.re * Real.sin z.im : ℝ) * I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
    simp only [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, Complex.ofReal_mul, mul_assoc]
  have hc := Real.sin_sq_add_cos_sq z.im
  have hs := Real.cosh_sq_sub_sinh_sq z.re
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, he]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_one, mul_zero, add_zero, zero_mul, sub_zero, zero_add]
  linear_combination 4 * (Real.sinh z.re)^2 * hc + 4 * (Real.sin z.im)^2 * hs

theorem two_div_pi_mul_abs_im_le_norm_two_mul_sinh_half {z : ℂ}
    (hz : |z.im| ≤ Real.pi) : 2 / Real.pi * |z.im| ≤ ‖2 * Complex.sinh (z / 2)‖ := by
  have him : (z / 2).im = z.im / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im]
  have hs : 2 / Real.pi * |z.im / 2| ≤ |Real.sin (z.im / 2)| :=
    Real.mul_abs_le_abs_sin (by rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]; linarith)
  have he := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / Real.pi * |z.im / 2|) hs 2
  rw [sq_abs, abs_div, show |(2 : ℝ)| = 2 by norm_num] at he
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [norm_two_mul_sinh_sq, him]
  nlinarith only [he, sq_nonneg (Real.sinh (z / 2).re)]

theorem two_div_pi_mul_norm_le_norm_two_mul_sinh_half {z : ℂ}
    (hz : ‖z‖ ≤ Real.pi) (hre : 0 ≤ z.re) :
    2 / Real.pi * ‖z‖ ≤ ‖2 * Complex.sinh (z / 2)‖ := by
  have hcre : (z / 2).re = z.re / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
  have hcim : (z / 2).im = z.im / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im]
  have him : |z.im / 2| ≤ Real.pi / 2 := by
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
    exact div_le_div_of_nonneg_right ((Complex.abs_im_le_norm z).trans hz) (by norm_num)
  have hsin := Real.mul_abs_le_abs_sin him
  have hPi : 0 ≤ 2 / Real.pi := by positivity
  have hs := pow_le_pow_left₀ (mul_nonneg hPi (abs_nonneg _)) hsin 2
  rw [mul_pow, sq_abs, sq_abs] at hs
  have hsinh : 2 / Real.pi * (z.re / 2) ≤ Real.sinh (z.re / 2) := by
    have hp : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr Real.two_le_pi
    exact (mul_le_of_le_one_left (by positivity) hp).trans
      (Real.self_le_sinh_iff.mpr (by positivity))
  have hr := pow_le_pow_left₀ (mul_nonneg hPi (by positivity)) hsinh 2
  rw [mul_pow] at hr
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [mul_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, norm_two_mul_sinh_sq,
    hcre, hcim]
  linear_combination 4 * hr + 4 * hs

private theorem sinh_series_term_bound {x : ℝ} (hx : 0 ≤ x) (hx₁ : x ^ 2 ≤ 5 / 2)
    (n : ℕ) :
    2 * x ^ (2 * (n + 1) + 1) / (Nat.factorial (2 * (n + 1) + 1) : ℝ) ≤
      (x ^ 3 / 3) * (1 / 8 : ℝ) ^ n := by
  induction n with
  | zero => norm_num; linarith
  | succ n ih =>
    let k := 2 * (n + 1) + 1
    have hkn : 3 ≤ k := by omega
    have he : 2 * (n + 1 + 1) + 1 = k + 1 + 1 := by omega
    rw [he, Nat.factorial_succ, Nat.factorial_succ, pow_succ, pow_succ, pow_succ]
    change 2 * (x ^ k * x * x) / (↑((k + 1 + 1) * ((k + 1) * (Nat.factorial k))) : ℝ) ≤ _
    push_cast
    have hf : (0 : ℝ) < (Nat.factorial k) := by exact_mod_cast Nat.factorial_pos k
    have hk : (3 : ℝ) ≤ k := by exact_mod_cast hkn
    have hd : (20 : ℝ) ≤ ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1) := by
      nlinarith [sq_nonneg ((k : ℝ) - 3)]
    have hcoef : x ^ 2 / (((k : ℝ) + 1 + 1) * ((k : ℝ) + 1)) ≤ 1 / 8 := by
      apply (div_le_iff₀ (by nlinarith : 0 < ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1))).mpr
      nlinarith
    have hfac : 2 * (x ^ k * x * x) /
      (((k : ℝ) + 1 + 1) * (((k : ℝ) + 1) * ((Nat.factorial k) : ℝ))) =
      (2 * x ^ k / ((Nat.factorial k) : ℝ)) * (x ^ 2 / (((k : ℝ) + 1 + 1) * ((k : ℝ) + 1))) := by
      field_simp
    rw [hfac]
    change 2 * x ^ k / ((Nat.factorial k) : ℝ) ≤ _ at ih
    calc
      _ ≤ (x ^ 3 / 3 * (1 / 8 : ℝ) ^ n) * (1 / 8 : ℝ) :=
        mul_le_mul ih hcoef (by positivity) (by positivity)
      _ = _ := by ring

theorem norm_two_mul_sinh_half_sub_le {z : ℂ} (hz : ‖z‖ ≤ Real.pi) :
    ‖2 * Complex.sinh (z / 2) - z‖ ≤ ‖z‖ ^ 3 / 21 := by
  let h := z / 2
  let x := ‖h‖
  let f (n : ℕ) : ℂ := 2 * (h ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℂ))
  let g (n : ℕ) : ℝ := x ^ 3 / 3 * (1 / 8 : ℝ) ^ n
  have hx : x = ‖z‖ / 2 := by simp [x, h]
  have hx₀ : 0 ≤ x := norm_nonneg h
  have hx₁ : x ^ 2 ≤ 5 / 2 := by
    have hb : x ≤ 3.15 / 2 := by rw [hx]; linarith [Real.pi_lt_d2]
    exact (pow_le_pow_left₀ hx₀ hb 2).trans (by norm_num)
  have hmain : HasSum f (2 * Complex.sinh h) := (Complex.hasSum_sinh h).mul_left 2
  have hf₀ : f 0 = z := by
    norm_num [f, h]
    ring
  have hf : 2 * Complex.sinh h - z = ∑' n : ℕ, f (n + 1) := by
    have ht := hmain.summable.sum_add_tsum_nat_add 1
    rw [hmain.tsum_eq] at ht
    rw [Finset.sum_range_one, hf₀] at ht
    exact (sub_eq_iff_eq_add').mpr ht.symm
  have hg : Summable g := (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hfg (n : ℕ) : ‖f (n + 1)‖ ≤ g n := by
    simp only [f, g, norm_mul, norm_div, norm_pow, Complex.norm_natCast, norm_ofNat, x]
    simpa only [mul_div_assoc] using sinh_series_term_bound hx₀ hx₁ n
  have hfn := hg.of_nonneg_of_le (fun n => norm_nonneg (f (n + 1))) hfg
  change ‖2 * Complex.sinh h - z‖ ≤ ‖z‖ ^ 3 / 21
  rw [hf]
  refine (norm_tsum_le_tsum_norm hfn).trans ((hfn.tsum_le_tsum hfg hg).trans_eq ?_)
  simp only [g, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1), hx]
  ring

theorem norm_inv_two_mul_sinh_half_sub_inv_le {z : ℂ} (hz : ‖z‖ ≤ Real.pi) (hre : 0 < z.re) :
    ‖(2 * Complex.sinh (z / 2))⁻¹ - z⁻¹‖ ≤ 0.08 * ‖z‖ := by
  let s := 2 * Complex.sinh (z / 2)
  have hz₀ : z ≠ 0 := by intro h; simp [h] at hre
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz₀
  have hlow : 2 / Real.pi * ‖z‖ ≤ ‖s‖ := two_div_pi_mul_norm_le_norm_two_mul_sinh_half hz hre.le
  have hsn : 0 < ‖s‖ := (by positivity : 0 < 2 / Real.pi * ‖z‖).trans_le hlow
  have hs₀ := norm_pos_iff.mp hsn
  change ‖s⁻¹ - z⁻¹‖ ≤ _
  rw [show s⁻¹ - z⁻¹ = (z - s) / (s * z) by field_simp [hs₀, hz₀],
    norm_div, norm_mul, norm_sub_rev]
  have hc : ‖s - z‖ ≤ ‖z‖ ^ 3 / 21 := norm_two_mul_sinh_half_sub_le hz
  refine (div_le_div₀ (by positivity : 0 ≤ ‖z‖ ^ 3 / 21) hc (by positivity) (mul_le_mul_of_nonneg_right hlow hn.le)).trans ?_
  have he : (21 : ℝ) ≠ 0 := by norm_num
  rw [show ‖z‖ ^ 3 / 21 / (2 / Real.pi * ‖z‖ * ‖z‖) = (Real.pi / 42) * ‖z‖ by
    field_simp [he, Real.pi_ne_zero, hn.ne']
    norm_num]
  exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_d2]) hn.le

end DurfeeCCS.Step08
