module

public import DurfeeCCS.Step10.OuterRho
public import DurfeeCCS.Step07.OuterTable
public import DurfeeCCS.Step07.PowerDecay

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Numerical majorants for the three preprocessing errors on pages 44 and 45. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Set DurfeeCCS.Step07

private theorem cubicRoot_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 3 : ℝ)) ^ (2 : ℕ) = x ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

private theorem cubicRoot_eighth {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 3 : ℝ)) ^ (8 : ℕ) = x ^ (8 / 3 : ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  norm_num

/-- Endpoint bound for the contribution of the discarded small shifted radii. -/
theorem smallRadius_majorant_lt {y : ℝ} (hy : 80 ≤ y) :
    (15 * π * y ^ 3 / 8) * exp (-0.315 * y + 0.010) < 0.00004 := by
  have hm := power_mul_exp_antitoneOn (x₀ := 80) (a := 0.315) (b := 0.010)
    3 1 (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
  have h := hm (show (80 : ℝ) ∈ Ici 80 from le_rfl) hy hy
  simp only [pow_one] at h
  have hp : (15 * π * y ^ 3 / 8) * exp (-0.315 * y + 0.010) ≤
      (15 * π * (80 : ℝ) ^ 3 / 8) * exp (-0.315 * 80 + 0.010) := by
    convert mul_le_mul_of_nonneg_left h (show 0 ≤ 15 * π / 8 by positivity) using 1 <;> ring
  apply hp.trans_lt
  have hExp : exp (-25.19 : ℝ) < 0.0000000000116 := by
    dyadic_interval +kernel [prec := 64]
  rw [show (-0.315 * 80 + 0.010 : ℝ) = -25.19 by norm_num]
  calc
    _ ≤ (15 * (3.141593 : ℝ) * 80 ^ 3 / 8) * 0.0000000000116 := by
      gcongr
      exact Real.pi_lt_d6.le
    _ < _ := by norm_num

/-- Endpoint bound after maximizing the kernel replacement majorant over the upper cap for h. -/
theorem kernelSwap_cap_majorant_lt {y : ℝ} (hy : 80 ≤ y) :
    5 * π * y ^ (8 / 3 : ℝ) * exp (-π ^ 2 * y ^ (2 / 3 : ℝ) / 10 + 0.010) < 0.0208 := by
  let T := (80 : ℝ) ^ (1 / 3 : ℝ)
  let t := y ^ (1 / 3 : ℝ)
  have hy₀ : 0 ≤ y := (by norm_num : (0 : ℝ) ≤ 80).trans hy
  have hT : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have ht : T ≤ t := Real.rpow_le_rpow (by norm_num) hy (by norm_num)
  have hThresh : (8 : ℝ) ≤ π ^ 2 / 10 * (2 : ℕ) * T ^ 2 := by
    dsimp [T]
    rw [cubicRoot_sq (by norm_num)]
    have hlo := outerPi_gt
    have hpow := outerEightyPow_lo
    calc
      _ ≤ (3.14159265358979 : ℝ) ^ 2 / 10 * 2 * 18.5663553344511 := by norm_num
      _ ≤ _ := by gcongr
  have hm := power_mul_exp_antitoneOn (b := 0.010) 8 2 (by decide) (by decide)
    hT (by positivity : 0 ≤ π ^ 2 / 10) hThresh
  have hs := hm (show T ∈ Ici T from le_rfl) ht ht
  have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 5 * π by positivity)
  have hrewrite (x : ℝ) (hx : 0 ≤ x) :
      5 * π * ((x ^ (1 / 3 : ℝ)) ^ (8 : ℕ) *
        exp (-(π ^ 2 / 10) * (x ^ (1 / 3 : ℝ)) ^ (2 : ℕ) + 0.010)) =
      5 * π * x ^ (8 / 3 : ℝ) * exp (-π ^ 2 * x ^ (2 / 3 : ℝ) / 10 + 0.010) := by
    rw [cubicRoot_sq hx, cubicRoot_eighth hx,
      show -(π ^ 2 / 10) * x ^ (2 / 3 : ℝ) = -π ^ 2 * x ^ (2 / 3 : ℝ) / 10 by ring]
    ring
  dsimp only [T, t, Nat.cast_ofNat] at h
  rw [hrewrite _ hy₀, hrewrite _ (by norm_num)] at h
  apply h.trans_lt
  let s := (80 : ℝ) ^ (2 / 3 : ℝ)
  have hs' : (80 : ℝ) ^ (8 / 3 : ℝ) = s ^ 4 := by
    dsimp [s]
    rw [← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    norm_num
  rw [hs']
  have hlo := outerPi_gt
  have hhi := outerPi_lt
  have hslo : 18.5663553344511 < s := outerEightyPow_lo
  have hshi : s < 18.5663553344512 := outerEightyPow_hi
  have hExp₁ : -(π ^ 2 * s / 10) + 0.010 ≤ -18.314 := by
    have h := mul_le_mul (pow_le_pow_left₀ (by norm_num) hlo.le 2) hslo.le
      (by norm_num) (by positivity : 0 ≤ π ^ 2)
    linarith only [h]
  have hExp₂ : exp (-18.314 : ℝ) < 1.113e-8 := by
    dyadic_interval +kernel [prec := 57]
  have hExp : exp (-π ^ 2 * s / 10 + 0.010) < 1.113e-8 := by
    exact (Real.exp_le_exp.mpr (by linarith only [hExp₁])).trans_lt hExp₂
  calc
    _ ≤ 5 * 3.14159265358980 * (18.5663553344512 : ℝ) ^ 4 * 1.113e-8 := by
      gcongr
    _ < _ := by norm_num

/-- Uniform numerical bound on the replacement error throughout the outer Bessel range. -/
theorem kernelSwap_majorant_lt {y h : ℝ} (hy : 80 ≤ y) (hh : 0 < h)
    (hhCap : h ≤ 4 * y ^ (1 / 3 : ℝ)) :
    20 * π / h * y ^ 3 * exp (-(2 * π ^ 2 * y / (5 * h)) + 0.010) < 0.0208 := by
  let τ := y ^ (1 / 3 : ℝ)
  let H := 4 * τ
  let a := 2 * π ^ 2 * y / 5
  have hy₀ : 0 < y := by linarith
  have hτ : 0 < τ := Real.rpow_pos_of_pos hy₀ _
  have hH : 0 < H := by dsimp [H]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hlarge : 1 ≤ a * H⁻¹ := by
    have hτsq : τ ^ (2 : ℕ) = y ^ (2 / 3 : ℝ) := cubicRoot_sq hy₀.le
    have hτcb : τ ^ (3 : ℕ) = y := by
      dsimp [τ]
      rw [← Real.rpow_mul_natCast hy₀.le, show (1 / 3 : ℝ) * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
    have hs : (18 : ℝ) < τ ^ (2 : ℕ) := by
      rw [hτsq]
      exact (by norm_num : (18 : ℝ) < 18.5663553344511).trans_le
        (outerEightyPow_lo.le.trans (Real.rpow_le_rpow (by norm_num) hy (by norm_num)))
    rw [show a * H⁻¹ = π ^ 2 / 10 * τ ^ 2 by
      dsimp [a, H]
      rw [← hτcb]
      field_simp [hτ.ne']
      ring]
    calc
      (1 : ℝ) ≤ 3 ^ 2 / 10 * (18 : ℝ) := by norm_num
      _ ≤ _ := by gcongr; exact Real.pi_gt_three.le
  have hm := power_mul_exp_antitoneOn (b := 0.010) 1 1 (by decide) (by decide)
    (inv_pos.mpr hH).le ha.le (by simpa using hlarge)
  have hInv : H⁻¹ ≤ h⁻¹ := (inv_le_inv₀ hH hh).mpr hhCap
  have hb := hm (show H⁻¹ ∈ Ici H⁻¹ from le_rfl) hInv hInv
  simp only [pow_one] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 20 * π * y ^ 3 by positivity)
  have hcapEq : y ^ 3 / τ = y ^ (8 / 3 : ℝ) := by
    change y ^ (3 : ℕ) / y ^ (1 / 3 : ℝ) = _
    rw [← Real.rpow_ofNat y 3, ← Real.rpow_sub hy₀]
    congr 1
    norm_num
  have haEq : a / H = π ^ 2 * y ^ (2 / 3 : ℝ) / 10 := by
    have hq : y / τ = y ^ (2 / 3 : ℝ) := by
      change y / y ^ (1 / 3 : ℝ) = _
      nth_rw 1 [← Real.rpow_one y]
      rw [← Real.rpow_sub hy₀]
      congr 1
      norm_num
    calc
      _ = π ^ 2 * (y / τ) / 10 := by dsimp [a, H]; field_simp [hτ.ne']; ring
      _ = _ := by rw [hq]
  calc
    _ = (20 * π * y ^ 3) * (h⁻¹ * exp (-a * h⁻¹ + 0.010)) := by
      rw [show -(2 * π ^ 2 * y / (5 * h)) = -a * h⁻¹ by dsimp [a]; ring]
      ring
    _ ≤ (20 * π * y ^ 3) * (H⁻¹ * exp (-a * H⁻¹ + 0.010)) := hb'
    _ = 5 * π * y ^ (8 / 3 : ℝ) * exp (-π ^ 2 * y ^ (2 / 3 : ℝ) / 10 + 0.010) := by
      rw [show -a * H⁻¹ = -π ^ 2 * y ^ (2 / 3 : ℝ) / 10 by
        rw [neg_mul, ← div_eq_mul_inv, haEq]; ring, ← mul_assoc, ← div_eq_mul_inv]
      have hW : 20 * π * y ^ 3 / H = 5 * π * (y ^ 3 / τ) := by
        dsimp [H]; field_simp [hτ.ne']; ring
      rw [hW, hcapEq]
    _ < _ := kernelSwap_cap_majorant_lt hy

/-- Extending the positive-index sum to all integers costs less than the indicated tiny tolerance. -/
theorem negativeExtension_majorant_lt {y : ℝ} (hy : 80 ≤ y) :
    (160 * π * y ^ 9 / (2 * log y)) *
      exp (y * (4 * π / sqrt 3 - 2 * log y)) < 1e-30 := by
  have hy₀ : 0 < y := by linarith
  have hlog := outerEightyLog_gt.trans_le (Real.log_le_log (by norm_num) hy)
  have hs : (1.732 : ℝ) < sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hup : 4 * π / sqrt 3 ≤ 7.26 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [Real.pi_lt_d4, hs]
  have hExp : y * (4 * π / sqrt 3 - 2 * log y) ≤ -1.5 * y := by
    have hcoef : 4 * π / sqrt 3 - 2 * log y ≤ -1.5 := by linarith
    linear_combination mul_le_mul_of_nonneg_left hcoef hy₀.le
  have hform : (160 * π * y ^ 9 / (2 * log y)) * exp (y * (4 * π / sqrt 3 - 2 * log y)) ≤
      (160 * π / 8.76) * (y ^ 9 * exp (-1.5 * y)) := by
    rw [show (160 * π * y ^ 9 / (2 * log y)) = (160 * π / (2 * log y)) * y ^ 9 by ring,
      mul_assoc]
    have hDen : (8.76 : ℝ) ≤ 2 * log y := by linarith
    gcongr
  have hm := power_mul_exp_antitoneOn (x₀ := 80) (a := 1.5) (b := 0)
    9 1 (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
  have hb := hm (show (80 : ℝ) ∈ Ici 80 from le_rfl) hy hy
  simp only [pow_one, add_zero] at hb
  refine hform.trans_lt ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_lt ?_)
  have he₁ : exp (-30 : ℝ) < 1e-13 := by
    dyadic_interval +kernel [prec := 63]
  have he : exp (-1.5 * 80 : ℝ) ≤ 1e-52 := by
    rw [show (-1.5 * 80 : ℝ) = (4 : ℕ) * (-30) by norm_num, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_nonneg _) he₁.le 4).trans_eq (by norm_num)
  calc
    _ ≤ (160 * 3.1416 / 8.76) * ((80 : ℝ) ^ 9 * 1e-52) := by
      gcongr
      exact Real.pi_lt_d4.le
    _ < _ := by norm_num

end DurfeeCCS.Step10
