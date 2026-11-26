module

public import DurfeeCCS.Step09.MidPhase
public import DurfeeCCS.Step07.ThetaTailRadius

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Range of the saddle line and its modular image on page 27. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step09

open Complex Real DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

theorem midSaddle_data {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) :
    let a := (saddleS r).re
    let b := (saddleS r).im
    1 < a ∧ a ≤ theta38Growth (Real.sqrt (n : ℝ)) ∧
      0 < midSlope r ∧ midSlope r < 1 ∧
      0 < midU n r ∧ midU n r < 0.072 ∧
      0.68 < b ^ 2 ∧ b < Real.pi / 2 ∧ a ^ 2 ≤ Real.log r ^ 2 + Real.pi ^ 2 / 3 := by
  let x := Real.sqrt (n : ℝ)
  let t := Real.log r
  let a := (saddleS r).re
  let b := (saddleS r).im
  have hx : 80 ≤ x := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hx' : 0 < x := by linarith
  have hr' : 0 < r := by linarith
  have ht : 0 ≤ t := Real.log_nonneg hr
  have htx : t ≤ Real.log x + 1 := by
    have h := Real.log_le_log hr' hmax
    rw [Real.log_mul (Real.exp_ne_zero _) hx'.ne', Real.log_exp, add_comm] at h
    exact h
  have hra : 1.06975 ≤ a :=
    saddle_at_one_lower.1.trans (monotoneOn_saddleS_re (by norm_num) hr' hr)
  have hrb : 0.85623 ≤ b :=
    saddle_at_one_lower.2.trans (monotoneOn_saddleS_im (by simp) hr hr)
  have hAb : a < theta38Growth x := by
    have h := saddleS_exp_re_lt_growth ht
    rw [Real.exp_log hr'] at h
    exact h.trans_le (Real.sqrt_le_sqrt (by linarith only [pow_le_pow_left₀ ht htx 2]))
  have hX : Real.sqrt (x / 80) ≤ x / 80 := by
    have hu : 0 ≤ x / 80 := by positivity
    rw [Real.sqrt_le_iff]
    exact ⟨hu, by nlinarith [mul_nonneg hu (show 0 ≤ x / 80 - 1 by linarith)]⟩
  have hU : midU n r < 0.072 := by
    change a / x < _
    apply (div_lt_iff₀ hx').mpr
    calc
      a < theta38Growth x := hAb
      _ ≤ 5.76 * Real.sqrt (x / 80) := theta38Growth_le hx
      _ ≤ 5.76 * (x / 80) := mul_le_mul_of_nonneg_left hX (by norm_num)
      _ = 0.072 * x := by ring
  have hb := saddleS_exp_im_lt_pi_half ht
  have ha := saddleS_exp_re_sq_le ht
  rw [Real.exp_log hr'] at ha hb
  refine ⟨by linarith, hAb.le, (midSlope_bounds hr').1, (midSlope_bounds hr').2,
    saddleU_pos (by omega) hr', hU, ?_, hb, ha⟩
  have h := pow_le_pow_left₀ (show 0 ≤ (0.85623 : ℝ) by norm_num) hrb 2
  linarith

theorem midU_lt_072 {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) : midU n r < 0.072 :=
  (midSaddle_data hn hr hmax).2.2.2.2.2.1

theorem eight_mul_midU_lt_pi {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) : 8 * midU n r < Real.pi := by
  linarith only [midU_lt_072 hn hr hmax, Real.pi_gt_d2]

theorem midOmega_ge_one {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r) :
    1 ≤ midOmega n r := by
  have hx : (80 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hr' : 0 < r := by linarith
  have hra : 1.06975 ≤ (saddleS r).re :=
    saddle_at_one_lower.1.trans (monotoneOn_saddleS_re (by norm_num) hr' hr)
  exact one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)

theorem norm_midEtaPoint {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 0 < r) (η : ℝ) :
    ‖midEtaPoint n r η‖ = midU n r * Real.sqrt (1 + η ^ 2) := by
  unfold midEtaPoint
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (saddleU_pos hn hr)]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im, pow_two]

theorem re_midEtaTransform_midEtaPoint {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 0 < r)
    (η : ℝ) :
    (midEtaTransform (midEtaPoint n r η)).re =
      4 * Real.pi ^ 2 / (midU n r * (1 + η ^ 2)) := by
  have hu := saddleU_pos hn hr
  have hη : 0 < 1 + η ^ 2 := by positivity
  rw [midEtaTransform, ← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    midEtaPoint_re, Complex.normSq_apply, midEtaPoint_im]
  field_simp [hu.ne', hη.ne']
  ring

theorem norm_midEtaPoint_lt {n : ℕ} {r η : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) (hη : |η| ≤ 8) :
    ‖midEtaPoint n r η‖ < 0.581 := by
  have h := pow_le_pow_left₀ (abs_nonneg η) hη 2
  rw [sq_abs] at h
  have hroot : Real.sqrt (1 + η ^ 2) ≤ 8.063 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by linarith⟩
  rw [norm_midEtaPoint (by omega) (by positivity)]
  exact (mul_le_mul (midU_lt_072 hn hr hmax).le hroot (Real.sqrt_nonneg _) (by norm_num)).trans_lt
    (by norm_num)

theorem re_midEtaTransform_midEtaPoint_gt {n : ℕ} {r η L B : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : |η| ≤ L) (hB : 0 ≤ B)
    (hsize : B * (0.072 * (1 + L ^ 2)) < 4 * Real.pi ^ 2) :
    B < (midEtaTransform (midEtaPoint n r η)).re := by
  have h := pow_le_pow_left₀ (abs_nonneg η) hη 2
  rw [sq_abs] at h
  rw [re_midEtaTransform_midEtaPoint (by omega) (by positivity)]
  have hu := saddleU_pos (by omega : 0 < n) (by positivity : 0 < r)
  apply (lt_div_iff₀ (mul_pos hu (by positivity))).mpr
  exact (mul_le_mul_of_nonneg_left (mul_le_mul (midU_lt_072 hn hr hmax).le
    (by linarith only [h]) (by positivity) (by norm_num)) hB).trans_lt hsize

theorem re_midEtaTransform_midEtaPoint_gt_843 {n : ℕ} {r η : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : |η| ≤ 8) : 8.43 < (midEtaTransform (midEtaPoint n r η)).re := by
  apply re_midEtaTransform_midEtaPoint_gt hn hr hmax hη (by norm_num)
  have hpi := pow_le_pow_left₀ (show 0 ≤ (3.14159 : ℝ) by norm_num)
    (show (3.14159 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_d6]) 2
  linarith

theorem re_midEtaTransform_midEtaPoint_gt_168 {n : ℕ} {r η : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hη : |η| ≤ 3 / 2) : 168 < (midEtaTransform (midEtaPoint n r η)).re := by
  apply re_midEtaTransform_midEtaPoint_gt hn hr hmax hη (by norm_num)
  have hpi := pow_le_pow_left₀ (show 0 ≤ (3.14159 : ℝ) by norm_num)
    (show (3.14159 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_d6]) 2
  linarith

end DurfeeCCS.Step09
