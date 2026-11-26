module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The ten strict numerical bounds for the explicit majorants on manuscript page 43. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open Real

/-- The coefficient used in the geometric majorant for small non-leading modes. -/
def outerSmallModeBound (c : ℝ) : ℝ :=
  1.47 * exp (-13 * c * π ^ 4 / 400) / (1 - exp (-13 * c * π ^ 4 / 200))

/-- High-frequency bound after setting the auxiliary parameter to 11. -/
def outerHighLowBound (c y₀ : ℝ) : ℝ :=
  29 * c ^ 3 * y₀ ^ 3 / 121 * exp (-76 * π ^ 2 * c * y₀ / 4125)

/-- High-frequency bound after setting the auxiliary parameter to `4 y₀^(1/3)`. -/
def outerHighLargeBound (c y₀ : ℝ) : ℝ :=
  let z := y₀ ^ (2 / 3 : ℝ)
  29 * c ^ 3 * y₀ * z ^ 2 / 16 * exp (-c * π ^ 2 * z / 12 + 7 * c * π ^ 2 / 40)

/-- Lower endpoint error bound after setting the auxiliary parameter to `4 y₀^(1/3)`. -/
def outerLowerBound (c y₀ : ℝ) : ℝ :=
  let z := y₀ ^ (2 / 3 : ℝ)
  7 * c ^ 2 * y₀ * z / 2 * exp (-17 * c * π ^ 2 * z / 120)

/-- Upper endpoint error bound on the full reduced range. -/
def outerUpperBound (c : ℝ) : ℝ :=
  (1.142 + outerSmallModeBound c) * (1 / (80 * c * 8.76) + 2 * exp (-160 * c * 8.76))

theorem outerPi_gt : (3.14159265358979 : ℝ) < π := by
  exact (by norm_num : (3.14159265358979 : ℝ) < 3.14159265358979323846).trans pi_gt_d20

theorem outerPi_lt : π < (3.14159265358980 : ℝ) := by
  exact pi_lt_d20.trans (by norm_num)

theorem outerEightyLog_gt : (4.38 : ℝ) < log 80 := by
  apply (lt_log_iff_exp_lt (by norm_num)).2
  dyadic_interval +kernel [prec := 30]

theorem outerEightyPow_lo : (18.5663553344511 : ℝ) < (80 : ℝ) ^ (2 / 3 : ℝ) := by
  have hc : ((80 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = 80 ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast (by norm_num), show (2 / 3 : ℝ) * (3 : ℕ) = (2 : ℕ) by norm_num,
      Real.rpow_natCast]
  by_contra! hl
  have hh := pow_le_pow_left₀ (by positivity) hl 3
  rw [hc] at hh
  norm_num at hh

theorem outerEightyPow_hi : (80 : ℝ) ^ (2 / 3 : ℝ) < (18.5663553344512 : ℝ) := by
  have hc : ((80 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = 80 ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast (by norm_num), show (2 / 3 : ℝ) * (3 : ℕ) = (2 : ℕ) by norm_num,
      Real.rpow_natCast]
  by_contra! hl
  have hh := pow_le_pow_left₀ (by norm_num) hl 3
  rw [hc] at hh
  norm_num at hh

private theorem real_div_nat (x : ℝ) (n : ℕ) :
    x / (n : ℝ) = x * (((1 : ℚ) / n : ℚ) : ℝ) := by
  simp [div_eq_mul_inv]

private theorem outerSmallModeDenom_pos {c : ℝ} (hc : 0 < c) :
    0 < 1 - exp (-13 * c * π ^ 4 / 200) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  convert neg_lt_zero.mpr (show 0 < 13 * c * π ^ 4 / 200 by positivity) using 1
  ring

theorem outerSmallModeBound_left : outerSmallModeBound (9 / 10) < 0.085385 := by
  unfold outerSmallModeBound
  rw [show (9 / 10 : ℝ) = 0.9 by norm_num]
  apply (div_lt_iff₀ (outerSmallModeDenom_pos (by norm_num))).2
  erw [real_div_nat _ 400, real_div_nat _ 200]
  have hlo := outerPi_gt
  have hhi := outerPi_lt
  dyadic_interval +kernel [prec := 42]

theorem outerSmallModeBound_right : outerSmallModeBound 1 < 0.062117 := by
  unfold outerSmallModeBound
  apply (div_lt_iff₀ (outerSmallModeDenom_pos (by norm_num))).2
  erw [real_div_nat _ 400, real_div_nat _ 200]
  have hlo := outerPi_gt
  have hhi := outerPi_lt
  dyadic_interval +kernel [prec := 42]

theorem outerHighLowBound_left : outerHighLowBound (9 / 10) 80 < 0.184340 := by
  unfold outerHighLowBound
  rw [show (9 / 10 : ℝ) = 0.9 by norm_num]
  erw [real_div_nat _ 121, real_div_nat _ 4125]
  have hlo := outerPi_gt
  have hhi := outerPi_lt
  dyadic_interval +kernel [prec := 46]

theorem outerHighLowBound_right : outerHighLowBound 1 80 < 0.059036 := by
  unfold outerHighLowBound
  erw [real_div_nat _ 121, real_div_nat _ 4125]
  have hlo := outerPi_gt
  have hhi := outerPi_lt
  dyadic_interval +kernel [prec := 46]

theorem outerHighLargeBound_left : outerHighLargeBound (9 / 10) 80 < 0.185375 := by
  dsimp [outerHighLargeBound]
  rw [show (9 / 10 : ℝ) = 0.9 by norm_num]
  erw [real_div_nat _ 16, real_div_nat _ 12,
    real_div_nat _ 40]
  generalize hz : (80 : ℝ) ^ (2 / 3 : ℝ) = z
  have hlo := outerPi_gt
  have hhi := outerPi_lt
  have hzlo : 18.5663553344511 < z := hz ▸ outerEightyPow_lo
  have hzhi : z < 18.5663553344512 := hz ▸ outerEightyPow_hi
  dyadic_interval +kernel [prec := 46]

theorem outerHighLargeBound_right : outerHighLargeBound 1 80 < 0.065639 := by
  dsimp [outerHighLargeBound]
  erw [real_div_nat _ 16, real_div_nat _ 12, real_div_nat _ 40]
  generalize hz : (80 : ℝ) ^ (2 / 3 : ℝ) = z
  have hlo := outerPi_gt
  have hhi := outerPi_lt
  have hzlo : 18.5663553344511 < z := hz ▸ outerEightyPow_lo
  have hzhi : z < 18.5663553344512 := hz ▸ outerEightyPow_hi
  dyadic_interval +kernel [prec := 46]

theorem outerLowerBound_left_sharp : outerLowerBound (9 / 10) 80 < 3.005e-7 := by
  dsimp [outerLowerBound]
  rw [show (9 / 10 : ℝ) = 0.9 by norm_num]
  erw [real_div_nat _ 2, real_div_nat _ 120]
  generalize hz : (80 : ℝ) ^ (2 / 3 : ℝ) = z
  have hlo := outerPi_gt
  have hhi := outerPi_lt
  have hzlo : 18.5663553344511 < z := hz ▸ outerEightyPow_lo
  have hzhi : z < 18.5663553344512 := hz ▸ outerEightyPow_hi
  dyadic_interval +kernel [prec := 51]

theorem outerLowerBound_right_sharp : outerLowerBound 1 80 < 2.767e-8 := by
  dsimp [outerLowerBound]
  erw [real_div_nat _ 2, real_div_nat _ 120]
  generalize hz : (80 : ℝ) ^ (2 / 3 : ℝ) = z
  have hlo := outerPi_gt
  have hhi := outerPi_lt
  have hzlo : 18.5663553344511 < z := hz ▸ outerEightyPow_lo
  have hzhi : z < 18.5663553344512 := hz ▸ outerEightyPow_hi
  dyadic_interval +kernel [prec := 51]

theorem outerLowerBound_left : outerLowerBound (9 / 10) 80 < 4e-7 :=
  outerLowerBound_left_sharp.trans (by norm_num)

theorem outerLowerBound_right : outerLowerBound 1 80 < 4e-7 :=
  outerLowerBound_right_sharp.trans (by norm_num)

private theorem outerUpperBound_le_cutoff {c : ℝ} (hc : 9 / 10 ≤ c) :
    outerUpperBound c ≤
      (1.142 + outerSmallModeBound c) * (1 / (80 * c * 8.76) + 2 * exp (-30)) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hexp : exp (-160 * c * 8.76) ≤ exp (-30) := Real.exp_le_exp.mpr (by linarith)
  have hden := outerSmallModeDenom_pos hc0
  have hm : 0 ≤ outerSmallModeBound c := by
    unfold outerSmallModeBound
    positivity
  unfold outerUpperBound
  gcongr

theorem outerUpperBound_left : outerUpperBound (9 / 10) < 0.001947 := by
  apply lt_of_le_of_lt (outerUpperBound_le_cutoff (c := 9 / 10) (by norm_num))
  have hnum : outerSmallModeBound (9 / 10) < 0.085385 := outerSmallModeBound_left
  have hm : exp (-30 : ℝ) < 0.00000000000010 := by
    dyadic_interval +kernel [prec := 65]
  have hh : 0 < 1 / (80 * (9 / 10 : ℝ) * 8.76) + 2 * exp (-30) := by positivity
  calc
    _ ≤ (1.142 + 0.085385) * (1 / (80 * (9 / 10 : ℝ) * 8.76) + 2 * 0.00000000000010) := by gcongr
    _ < _ := by norm_num

theorem outerUpperBound_right : outerUpperBound 1 < 0.001719 := by
  apply lt_of_le_of_lt (outerUpperBound_le_cutoff (c := 1) (by norm_num))
  have hnum : outerSmallModeBound 1 < 0.062117 := outerSmallModeBound_right
  have hm : exp (-30 : ℝ) < 0.00000000000010 := by
    dyadic_interval +kernel [prec := 65]
  have hh : 0 < 1 / (80 * (1 : ℝ) * 8.76) + 2 * exp (-30) := by positivity
  calc
    _ ≤ (1.142 + 0.062117) * (1 / (80 * (1 : ℝ) * 8.76) + 2 * 0.00000000000010) := by gcongr
    _ < _ := by norm_num

theorem outerTableLeftTotal :
    (1.142 + 0.085385 + max 0.184340 0.185375 + 4e-7 + 0.001947 : ℝ) < 1.42 := by
  rw [max_eq_right (by norm_num)]
  norm_num

theorem outerTableRightTotal :
    (0.062117 + max 0.059036 0.065639 + 4e-7 + 0.001719 : ℝ) < 0.130 := by
  rw [max_eq_right (by norm_num)]
  norm_num

end DurfeeCCS.Step07
