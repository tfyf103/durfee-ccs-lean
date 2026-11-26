module

public import DurfeeCCS.Step10.OuterFarParameters
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Numerical estimates for the three tails in Lemma 4.3. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Set

theorem farCube_lower {y : ℝ} (hy : 80 ≤ y) : (4.308869 : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
  have hy0 : 0 ≤ y := by linarith
  by_contra! h
  have hle := pow_lt_pow_left₀ h (rpow_nonneg hy0 (1 / 3 : ℝ)) (by decide : 3 ≠ 0)
  rw [farCube_eq hy0] at hle
  norm_num at hle
  linarith

theorem farSqrtThree_bounds : (1.73205080 : ℝ) < sqrt 3 ∧ sqrt 3 < 1.73205081 :=
  ⟨(lt_sqrt (by norm_num)).mpr (by norm_num),
    (sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)⟩

private theorem rpow_quarter_bound {x b p : ℝ} (hb : 0 ≤ b)
    (h : (x ^ p) ^ (4 : ℕ) < b ^ (4 : ℕ)) : x ^ p < b := by
  by_contra! h'
  have hh := pow_le_pow_left₀ hb h' 4
  linarith

theorem farThreeRpow54_lt : (3 : ℝ) ^ (5 / 4 : ℝ) < 3.94822204 := by
  apply rpow_quarter_bound (by norm_num)
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3),
    show (5 / 4 : ℝ) * (4 : ℕ) = (5 : ℕ) by norm_num, rpow_natCast]
  norm_num

theorem farThreeRpow34_lt : (3 : ℝ) ^ (3 / 4 : ℝ) < 2.279508 := by
  apply rpow_quarter_bound (by norm_num)
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3),
    show (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) by norm_num, rpow_natCast]
  norm_num

theorem farTwoRpow52_lt : (2 : ℝ) ^ (5 / 2 : ℝ) < 5.657 := by
  apply rpow_quarter_bound (by norm_num)
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    show (5 / 2 : ℝ) * (4 : ℕ) = (10 : ℕ) by norm_num, rpow_natCast]
  norm_num

private theorem far1252Rpow52_lt : (12.52 : ℝ) ^ (5 / 2 : ℝ) < 555 := by
  apply rpow_quarter_bound (by norm_num)
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 12.52),
    show (5 / 2 : ℝ) * (4 : ℕ) = (10 : ℕ) by norm_num, rpow_natCast]
  norm_num

private theorem farHigh_antitone :
    AntitoneOn (fun w : ℝ => (1 + 3 / 4 * w ^ 2) * exp (-2 * w)) (Ici 4.308869) := by
  let g := fun w : ℝ => (1 + 3 / 4 * w ^ 2) * exp (-2 * w)
  have hg (w : ℝ) : HasDerivAt g (exp (-2 * w) * (-2 + 3 / 2 * w - 3 / 2 * w ^ 2)) w := by
    have h1 := (((hasDerivAt_pow 2 w).const_mul (3 / 4 : ℝ)).const_add (1 : ℝ))
    have h2 := ((hasDerivAt_id w).const_mul (-2 : ℝ)).exp
    convert h1.mul h2 using 1
    · rfl
    · norm_num
      ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun w _ => (hg w).continuousAt.continuousWithinAt
  · exact fun w _ => (hg w).differentiableAt.differentiableWithinAt
  · intro w hw
    rw [(hg w).deriv]
    have hw' : 4.308869 ≤ w := interior_subset hw
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (by nlinarith [mul_nonneg (show 0 ≤ w by linarith) (show 0 ≤ w - 1 by linarith)])

theorem farCentralHigh_constant {w : ℝ} (hw : 4.308869 ≤ w) :
    (2.2 / 0.9) * (3 : ℝ) ^ (5 / 4 : ℝ) * ((1 + 3 / 4 * w ^ 2) * exp (-2 * w)) <
      0.026053 := by
  have hend : (2.2 / 0.9 : ℝ) * 3.94822204 *
      ((1 + 3 / 4 * (4.308869 : ℝ) ^ 2) * exp (-2 * 4.308869)) < 0.026053 := by
    have h : exp (-2 * (4.308869 : ℝ)) < 0.000180869 := by
      dyadic_interval +kernel [prec := 48]
    have hconst :
        (2.2 / 0.9 : ℝ) * 3.94822204 * (1 + 3 / 4 * (4.308869 : ℝ) ^ 2) > 0 := by
      norm_num
    nlinarith [mul_lt_mul_of_pos_left h hconst]
  refine lt_of_le_of_lt ?_ hend
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left farThreeRpow54_lt.le (by norm_num)
  · exact farHigh_antitone (le_refl _) hw hw
  · positivity
  · norm_num



private theorem farLow_antitone :
    AntitoneOn (fun f : ℝ => (5 / 2 : ℝ) * log f + 2 * π * (5 - f) / sqrt 3) (Ici 12.52) := by
  let g := fun f : ℝ => (5 / 2 : ℝ) * log f + 2 * π * (5 - f) / sqrt 3
  have hg (f : ℝ) (hf : 12.52 ≤ f) : HasDerivAt g ((5 / 2) / f - 2 * π / sqrt 3) f := by
    have hf0 : 0 < f := by linarith
    have h1 := (hasDerivAt_log hf0.ne').const_mul (5 / 2 : ℝ)
    have h2 := (((hasDerivAt_id f).const_sub (5 : ℝ)).const_mul (2 * π)).div_const (sqrt 3)
    convert h1.add h2 using 1
    · rfl
    · ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun f hf => (hg f hf).continuousAt.continuousWithinAt
  · exact fun f hf => (hg f (interior_subset hf)).differentiableAt.differentiableWithinAt
  · intro f hf
    have hf' : 12.52 ≤ f := interior_subset hf
    rw [(hg f hf').deriv]
    apply sub_nonpos.mpr
    have hs3 := farSqrtThree_bounds.2
    have hπ := Real.pi_gt_three
    calc
      _ ≤ (5 / 2 : ℝ) / 12.52 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hf'
      _ ≤ 2 * 3 / 1.73205081 := by norm_num
      _ ≤ _ := by gcongr

theorem farCentralLow_constant {f : ℝ} (hf : 12.52 ≤ f) :
    (200 * (3 : ℝ) ^ (3 / 4 : ℝ) / 0.9) *
      (f ^ (5 / 2 : ℝ) * exp (2 * π * (5 - f) / sqrt 3)) < 4e-7 := by
  have hmon : f ^ (5 / 2 : ℝ) * exp (2 * π * (5 - f) / sqrt 3) ≤
      (12.52 : ℝ) ^ (5 / 2 : ℝ) * exp (2 * π * (5 - 12.52) / sqrt 3) := by
    rw [Real.rpow_def_of_pos (show 0 < f by linarith),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 12.52), ← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    simpa only [mul_comm (log f), mul_comm (log (12.52 : ℝ))] using
      farLow_antitone (le_refl _) hf hf
  have hπ1 := DurfeeCCS.Step07.outerPi_gt
  have hs3 := farSqrtThree_bounds.2
  have hexp : 2 * π * (5 - 12.52) / sqrt 3 ≤ (-27.2790 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h1 := mul_le_mul_of_nonpos_right hπ1.le (by norm_num : 2 * (5 - (12.52 : ℝ)) ≤ 0)
    have h2 := mul_le_mul_of_nonpos_left hs3.le (by norm_num : (-27.2790 : ℝ) ≤ 0)
    linarith
  calc
    _ ≤ (200 * 2.279508 / 0.9) *
        (555 * exp (-27.2790)) := by
      apply mul_le_mul
      · gcongr; exact farThreeRpow34_lt.le
      · exact hmon.trans (mul_le_mul far1252Rpow52_lt.le (exp_le_exp.mpr hexp)
          (exp_nonneg _) (by norm_num))
      · exact mul_nonneg (rpow_nonneg (by linarith) _) (exp_nonneg _)
      · norm_num
    _ < _ := by
      have h : exp (-27.2790 : ℝ) < 0.000000000001422 := by
        dyadic_interval +kernel [prec := 58]
      linarith

end DurfeeCCS.Step10
