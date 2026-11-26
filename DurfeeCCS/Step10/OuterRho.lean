module

public import DurfeeCCS.Step06.Branches
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Principal square roots and phase coordinates for the outer Bessel kernel. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Complex Real Set DurfeeCCS.Step06

/-- The outer kernel's principal square root with real parameter a (the squared Bessel scale). -/
def outerRhoAt (h t a : ℝ) : ℂ := (((h : ℂ) + I * (t : ℂ)) ^ 2 + (a : ℂ)).sqrt

/-- The principal square root in Proposition 4.1, with Bessel scale 4π²/3. -/
def outerRho (h t : ℝ) : ℂ := outerRhoAt h t (4 * π ^ 2 / 3)

theorem outerRhoAt_sq (h t a : ℝ) :
    outerRhoAt h t a ^ 2 = ((h : ℂ) + I * (t : ℂ)) ^ 2 + (a : ℂ) :=
  principalSqrt_sq _

theorem outerRhoAt_re_sq_sub_im_sq (h t a : ℝ) :
    (outerRhoAt h t a).re ^ 2 - (outerRhoAt h t a).im ^ 2 = h ^ 2 + a - t ^ 2 := by
  have hx := congrArg Complex.re (outerRhoAt_sq h t a)
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hx
  simp only [pow_two]
  linear_combination hx

theorem outerRhoAt_re_mul_im (h t a : ℝ) :
    (outerRhoAt h t a).re * (outerRhoAt h t a).im = h * t := by
  have hx := congrArg Complex.im (outerRhoAt_sq h t a)
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hx
  linear_combination hx / 2

private theorem outerRhoAt_re_pos {h t a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    0 < (outerRhoAt h t a).re := by
  have hp : 0 ≤ (outerRhoAt h t a).re := by
    unfold outerRhoAt
    rw [Complex.sqrt_eq_real_add_ite]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, Complex.ofReal_im]
    split_ifs <;> simp <;> positivity
  refine lt_of_le_of_ne hp (Ne.symm ?_)
  intro hz
  have him := outerRhoAt_re_mul_im h t a
  rw [hz, zero_mul, eq_comm] at him
  have ht := (mul_eq_zero.mp him).resolve_left hh.ne'
  have hreal := outerRhoAt_re_sq_sub_im_sq h t a
  rw [hz] at hreal
  simp only [ht] at hreal
  nlinarith [sq_nonneg (outerRhoAt h t a).im, sq_nonneg h]

theorem outerRhoAt_im_eq {h t a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    (outerRhoAt h t a).im = h * t / (outerRhoAt h t a).re := by
  apply (eq_div_iff (outerRhoAt_re_pos hh ha).ne').mpr
  rw [mul_comm]
  exact outerRhoAt_re_mul_im h t a

private theorem outerRhoAt_square_gap {h t a : ℝ} :
    ((outerRhoAt h t a).re ^ 2 - h ^ 2) * ((outerRhoAt h t a).re ^ 2 + t ^ 2) =
      a * (outerRhoAt h t a).re ^ 2 := by
  let x := (outerRhoAt h t a).re
  let b := (outerRhoAt h t a).im
  have h₁ : x ^ 2 - b ^ 2 = h ^ 2 + a - t ^ 2 := outerRhoAt_re_sq_sub_im_sq h t a
  have h₂ : x * b = h * t := outerRhoAt_re_mul_im h t a
  have h₃ := congrArg (fun w : ℝ => w ^ 2) h₂
  change (x * b) ^ 2 = (h * t) ^ 2 at h₃
  change (x ^ 2 - h ^ 2) * (x ^ 2 + t ^ 2) = a * x ^ 2
  linear_combination x ^ 2 * h₁ + h₃

theorem outerRhoAt_re_gt {h t a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    h < (outerRhoAt h t a).re := by
  have hp : 0 < (outerRhoAt h t a).re := outerRhoAt_re_pos hh ha
  have hp₁ : 0 < (outerRhoAt h t a).re ^ 2 + t ^ 2 := by positivity
  have hg := outerRhoAt_square_gap (h := h) (t := t) (a := a)
  have hp₂ : 0 < a * (outerRhoAt h t a).re ^ 2 := by positivity
  have hs : 0 < (outerRhoAt h t a).re ^ 2 - h ^ 2 :=
    (mul_pos_iff_of_pos_right hp₁).mp (hg ▸ hp₂)
  nlinarith [mul_pos hh hp]

/-- The exact difference identity underlying the real-part bounds in (72). -/
theorem outerRhoAt_re_gap_eq {h t a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    Real.sqrt (h ^ 2 + a) - (outerRhoAt h t a).re =
      a * t ^ 2 /
        (((outerRhoAt h t a).re ^ 2 + t ^ 2) *
          (Real.sqrt (h ^ 2 + a) + (outerRhoAt h t a).re)) := by
  let x := (outerRhoAt h t a).re
  let p := Real.sqrt (h ^ 2 + a)
  have hp : 0 < p := by dsimp [p]; positivity
  have hx : 0 < x := outerRhoAt_re_pos hh ha
  have hp₂ : p ^ 2 = h ^ 2 + a := Real.sq_sqrt (by positivity)
  have hg : (x ^ 2 - h ^ 2) * (x ^ 2 + t ^ 2) = a * x ^ 2 :=
    outerRhoAt_square_gap
  change p - x = a * t ^ 2 / ((x ^ 2 + t ^ 2) * (p + x))
  apply (eq_div_iff (by positivity : ((x ^ 2 + t ^ 2) * (p + x)) ≠ 0)).mpr
  linear_combination (x ^ 2 + t ^ 2) * hp₂ - hg

theorem outerRhoAt_re_gap_pos {h t a : ℝ} (hh : 0 < h) (ha : 0 < a) (ht : t ≠ 0) :
    0 < Real.sqrt (h ^ 2 + a) - (outerRhoAt h t a).re := by
  rw [outerRhoAt_re_gap_eq hh ha]
  have hx := outerRhoAt_re_pos (t := t) hh ha
  positivity

theorem outerRhoAt_re_gap_le {h t a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    Real.sqrt (h ^ 2 + a) - (outerRhoAt h t a).re ≤
      a * t ^ 2 / (2 * h * (h ^ 2 + a)) := by
  rw [outerRhoAt_re_gap_eq hh ha]
  have hx := outerRhoAt_re_gt (t := t) hh ha
  have h₁ : h ^ 2 + a ≤ (outerRhoAt h t a).re ^ 2 + t ^ 2 := by
    linarith [outerRhoAt_re_sq_sub_im_sq h t a, sq_nonneg (outerRhoAt h t a).im]
  have h₂ : h ≤ Real.sqrt (h ^ 2 + a) := Real.le_sqrt_of_sq_le (by linarith)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  rw [mul_comm (2 * h)]
  gcongr
  linarith

theorem outerRho_re_gt {h t : ℝ} (hh : 0 < h) : h < (outerRho h t).re := by
  exact outerRhoAt_re_gt hh (by positivity)

theorem outerRho_im_eq {h t : ℝ} (hh : 0 < h) :
    (outerRho h t).im = h * t / (outerRho h t).re := by
  exact outerRhoAt_im_eq hh (by positivity)

theorem outerRho_im_pi_pos {h : ℝ} (hh : 0 < h) : 0 < (outerRho h π).im := by
  rw [outerRho_im_eq hh]
  exact div_pos (by positivity) (hh.trans (outerRho_re_gt hh))

theorem outerRho_im_pi_lt {h : ℝ} (hh : 0 < h) : (outerRho h π).im < π := by
  rw [outerRho_im_eq hh, div_lt_iff₀ (hh.trans (outerRho_re_gt hh))]
  simpa only [mul_comm π] using mul_lt_mul_of_pos_right (outerRho_re_gt (t := π) hh) pi_pos

theorem continuousOn_outerRho_pi : ContinuousOn (fun h => outerRho h π) (Ioi (0 : ℝ)) := by
  unfold outerRho outerRhoAt
  apply Complex.continuousOn_sqrt.comp (Continuous.continuousOn ?_)
  · intro h hh
    apply Complex.mem_slitPlane_iff.mpr
    right
    have hh' : 0 < h := hh
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      one_mul, sub_zero, zero_add, add_zero]
    exact (add_pos (mul_pos hh' pi_pos) (mul_pos pi_pos hh')).ne'
  · fun_prop

theorem outerRho_arg_pi_pos {h : ℝ} (hh : 0 < h) : 0 < (outerRho h π).arg := by
  have hi := outerRho_im_pi_pos hh
  refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hi.le) (Ne.symm ?_)
  exact fun hz => hi.ne' (Complex.arg_eq_zero_iff.mp hz).2

theorem outerRho_arg_pi_lt {h : ℝ} (hh : 0 < h) : (outerRho h π).arg < π / h := by
  let w := outerRho h π
  have hx : 0 < w.re := hh.trans (outerRho_re_gt hh)
  have hi : 0 < w.im := outerRho_im_pi_pos hh
  have ha : w.arg = Real.arctan (w.im / w.re) := by
    rw [← Complex.tan_arg]
    have ht := (abs_lt.mp ((Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hx)))
    exact (Real.arctan_tan (by linarith only [ht.1]) ht.2).symm
  calc
    w.arg = Real.arctan (w.im / w.re) := ha
    _ < w.im / w.re := Real.arctan_lt_self (div_pos hi hx)
    _ ≤ π / h := div_le_div₀ pi_pos.le (outerRho_im_pi_lt hh).le hh
      (outerRho_re_gt hh).le

/-- The phase lies above the continuous maximizer, with the quantitative excess on page 51. -/
theorem outerRho_phase_gap {y h : ℝ} (hy : 0 ≤ y) (hh : 0 < h) :
    0 < (y * (outerRho h π).im + (outerRho h π).arg) / π -
      y * h / Real.sqrt (h ^ 2 + 4 * π ^ 2 / 3) ∧
    (y * (outerRho h π).im + (outerRho h π).arg) / π -
      y * h / Real.sqrt (h ^ 2 + 4 * π ^ 2 / 3) ≤
      2 * π ^ 4 * y / (3 * h * (Real.sqrt (h ^ 2 + 4 * π ^ 2 / 3)) ^ 3) + 1 / h := by
  let a := 4 * π ^ 2 / 3
  let p := Real.sqrt (h ^ 2 + a)
  let x := (outerRho h π).re
  let theta := (outerRho h π).arg
  have ha : 0 < a := by dsimp [a]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hx : 0 < x := hh.trans (outerRho_re_gt hh)
  have hgap0 : 0 < p - x := outerRhoAt_re_gap_pos hh ha pi_pos.ne'
  have hg : p - x ≤ a * π ^ 2 / (2 * h * (h ^ 2 + a)) :=
    outerRhoAt_re_gap_le hh ha
  have hp2 : p ^ 2 = h ^ 2 + a := Real.sq_sqrt (by positivity)
  have hE : (y * (outerRho h π).im + theta) / π - y * h / p =
      (y * h / x) * ((p - x) / p) + theta / π := by
    rw [outerRho_im_eq hh]
    change (y * (h * π / x) + theta) / π - y * h / p = _
    field_simp [pi_pos.ne', hp.ne', hx.ne']
    ring
  change 0 < (y * (outerRho h π).im + theta) / π - y * h / p ∧
    (y * (outerRho h π).im + theta) / π - y * h / p ≤
      2 * π ^ 4 * y / (3 * h * p ^ 3) + 1 / h
  rw [hE]
  have harg := outerRho_arg_pi_pos hh
  change 0 < theta at harg
  constructor
  · positivity
  have hhy : y * h / x ≤ y := by
    rw [div_le_iff₀ hx]
    exact mul_le_mul_of_nonneg_left (outerRho_re_gt (t := π) hh).le hy
  calc
    _ ≤ y * (a * π ^ 2 / (2 * h * (h ^ 2 + a)) / p) + (π / h) / π :=
      add_le_add (mul_le_mul hhy (div_le_div_of_nonneg_right hg hp.le) (by positivity) hy)
        (div_le_div_of_nonneg_right (outerRho_arg_pi_lt hh).le pi_pos.le)
    _ = _ := by
      rw [← hp2]
      dsimp only [a]
      field_simp [hh.ne', hp.ne', pi_pos.ne']
      ring

end DurfeeCCS.Step10
