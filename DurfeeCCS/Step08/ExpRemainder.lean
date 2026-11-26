module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exponential comparisons and the first two remainder bounds in (20). -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set

private theorem affine_re_le_max {A B : ℂ} {t : ℝ} (ht : t ∈ Icc 0 1) :
    (B + (A - B) * (t : ℂ)).re ≤ max A.re B.re := by
  have h₀ := mul_le_mul_of_nonneg_right (le_max_left A.re B.re) ht.1
  have h₁ := mul_le_mul_of_nonneg_right (le_max_right A.re B.re) (sub_nonneg.mpr ht.2)
  simp only [add_re, mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  linarith only [h₀, h₁]

/-- The straight complex segment gives an exponential Lipschitz estimate. -/
theorem norm_exp_sub_exp_le (A B : ℂ) :
    ‖exp A - exp B‖ ≤ ‖A - B‖ * Real.exp (max A.re B.re) := by
  let F (t : ℝ) : ℂ := exp (B + (A - B) * (t : ℂ))
  let f (t : ℝ) : ℂ := (A - B) * F t
  have hDer (t : ℝ) : HasDerivAt F (f t) t := by
    have h := (Complex.hasDerivAt_exp (B + (A - B) * (t : ℂ))).comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).const_mul (A - B)).const_add B)
    simpa only [F, f, Function.comp_apply, id_eq, mul_one, mul_comm] using h.comp_ofReal
  have hcont : Continuous f := by unfold f F; fun_prop
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hDer t) (hcont.intervalIntegrable 0 1)
  have hends : F 1 - F 0 = exp A - exp B := by
    simp only [F, ofReal_one, ofReal_zero, mul_one, mul_zero, add_zero, add_sub_cancel]
  rw [hends] at heq
  have hbound (t : ℝ) (ht : t ∈ uIoc (0 : ℝ) 1) :
      ‖f t‖ ≤ ‖A - B‖ * Real.exp (max A.re B.re) := by
    rw [uIoc_of_le zero_le_one] at ht
    dsimp only [f, F]
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (affine_re_le_max ⟨ht.1.le, ht.2⟩))
      (norm_nonneg _)
  rw [← heq]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

theorem norm_exp_sub_one_le (z : ℂ) :
    ‖exp z - 1‖ ≤ ‖z‖ * Real.exp (max 0 z.re) := by
  simpa [max_comm] using norm_exp_sub_exp_le z 0

theorem norm_exp_sub_exp_le_exp_norm (A B : ℂ) :
    ‖exp A - exp B‖ ≤ Real.exp B.re * (Real.exp ‖A - B‖ - 1) := by
  have h : ‖exp (A - B) - 1‖ ≤ Real.exp ‖A - B‖ - 1 := by
    simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (A - B) 1
  have heq : exp A - exp B = exp B * (exp (A - B) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one, add_comm B, sub_add_cancel]
  rw [heq, norm_mul, Complex.norm_exp]
  exact mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)

private theorem integral_taylor_weight :
    (∫ t in (0 : ℝ)..1, (1 - t)) = 1 / 2 := by
  have h (t : ℝ) : HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - t) t := by
    convert (hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const 2) using 1
    · rfl
    · norm_num
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => h t) ((show Continuous (fun t : ℝ => 1 - t) by fun_prop).intervalIntegrable 0 1)]
  norm_num

/-- The integral second remainder keeps the real-part exponential weight. -/
theorem norm_exp_sub_one_sub_le (z : ℂ) :
    ‖exp z - 1 - z‖ ≤ (‖z‖ ^ 2 / 2) * Real.exp (max 0 z.re) := by
  let F (t : ℝ) : ℂ := (z * (1 - (t : ℂ)) + 1) * exp (z * (t : ℂ))
  let f (t : ℝ) : ℂ := z ^ 2 * (1 - (t : ℂ)) * exp (z * (t : ℂ))
  have hDer (t : ℝ) : HasDerivAt F (f t) t := by
    have h₁ := (((hasDerivAt_id (t : ℂ)).const_sub 1).const_mul z).add_const 1
    have h₂ := (Complex.hasDerivAt_exp (z * (t : ℂ))).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).const_mul z)
    convert (h₁.mul h₂).comp_ofReal using 1
    · rfl
    · dsimp only [f, Function.comp_apply, id_eq]
      ring
  have hcont : Continuous f := by unfold f; fun_prop
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hDer t) (hcont.intervalIntegrable 0 1)
  have hends : F 1 - F 0 = exp z - 1 - z := by
    simp only [F, ofReal_zero, ofReal_one, sub_self, mul_zero, zero_add, one_mul,
      mul_one, sub_zero, Complex.exp_zero]
    ring
  rw [hends] at heq
  let C := ‖z‖ ^ 2 * Real.exp (max 0 z.re)
  have hbound (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : ‖f t‖ ≤ C * (1 - t) := by
    have ht₁ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hr := affine_re_le_max (A := z) (B := 0) ⟨ht.1.le, ht.2⟩
    simp only [zero_add, sub_zero, zero_re, max_comm z.re] at hr
    have tn : ‖(1 : ℂ) - (t : ℂ)‖ = 1 - t := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_of_nonneg ht₁]
    dsimp only [f, C]
    rw [norm_mul, norm_mul, norm_pow, tn, Complex.norm_exp]
    calc
      _ ≤ (‖z‖ ^ 2 * (1 - t)) * Real.exp (max 0 z.re) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr) (by positivity)
      _ = _ := by ring
  have hC : Continuous (fun t : ℝ => C * (1 - t)) := by fun_prop
  rw [← heq]
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (ae_of_all _ hbound) (hC.intervalIntegrable 0 1)).trans_eq ?_
  rw [intervalIntegral.integral_const_mul, integral_taylor_weight]
  dsimp [C]
  ring

end DurfeeCCS.Step08
