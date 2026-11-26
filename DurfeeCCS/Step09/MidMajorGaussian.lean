module

public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import DurfeeCCS.Step08.SaddleBesselLaplace

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Gaussian moments and truncation used for the inner integral in (58). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open MeasureTheory Set

/-- The sum of the two tails of a real Gaussian. -/
theorem midGaussian_tail_le {A h : ℝ} (hA : 0 < A) (hh : 0 < h) :
    (∫ x in (Icc (-h) h)ᶜ, Real.exp (-A * x ^ 2)) ≤
      Real.exp (-A * h ^ 2) / (A * h) := by
  let f (x : ℝ) := Real.exp (-A * x ^ 2)
  have hf : Integrable f := integrable_exp_neg_mul_sq hA
  let e (x : ℝ) := Real.exp (A * h ^ 2) * Real.exp (-(2 * A * h) * x)
  have hrate : -(2 * A * h) < 0 := neg_lt_zero.mpr (by positivity)
  have hE : IntegrableOn e (Ioi h) :=
    (integrableOn_exp_mul_Ioi hrate h).const_mul _
  have hbound : (∫ x in Ioi h, f x) ≤ ∫ x in Ioi h, e x := by
    apply setIntegral_mono_on hf.integrableOn hE measurableSet_Ioi
    intro x _
    unfold f e
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by
      nlinarith only [mul_nonneg hA.le (sq_nonneg (x - h))])
  have hei : (∫ x in Ioi h, e x) = Real.exp (-A * h ^ 2) / (2 * A * h) := by
    unfold e
    rw [integral_const_mul, integral_exp_mul_Ioi hrate h]
    rw [show -Real.exp (-(2 * A * h) * h) / -(2 * A * h) =
        Real.exp (-(2 * A * h) * h) / (2 * A * h) by ring, ← mul_div_assoc,
      ← Real.exp_add]
    congr 2
    ring
  have hneg : (∫ x in Iio (-h), f x) = ∫ x in Ioi h, f x := by
    rw [← integral_Iic_eq_integral_Iio]
    simpa [f, neg_sq] using (integral_comp_neg_Ioi h f).symm
  have hs : (Icc (-h) h)ᶜ = Iio (-h) ∪ Ioi h := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  rw [hs, setIntegral_union (disjoint_left.2 (fun x hx hy => by
    have hx' : x < -h := hx
    have hy' : h < x := hy
    linarith only [hx',hy',hh])) measurableSet_Ioi hf.integrableOn hf.integrableOn, hneg]
  have hpos := hbound.trans_eq hei
  calc
    _ ≤ Real.exp (-A * h ^ 2) / (2 * A * h) +
      Real.exp (-A * h ^ 2) / (2 * A * h) := add_le_add hpos hpos
    _ = _ := by ring

/-- The fourth Gaussian moment, compared with its total mass. -/
theorem midGaussian_fourth_moment {A : ℝ} (hA : 0 < A) :
    (∫ x : ℝ, x ^ 4 * Real.exp (-A * x ^ 2)) =
      (∫ x : ℝ, Real.exp (-A * x ^ 2)) * (3 / (4 * A ^ 2)) := by
  let f (x : ℝ) := x ^ 4 * Real.exp (-A * x ^ 2)
  have hf : Integrable f := by
    simpa only [f, Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hA (s := (4 : ℕ)) (by norm_num))
  have hneg : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    simpa [f, neg_sq, show Even (4 : ℕ) by decide] using (integral_comp_neg_Ioi 0 f).symm
  have hpos : (∫ x in Ioi (0 : ℝ), f x) =
      A ^ (-5 / 2 : ℝ) * (1 / 2) * Real.Gamma (5 / 2) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℕ)) (q := (4 : ℕ))
      (by norm_num) (by norm_num) hA
    convert h using 2 <;> norm_num [f, Real.rpow_natCast]
  change (∫ x, f x) = _
  rw [← integral_add_compl measurableSet_Ioi hf, compl_Ioi, hneg, hpos,
    DurfeeCCS.Step08.gamma_five_halves, integral_gaussian A,
    Real.sqrt_div Real.pi_nonneg]
  rw [show (-5 / 2 : ℝ) = -2 - 1 / 2 by norm_num,
    Real.rpow_sub hA, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hA.le, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  ring

/-- The norm of a double-ended phase error can be controlled by a single Gaussian. -/
theorem midGaussian_integrable_quartic {A : ℝ} (hA : 0 < A) :
    Integrable (fun x : ℝ => x ^ 4 * Real.exp (-A * x ^ 2)) := by
  simpa only [Real.rpow_natCast] using
    (integrable_rpow_mul_exp_neg_mul_sq hA (s := (4 : ℕ)) (by norm_num))

end DurfeeCCS.Step09
