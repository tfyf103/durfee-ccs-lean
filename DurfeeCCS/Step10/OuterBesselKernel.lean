module

public import DurfeeCCS.Step06.BesselSeries
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The compactly supported Bessel kernel used in the outer Durfee range. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open MeasureTheory Set intervalIntegral
open scoped ContDiff
open DurfeeCCS.Step06

/-- Smooth continuation in the squared radial variable after removing the constant term. -/
def outerBesselCore (u : ℝ) : ℝ :=
  Real.pi ^ 3 / 18 * ((besselAuxSeries 2).sum ((Real.pi ^ 2 / 3 * u : ℝ) : ℂ)).re -
    Real.pi ^ 3 / 36

@[simp] theorem outerBesselCore_zero : outerBesselCore 0 = 0 := by
  rw [outerBesselCore]
  have h : (besselAuxSeries 2).sum 0 = (1 / 2 : ℂ) := by
    rw [besselAuxSeries, FormalMultilinearSeries.sum]
    simp_rw [FormalMultilinearSeries.ofScalars_apply_eq]
    rw [tsum_eq_single 0]
    · norm_num [besselAuxCoeff]
    · intro n hn
      simp [zero_pow hn]
  rw [mul_zero, Complex.ofReal_zero, h]
  norm_num [Complex.div_re]
  ring

theorem contDiff_outerBesselCore {k : ℕ∞ω} : ContDiff ℝ k outerBesselCore := by
  have h : ContDiff ℂ k (besselAuxSeries 2).sum :=
    AnalyticOnNhd.contDiff (fun z _ => analyticAt_besselAuxSeries 2 z)
  have h' : ContDiff ℝ k (besselAuxSeries 2).sum := h.restrict_scalars ℝ
  have harg : ContDiff ℝ k (fun u : ℝ => ((Real.pi ^ 2 / 3 * u : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_id)
  exact (contDiff_const.mul (Complex.reCLM.contDiff.comp (h'.comp harg))).sub contDiff_const

/-- The interior Bessel formula for the smooth core. -/
theorem outerBesselCore_eq_bessel {u : ℝ} (hu : 0 < u) :
    outerBesselCore u =
      Real.pi * (besselI 2 ((2 * Real.pi / Real.sqrt 3 * Real.sqrt u : ℝ) : ℂ)).re / (6 * u) -
        Real.pi ^ 3 / 36 := by
  let z : ℝ := 2 * Real.pi / Real.sqrt 3 * Real.sqrt u
  have hs : (z / 2) ^ 2 = Real.pi ^ 2 / 3 * u := by
    dsimp [z]
    have h₃ : Real.sqrt (3 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    rw [show (2 * Real.pi / Real.sqrt 3 * Real.sqrt u / 2 : ℝ) =
      Real.pi / Real.sqrt 3 * Real.sqrt u by ring, mul_pow, div_pow]
    rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt hu.le]
  have hz : ((z : ℂ) / 2) ^ 2 = ((Real.pi ^ 2 / 3 * u : ℝ) : ℂ) := by exact_mod_cast hs
  change _ = Real.pi * (besselI 2 (z : ℂ)).re / (6 * u) - Real.pi ^ 3 / 36
  rw [besselI_eq_aux, hz, Complex.re_ofReal_mul, outerBesselCore]
  field_simp [hu.ne']
  ring

/-- The paper's function \(K_y\), vanishing outside \([-y,y]\). -/
def outerBesselKernel (y x : ℝ) : ℝ :=
  if x ^ 2 ≤ y ^ 2 then outerBesselCore (y ^ 2 - x ^ 2) else 0

theorem outerBesselKernel_eq_bessel {y x : ℝ} (hy : 0 < y) (hx : |x| < y) :
    outerBesselKernel y x =
      Real.pi * (besselI 2 ((2 * Real.pi / Real.sqrt 3 * Real.sqrt (y ^ 2 - x ^ 2) : ℝ) : ℂ)).re /
          (6 * (y ^ 2 - x ^ 2)) - Real.pi ^ 3 / 36 := by
  have h := (sq_lt_sq).2 (show |x| < |y| by rwa [abs_of_pos hy])
  rw [outerBesselKernel, ite_eq_left h.le, outerBesselCore_eq_bessel (sub_pos.2 h)]

theorem outerBesselKernel_eq_zero {y x : ℝ} (hy : 0 ≤ y) (hx : y ≤ |x|) :
    outerBesselKernel y x = 0 := by
  have h := (sq_le_sq).2 (show |y| ≤ |x| by rwa [abs_of_nonneg hy])
  rcases eq_or_lt_of_le h with h | h
  · simp [outerBesselKernel, h]
  · exact ite_eq_right h.not_ge

theorem continuous_outerBesselKernel (y : ℝ) : Continuous (outerBesselKernel y) := by
  unfold outerBesselKernel
  refine Continuous.if_le ((contDiff_outerBesselCore (k := 0)).continuous.comp
    (by fun_prop)) continuous_const (by fun_prop) continuous_const ?_
  intro x hx
  rw [hx, sub_self, outerBesselCore_zero]

/-- Bilateral Laplace transform of the compactly supported kernel. -/
def kernelTransform (y : ℝ) (ζ : ℂ) : ℂ :=
  ∫ x in -y..y, (outerBesselKernel y x : ℂ) * Complex.exp (ζ * (x : ℂ))

theorem kernelTransform_eq_core {y : ℝ} (hy : 0 ≤ y) (ζ : ℂ) :
    kernelTransform y ζ =
      ∫ x in -y..y, (outerBesselCore (y ^ 2 - x ^ 2) : ℂ) * Complex.exp (ζ * (x : ℂ)) := by
  unfold kernelTransform outerBesselKernel
  apply integral_congr
  intro x hx
  rw [uIcc_of_le (by linarith)] at hx
  simp only
  rw [ite_eq_left ((sq_le_sq).2 (by rw [abs_of_nonneg hy]; exact abs_le.2 hx))]

end DurfeeCCS.Step10
