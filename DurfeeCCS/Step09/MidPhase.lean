module

public import DurfeeCCS.Step06.Theta
public import DurfeeCCS.Step08.MidpointLogSeries
public import DurfeeCCS.Step08.SaddleNormalization
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The phase and multiplier in (47)–(50). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory DurfeeCCS.Step06 DurfeeCCS.Step08

def midFrequency (p : ℤ) : ℝ := Real.pi * ((p : ℝ) + 1 / 2)

/-- The radius `(-1)^(p+1) / r` in the periodized integrals. -/
def midModeRadius (r : ℝ) (p : ℤ) : ℝ := if Even p then -r⁻¹ else r⁻¹

def midPhase (r : ℝ) (p : ℤ) (χ : ℝ) : ℂ :=
  ((Real.log r : ℂ) + (midFrequency p : ℂ) * I) ^ 2 + (Real.pi : ℂ) ^ 2 / 3 -
    (χ : ℂ) ^ 2 - saddleG (midModeRadius r p) χ

abbrev midU := saddleU

abbrev midOmega := saddleOmega

def midSlope (r : ℝ) : ℝ := (saddleS r).im / (saddleS r).re

def midEtaPoint (n : ℕ) (r η : ℝ) : ℂ := (midU n r : ℂ) * (1 + (η : ℂ) * I)

def midEtaTransform (ζ : ℂ) : ℂ := 4 * (Real.pi : ℂ) ^ 2 / ζ

/-- The multiplier after applying the modular Euler product identity. -/
def midMultiplier (r : ℝ) (p : ℤ) (ζ : ℂ) (χ : ℝ) : ℂ :=
  exp (-ζ / 12) / eulerProduct (midEtaTransform ζ) ^ 2 *
    exp (saddleG (midModeRadius r p) χ / ζ - pairedLog (midModeRadius r p) χ ζ)

/-- The integrand of the frequency contribution on the vertical line. -/
def midIntegrand (n : ℕ) (r : ℝ) (p : ℤ) (η χ : ℝ) : ℂ :=
  let ζ := midEtaPoint n r η
  exp ((n : ℂ) * ζ + midPhase r p χ / ζ) * midMultiplier r p ζ χ

def midContribution (n : ℕ) (r : ℝ) (p : ℤ) (l h : ℝ) : ℂ :=
  (midU n r / (4 * Real.pi ^ 2) : ℝ) *
    ∫ η in l..h, ∫ χ : ℝ, midIntegrand n r p η χ

@[simp] theorem midEtaPoint_re (n : ℕ) (r η : ℝ) :
    (midEtaPoint n r η).re = midU n r := by simp [midEtaPoint, Complex.mul_re]

@[simp] theorem midEtaPoint_im (n : ℕ) (r η : ℝ) :
    (midEtaPoint n r η).im = midU n r * η := by simp [midEtaPoint, Complex.mul_im]

theorem midEtaPoint_eq_vertical (n : ℕ) (r η : ℝ) :
    midEtaPoint n r η = verticalPoint (midU n r) (midU n r * η) := by
  unfold midEtaPoint verticalPoint
  rw [Complex.ofReal_mul]
  ring

theorem midModeRadius_abs {r : ℝ} (hr : 0 < r) (p : ℤ) :
    |midModeRadius r p| = r⁻¹ := by
  unfold midModeRadius
  split <;> simp [abs_of_nonneg (inv_nonneg.mpr hr.le)]

theorem midModeRadius_abs_le_one {r : ℝ} (hr : 1 ≤ r) (p : ℤ) :
    |midModeRadius r p| ≤ 1 := by
  rw [midModeRadius_abs (by positivity)]
  exact inv_le_one_of_one_le₀ hr

@[simp] theorem midModeRadius_zero (r : ℝ) : midModeRadius r 0 = -r⁻¹ := by simp [midModeRadius]

@[simp] theorem midModeRadius_neg_one (r : ℝ) : midModeRadius r (-1) = r⁻¹ := by
  unfold midModeRadius
  norm_num

theorem midSlope_bounds {r : ℝ} (hr : 0 < r) : 0 < midSlope r ∧ midSlope r < 1 := by
  obtain ⟨hb,hab⟩ := saddleS_components hr
  exact ⟨div_pos hb (hb.trans hab), (div_lt_one (hb.trans hab)).mpr hab⟩

end DurfeeCCS.Step09
