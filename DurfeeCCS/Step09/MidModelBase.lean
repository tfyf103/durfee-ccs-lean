module

public import DurfeeCCS.Step08.NearOriginLaplace
public import DurfeeCCS.Step06.Branches
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The model contour and its phase gaps in Lemma 3.7. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set
open DurfeeCCS.Step08 (verticalPoint verticalPoint_re verticalPoint_im
  norm_verticalPoint_sq verticalPoint_ne_zero)

/-- The vertical contour with unit real part. -/
abbrev midModelZ (η : ℝ) : ℂ := verticalPoint 1 η

def midModelK (t ρ : ℝ) : ℂ := (t : ℂ) * midModelZ ρ ^ 2

def midModelOsc (t η : ℝ) : ℂ := Complex.exp ((t : ℂ) * (η : ℂ) * I)

def midModelWeight (t ρ : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ) - 2 * (t : ℂ) * (ρ : ℂ) * I)

/-- The H function in equation (51). -/
def midModelH (t ρ η : ℝ) : ℂ :=
  Complex.sqrt (midModelZ η) * Complex.exp (midModelK t ρ / midModelZ η)

/-- The integrand of the finite contour in Lemma 3.7. -/
def midModelIntegrand (t ρ η : ℝ) : ℂ :=
  Complex.sqrt (midModelZ η) *
    Complex.exp (-(t : ℂ) * (((η - ρ : ℝ) : ℂ) ^ 2) / midModelZ η)

def midModelJ (t ρ : ℝ) : ℂ :=
  ∫ η in (0 : ℝ)..(3 / 2), midModelIntegrand t ρ η

theorem midModelZ_ne_zero (η : ℝ) : midModelZ η ≠ 0 :=
  verticalPoint_ne_zero zero_lt_one η

theorem one_le_norm_midModelZ (η : ℝ) : 1 ≤ ‖midModelZ η‖ := by
  simpa using Complex.re_le_norm (midModelZ η)

theorem abs_le_norm_midModelZ (η : ℝ) : |η| ≤ ‖midModelZ η‖ := by
  simpa using Complex.abs_im_le_norm (midModelZ η)

theorem norm_midModelOsc (t η : ℝ) : ‖midModelOsc t η‖ = 1 := by
  rw [midModelOsc, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_midModelWeight (t ρ : ℝ) : ‖midModelWeight t ρ‖ = Real.exp (-t) := by
  rw [midModelWeight, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_midModelK (t ρ : ℝ) :
    ‖midModelK t ρ‖ = |t| * (1 + ρ ^ 2) := by
  rw [midModelK, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
    norm_verticalPoint_sq]
  norm_num

/-- Equation (51). -/
theorem midModelIntegrand_eq (t ρ η : ℝ) :
    midModelIntegrand t ρ η = midModelWeight t ρ * (midModelOsc t η * midModelH t ρ η) := by
  have hz := midModelZ_ne_zero η
  unfold midModelIntegrand midModelWeight midModelOsc midModelH
  calc
    _ = Complex.sqrt (midModelZ η) *
      (Complex.exp (-(t : ℂ) - 2 * (t : ℂ) * (ρ : ℂ) * I) *
        Complex.exp ((t : ℂ) * (η : ℂ) * I) *
        Complex.exp (midModelK t ρ / midModelZ η)) := by
      rw [← exp_add, ← exp_add]
      congr 2
      unfold midModelK
      field_simp [hz]
      unfold midModelZ verticalPoint
      push_cast
      ring_nf
      simp only [Complex.I_sq, mul_neg, mul_one, sub_eq_add_neg]
      ring
    _ = _ := by ring

theorem re_midModelZ_sq_div (ρ η : ℝ) :
    (midModelZ ρ ^ 2 / midModelZ η).re = 1 - (η - ρ) ^ 2 / (1 + η ^ 2) := by
  rw [Complex.div_re, Complex.normSq_eq_norm_sq, norm_verticalPoint_sq]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, verticalPoint_re, verticalPoint_im,
    one_mul, mul_one]
  have hp : (0 : ℝ) < 1 + η * η := by nlinarith [sq_nonneg η]
  field_simp
  ring

theorem re_midModelK_div (t ρ η : ℝ) :
    (midModelK t ρ / midModelZ η).re = t * (1 - (η - ρ) ^ 2 / (1 + η ^ 2)) := by
  rw [midModelK, mul_div_assoc, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, re_midModelZ_sq_div]

private theorem midModel_gap_nonneg_den (η : ℝ) : 0 < 1 + η ^ 2 := by positivity

theorem midModel_gap_left {ρ η : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hη : η ≤ 0) :
    ρ ^ 2 ≤ (η - ρ) ^ 2 / (1 + η ^ 2) := by
  rw [le_div_iff₀ (midModel_gap_nonneg_den η)]
  have h : 0 ≤ (1 - ρ ^ 2) * η ^ 2 :=
    mul_nonneg (sub_nonneg.mpr (by simpa using pow_le_pow_left₀ hρ hρ' 2)) (sq_nonneg _)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hρ hη]

theorem midModel_gap_right {ρ η : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hη : 3 / 2 ≤ η) :
    (3 - 2 * ρ) ^ 2 / 13 ≤ (η - ρ) ^ 2 / (1 + η ^ 2) := by
  rw [div_le_div_iff₀ (show (0 : ℝ) < 13 by norm_num) (midModel_gap_nonneg_den η)]
  have h₁ : 0 ≤ (1 - ρ ^ 2) * (η + 3 / 2) :=
    mul_nonneg (sub_nonneg.mpr (by simpa using pow_le_pow_left₀ hρ hρ' 2)) (by linarith)
  have h₂ : 0 ≤ 2 * ρ * ((3 / 2) * η - 1) :=
    mul_nonneg (by positivity) (by linarith)
  have h₃ := mul_nonneg (sub_nonneg.mpr hη) (add_nonneg h₁ h₂)
  nlinarith only [h₃]

theorem continuous_midModelOsc (t : ℝ) : Continuous (midModelOsc t) := by
  unfold midModelOsc
  fun_prop

end DurfeeCCS.Step09
