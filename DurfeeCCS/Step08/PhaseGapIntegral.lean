module

public import DurfeeCCS.Step06.SaddleComponents
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The logarithmic integral representation for the first saddle region. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06
open scoped Interval Real

private theorem intervalIntegrable_dilogKernel_one :
    IntervalIntegrable (dilogKernel 1) volume 0 1 := by
  have hcut : (1 / 2 : ℂ) ∈ dilogCut := mem_dilogCut_iff.mpr (Or.inl (by norm_num))
  have hs := (intervalIntegrable_dilogKernel hcut).comp_mul_left (c := (2 : ℝ))
  have hs' : IntervalIntegrable (fun t : ℝ => (2 : ℂ) * dilogKernel (1 / 2) (2 * t))
      volume 0 (1 / 2) := by
    simpa only [zero_div] using hs.const_mul (2 : ℂ)
  have h₁ : IntervalIntegrable (dilogKernel 1) volume 0 (1 / 2) := by
    refine (intervalIntegrable_congr_uIoo ?_).mpr hs'
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    intro t ht
    have ht' : 2 * t ≠ 0 := by linarith [ht.1]
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    simp only [dilogKernel, ite_eq_right ht.1.ne', ite_eq_right ht', Complex.ofReal_mul]
    push_cast
    have he : (1 : ℂ) - (2 * (t : ℂ)) * (1 / 2) = 1 - (t : ℂ) * 1 := by ring
    rw [he]
    field_simp
  have hl : IntervalIntegrable (fun t => Real.log (1 - t)) volume (1 / 2) 1 := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := (1 / 2 : ℝ)) (b := 0)).comp_sub_left 1
    convert h using 1 <;> norm_num
  have hlc : IntervalIntegrable (fun t => (Real.log (1 - t) : ℂ)) volume (1 / 2) 1 :=
    ⟨hl.1.ofReal, hl.2.ofReal⟩
  have hv : ContinuousOn (fun t : ℝ => ((t : ℂ)⁻¹)) (uIcc (1 / 2) 1) := by
    refine Complex.continuous_ofReal.continuousOn.inv₀ ?_
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    intro t ht
    have h : t ≠ 0 := by linarith [ht.1]
    exact_mod_cast h
  have h₂ : IntervalIntegrable (dilogKernel 1) volume (1 / 2) 1 := by
    refine (intervalIntegrable_congr_uIoo ?_).mpr (hlc.neg.mul_continuousOn hv)
    rw [uIoo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    intro t ht
    have ht₀ : t ≠ 0 := by linarith [ht.1]
    simp only [dilogKernel, ite_eq_right ht₀, mul_one, Pi.neg_apply, div_eq_mul_inv]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_log (sub_nonneg.mpr ht.2.le)]
  exact h₁.trans h₂

/-- Endpoint-integrability of the straight-segment dilogarithm on the closed unit disk. -/
theorem intervalIntegrable_dilogKernel_closedDisk {z : ℂ} (hz : ‖z‖ ≤ 1) :
    IntervalIntegrable (dilogKernel z) volume 0 1 := by
  by_cases hz' : z = 1
  · simpa [hz'] using intervalIntegrable_dilogKernel_one
  refine intervalIntegrable_dilogKernel (mem_dilogCut_iff.mpr ?_)
  by_cases him : z.im = 0
  · left
    have h := (Complex.re_le_norm z).trans hz
    refine lt_of_le_of_ne h ?_
    intro hre
    apply hz'
    apply Complex.ext
    · simpa using hre
    · simpa using him
  · exact Or.inr him

/-- The quadratic appearing inside the principal logarithm in (21). -/
noncomputable def saddleLogArgument (θ y : ℝ) : ℂ :=
  1 - (y : ℂ)^2 + 2 * (y : ℂ) * I * (Real.cos θ : ℂ)

private theorem saddleLogArgument_mul (θ y : ℝ) :
    saddleLogArgument θ y =
      (1 + (y : ℂ) * I * Complex.exp ((θ : ℂ) * I)) *
      (1 + (y : ℂ) * I * Complex.exp (-(θ : ℂ) * I)) := by
  unfold saddleLogArgument
  have hc : Complex.exp ((θ : ℂ) * I) + Complex.exp (-(θ : ℂ) * I) =
      2 * (Real.cos θ : ℂ) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp [Complex.ofReal_cos]
    ring
  have hp : Complex.exp ((θ : ℂ) * I) * Complex.exp (-(θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  calc
    _ = 1 + (y : ℂ) * I * (Complex.exp ((θ : ℂ) * I) +
         Complex.exp (-(θ : ℂ) * I)) +
         ((y : ℂ) * I)^2 * (Complex.exp ((θ : ℂ) * I) * Complex.exp (-(θ : ℂ) * I)) := by
      rw [hc, hp, mul_pow, Complex.I_sq]
      ring
    _ = _ := by ring

theorem log_mul_of_pos_re {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Complex.log (z * w) = Complex.log z + Complex.log w := by
  have hzne : z ≠ 0 := by intro h; simp [h] at hz
  have hwne : w ≠ 0 := by intro h; simp [h] at hw
  have h₁ := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have h₂ := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  exact Complex.log_mul hzne hwne ⟨by linarith [h₁.1, h₂.1], by linarith [h₁.2, h₂.2]⟩

private theorem norm_saddleSeed (r θ : ℝ) :
    ‖-(r : ℂ) * I * Complex.exp ((θ : ℂ) * I)‖ = |r| := by
  simp [Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs]

private theorem log_saddleLogArgument {y : ℝ} (hy : 0 ≤ y) (hy₁ : y < 1) (θ : ℝ) :
    Complex.log (saddleLogArgument θ y) =
      Complex.log (1 + (y : ℂ) * I * Complex.exp ((θ : ℂ) * I)) +
      Complex.log (1 + (y : ℂ) * I * Complex.exp (-(θ : ℂ) * I)) := by
  rw [saddleLogArgument_mul]
  have h (φ : ℝ) : 0 < (1 + (y : ℂ) * I * Complex.exp ((φ : ℂ) * I)).re := by
    have hn : ‖-((y : ℂ) * I * Complex.exp ((φ : ℂ) * I))‖ = y := by
      simp [Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hy]
    have hb := Complex.re_le_norm (-((y : ℂ) * I * Complex.exp ((φ : ℂ) * I)))
    rw [hn, Complex.neg_re] at hb
    simp only [Complex.add_re, Complex.one_re]
    linarith
  exact log_mul_of_pos_re (h θ) (by simpa [Complex.ofReal_neg] using h (-θ))

private theorem dilogKernels_eq_scaled (r θ t : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1)
    (ht : t ∈ Ioo 0 1) :
    -(dilogKernel (-(r : ℂ) * I * Complex.exp ((θ : ℂ) * I)) t +
      dilogKernel (-(r : ℂ) * I * Complex.exp (-(θ : ℂ) * I)) t) =
        (r : ℂ) * (Complex.log (saddleLogArgument θ (t * r)) / ((t * r : ℝ) : ℂ)) := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he (z : ℂ) : 1 - (t : ℂ) * (-(r : ℂ) * I * z) = 1 + ((t * r : ℝ) : ℂ) * I * z := by
    push_cast
    ring
  rw [log_saddleLogArgument (mul_nonneg ht.1.le hr.le)
      ((mul_le_of_le_one_right ht.1.le hr₁).trans_lt ht.2)]
  simp only [dilogKernel, ite_eq_right ht.1.ne', he]
  push_cast
  field_simp
  ring

/-- The integral in (21) is integrable including the singular endpoint (r=1). -/
theorem intervalIntegrable_saddle_log {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (θ : ℝ) :
    IntervalIntegrable (fun y : ℝ => Complex.log (saddleLogArgument θ y) / (y : ℂ))
      volume 0 r := by
  let f (y : ℝ) := Complex.log (saddleLogArgument θ y) / (y : ℂ)
  have hi (φ : ℝ) : IntervalIntegrable
      (dilogKernel (-(r : ℂ) * I * Complex.exp ((φ : ℂ) * I))) volume 0 1 :=
    intervalIntegrable_dilogKernel_closedDisk (by rw [norm_saddleSeed, abs_of_pos hr]; exact hr₁)
  have hp : IntervalIntegrable (fun t : ℝ => (r : ℂ) * f (t * r)) volume 0 1 := by
    apply (intervalIntegrable_congr_uIoo ?_).mp ((hi θ).add (hi (-θ))).neg
    rw [uIoo_of_le zero_le_one]
    intro t ht
    simpa only [Pi.neg_apply, Pi.add_apply, Complex.ofReal_neg, f] using
      dilogKernels_eq_scaled r θ t hr hr₁ ht
  have hp' := hp.const_mul (r : ℂ)⁻¹
  have hcomp : IntervalIntegrable (fun t : ℝ => f (t * r)) volume 0 1 := by
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simpa only [← mul_assoc, inv_mul_cancel₀ hrc, one_mul] using hp'
  have h := hcomp.comp_mul_right (c := r⁻¹)
  simpa only [zero_div, one_div, inv_inv, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one] using h

/-- The logarithmic formula (21) throughout (0<r≤1), with the endpoint taken in the integral. -/
theorem saddleG_eq_log_integral {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (θ : ℝ) :
    saddleG r θ = ∫ y in (0 : ℝ)..r, Complex.log (saddleLogArgument θ y) / (y : ℂ) := by
  let f (y : ℝ) := Complex.log (saddleLogArgument θ y) / (y : ℂ)
  have hi (φ : ℝ) : IntervalIntegrable
      (dilogKernel (-(r : ℂ) * I * Complex.exp ((φ : ℂ) * I))) volume 0 1 :=
    intervalIntegrable_dilogKernel_closedDisk (by rw [norm_saddleSeed, abs_of_pos hr]; exact hr₁)
  have he : (-((∫ t in (0 : ℝ)..1, dilogKernel
      (-(r : ℂ) * I * Complex.exp ((θ : ℂ) * I)) t) +
      (∫ t in (0 : ℝ)..1, dilogKernel (-(r : ℂ) * I * Complex.exp (-(θ : ℂ) * I)) t))) =
      r • (∫ t in (0 : ℝ)..1, f (t * r)) := by
    rw [← intervalIntegral.integral_add (hi θ) (by simpa [Complex.ofReal_neg] using hi (-θ)),
      ← intervalIntegral.integral_neg, Complex.real_smul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one ?_
    intro t ht
    exact dilogKernels_eq_scaled r θ t hr hr₁ ht
  rw [intervalIntegral.smul_integral_comp_mul_right f r, zero_mul, one_mul] at he
  simpa only [saddleG, principalDilog, neg_add, sub_eq_add_neg, f] using he

end DurfeeCCS.Step08
