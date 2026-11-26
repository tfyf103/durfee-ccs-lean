module

public import DurfeeCCS.Step06.BesselIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! Bounds for the modified Bessel function of order two. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Step06 Set MeasureTheory intervalIntegral

/-- The order-two Bessel bound obtained by comparing the series with order zero. -/
theorem norm_besselI_two_real_le {x : ℝ} (hx : 0 ≤ x) :
    ‖besselI 2 (x : ℂ)‖ ≤ x ^ 2 / 8 * Real.exp x := by
  have hterm (k : ℕ) :
      ‖besselITerm 2 k (x : ℂ)‖ ≤ x ^ 2 / 8 * ‖besselITerm 0 k (x : ℂ)‖ := by
    have hf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have hf₂ : (2 : ℝ) * k.factorial ≤ ((k + 2).factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hf.le,
        mul_nonneg (sq_nonneg (k : ℝ)) hf.le]
    simp only [besselITerm, add_zero, norm_div, norm_mul, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
    norm_num only [Complex.norm_ofNat]
    rw [pow_add]
    have hh := div_le_div_of_nonneg_left (a := (x / 2) ^ (2 * k) * (x / 2) ^ 2)
      (by positivity) (by positivity : (0 : ℝ) < (k.factorial : ℝ) * (2 * k.factorial))
      (mul_le_mul_of_nonneg_left hf₂ hf.le)
    refine hh.trans_eq ?_
    ring
  have hsum (m : ℕ) : (∑' k, ‖besselITerm m k (x : ℂ)‖) = (besselI m (x : ℂ)).re := by
    have hs := Complex.hasSum_re (summable_besselITerm m (x : ℂ)).hasSum
    rw [besselI, ← hs.tsum_eq]
    apply tsum_congr
    intro k
    change ‖besselITerm m k (x : ℂ)‖ = (besselITerm m k (x : ℂ)).re
    have hreal : besselITerm m k (x : ℂ) =
        (((x / 2) ^ (2 * k + m) / ((k.factorial : ℝ) * ((k + m).factorial : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_nonneg]
    positivity
  have hzero : (besselI 0 (x : ℂ)).re ≤ Real.exp x := by
    rw [besselI_zero_integral, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    have hp := Real.pi_pos
    have hh : (∫ t in (0 : ℝ)..Real.pi, Real.exp (x * Real.cos t)) ≤ Real.exp x * Real.pi := by
      have hh' := intervalIntegral.integral_mono_on (μ := volume) hp.le
        (f := fun t => Real.exp (x * Real.cos t)) (g := fun _ => Real.exp x)
        (Continuous.intervalIntegrable (by fun_prop) ..) (Continuous.intervalIntegrable continuous_const ..) (fun t _ =>
          Real.exp_le_exp.mpr (by simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one t) hx))
      simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh'
    calc
      Real.pi⁻¹ * (∫ t in (0 : ℝ)..Real.pi, Real.exp (x * Real.cos t)) ≤
          Real.pi⁻¹ * (Real.exp x * Real.pi) :=
        mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hp.le)
      _ = _ := by field_simp
  calc
    _ ≤ ∑' k, ‖besselITerm 2 k (x : ℂ)‖ := norm_tsum_le_tsum_norm (summable_norm_besselITerm _ _)
    _ ≤ ∑' k, x ^ 2 / 8 * ‖besselITerm 0 k (x : ℂ)‖ :=
      (summable_norm_besselITerm _ _).tsum_le_tsum hterm
        ((summable_norm_besselITerm _ _).mul_left _)
    _ ≤ _ := by rw [tsum_mul_left, hsum 0]; gcongr

end DurfeeCCS.Step10
