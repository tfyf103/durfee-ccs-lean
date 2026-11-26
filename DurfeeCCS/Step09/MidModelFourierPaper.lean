module

public import DurfeeCCS.Step09.MidModelLaplace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The half-integer Fourier integral with the factorials written as in the manuscript. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory

theorem midModelCpow_eq_halfKernel (η : ℝ) (k : ℕ) :
    midModelZ η ^ (-(k : ℂ) - 3 / 2) = (midModelZ η).sqrt / midModelZ η ^ (k + 2) := by
  rw [show -(k : ℂ) - 3 / 2 = (2 : ℂ)⁻¹ - ((k + 2 : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_sub _ _ (midModelZ_ne_zero η), Complex.cpow_natCast]
  rfl

theorem integral_midModelCpow_fourier (k : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ η : ℝ, midModelOsc t η * (midModelZ η ^ (-(k : ℂ) - 3 / 2))) =
      ((2 : ℂ) * (Real.sqrt Real.pi : ℂ) * (4 : ℂ) ^ (k + 1) *
          ((k + 1).factorial : ℂ) / ((2 * k + 2).factorial : ℂ)) *
        Complex.exp (-(t : ℂ)) * ((t ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) := by
  simp_rw [midModelCpow_eq_halfKernel]
  rw [integral_midHalfKernel_fourier k ht]
  have hp : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hp₀ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hf : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 1)
  have hf₂ : ((2 * k + 2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * k + 2)
  unfold midHalfGammaCoeff
  push_cast
  rw [← hp]
  field_simp

end DurfeeCCS.Step09
