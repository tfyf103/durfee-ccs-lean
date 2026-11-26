module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Fourier coefficient extraction on the full real angular interval. -/

@[expose] public section

namespace DurfeeCCS.Step06

open Complex MeasureTheory

/-- The orthogonal exponential modes for the normalization in (4). -/
theorem integral_integer_mode (k : ℤ) :
    (∫ v : ℝ in -Real.pi..Real.pi, Complex.exp ((k : ℂ) * I * v)) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [intervalIntegral.integral_const, Complex.real_smul, two_mul]
  · rw [ite_eq_right hk, integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast hk) I_ne_zero)]
    have harg : (k : ℂ) * I * ↑Real.pi =
        (k : ℂ) * I * ↑(-Real.pi) + (k : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, zero_div]

/-- The angular coefficient formula for any series converging absolutely at the circle radius.
The summable bounds below are independent of the angle, so the interchange is justified. -/
theorem angular_coefficient_of_summable (a : ℕ → ℂ) (n : ℕ) (u : ℝ)
    (ha : Summable (fun m => ‖a m * Complex.exp (-(u : ℂ)) ^ m‖)) :
    a n = (2 * Real.pi : ℂ)⁻¹ *
      ∫ v : ℝ in -Real.pi..Real.pi,
        Complex.exp ((n : ℂ) * ((u : ℂ) + v * I)) *
          (∑' m, a m * Complex.exp (-((u : ℂ) + v * I)) ^ m) := by
  let f : ℕ → ℝ → ℂ := fun m v =>
    a m * Complex.exp (((n : ℂ) - m) * u) *
      Complex.exp ((Int.cast ((n : ℤ) - (m : ℤ)) : ℂ) * I * v)
  let bound : ℕ → ℝ := fun m => Real.exp (n * u) * ‖a m * Complex.exp (-(u : ℂ)) ^ m‖
  have hnorm (m : ℕ) (v : ℝ) : ‖f m v‖ = bound m := by
    have hmode : (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * I * v =
        (((n : ℝ) - m) * v : ℝ) * I := by push_cast; ring
    have hu : ((n : ℂ) - m) * u = (((n : ℝ) - m) * u : ℝ) := by
      push_cast
      simp
    have hexp : Real.exp (((n : ℝ) - m) * u) =
        Real.exp (n * u) * (Real.exp (-u)) ^ m := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    change ‖a m * Complex.exp (((n : ℂ) - m) * u) *
      Complex.exp ((Int.cast ((n : ℤ) - (m : ℤ)) : ℂ) * I * v)‖ =
      Real.exp (n * u) * ‖a m * Complex.exp (-(u : ℂ)) ^ m‖
    rw [hmode, hu, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul,
      Complex.norm_exp_ofReal, norm_mul, norm_pow, Complex.norm_exp, Complex.neg_re,
      Complex.ofReal_re, hexp]
    ring
  have hs : Summable bound := ha.mul_left _
  have hf (m : ℕ) : Continuous (f m) := by unfold f; fun_prop
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -Real.pi) (b := Real.pi) (μ := volume) (F := f)
    (f := fun v => ∑' m, f m v) (fun m _ => bound m)
    (fun m => (hf m).aestronglyMeasurable)
    (fun m => ae_of_all _ fun v _ => (hnorm m v).le)
    (ae_of_all _ fun _ _ => hs)
    intervalIntegrable_const
    (ae_of_all _ fun v _ => (Summable.of_norm (by simpa only [hnorm] using hs)).hasSum)
  have hterm (m : ℕ) :
      (∫ v in -Real.pi..Real.pi, f m v) = if m = n then (2 * Real.pi : ℂ) * a n else 0 := by
    dsimp only [f]
    rw [intervalIntegral.integral_const_mul, integral_integer_mode ((n : ℤ) - (m : ℤ))]
    by_cases hmn : m = n
    · subst m
      simp [mul_comm]
    · have hnone : (n : ℤ) - (m : ℤ) ≠ 0 := by omega
      simp [hnone, hmn]
  have hf' (v : ℝ) :
      (∑' m, f m v) = Complex.exp ((n : ℂ) * ((u : ℂ) + v * I)) *
        ∑' m, a m * Complex.exp (-((u : ℂ) + v * I)) ^ m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    let b : ℂ := (u : ℂ) + v * I
    have he : ((n : ℂ) - m) * u + ((Int.cast ((n : ℤ) - (m : ℤ)) : ℂ) * I * v) =
        (n : ℂ) * b + (m : ℂ) * -b := by
      dsimp only [b]
      push_cast
      ring
    change a m * Complex.exp (((n : ℂ) - m) * u) *
        Complex.exp ((Int.cast ((n : ℤ) - (m : ℤ)) : ℂ) * I * v) =
      Complex.exp ((n : ℂ) * b) * (a m * Complex.exp (-b) ^ m)
    rw [← Complex.exp_nat_mul (-b) m, mul_assoc, ← Complex.exp_add, he, Complex.exp_add]
    ring
  have hint := hsum.tsum_eq
  simp_rw [hterm] at hint
  rw [tsum_ite_eq] at hint
  simp_rw [← hf']
  rw [← hint, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)

end DurfeeCCS.Step06
