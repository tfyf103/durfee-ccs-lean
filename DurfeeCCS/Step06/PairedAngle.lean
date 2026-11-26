module

public import DurfeeCCS.Step06.AngleCoefficients
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Angular averaging for a product of two absolutely convergent Fourier series. -/

@[expose] public section

namespace DurfeeCCS.Step06

open Complex MeasureTheory

/-- The average of two oppositely oriented Fourier series is their diagonal sum. -/
theorem angular_integral_mul_tsum (a b : ℕ → ℂ)
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) :
    (∫ θ : ℝ in -Real.pi..Real.pi,
      (∑' n : ℕ, a n * exp ((n : ℂ) * I * θ)) *
        (∑' m : ℕ, b m * exp (-(m : ℂ) * I * θ))) =
      (2 * Real.pi : ℂ) * ∑' n, a n * b n := by
  let f : ℕ × ℕ → ℝ → ℂ := fun nm θ =>
    a nm.1 * b nm.2 * exp ((Int.cast ((nm.1 : ℤ) - (nm.2 : ℤ)) : ℂ) * I * θ)
  let bound : ℕ × ℕ → ℝ := fun nm => ‖a nm.1‖ * ‖b nm.2‖
  have hmode (k : ℤ) (θ : ℝ) : ‖exp ((k : ℂ) * I * θ)‖ = 1 := by
    rw [show (k : ℂ) * I * θ = (((k : ℝ) * θ : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  have hnorm (nm : ℕ × ℕ) (θ : ℝ) : ‖f nm θ‖ = bound nm := by
    dsimp only [f, bound]
    rw [norm_mul, hmode ((nm.1 : ℤ) - (nm.2 : ℤ)) θ, mul_one, norm_mul]
  have hs : Summable bound := ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hf (nm : ℕ × ℕ) : Continuous (f nm) := by unfold f; fun_prop
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -Real.pi) (b := Real.pi) (μ := volume) (F := f)
    (f := fun θ => ∑' nm, f nm θ) (fun nm _ => bound nm)
    (fun nm => (hf nm).aestronglyMeasurable)
    (fun nm => ae_of_all _ fun θ _ => (hnorm nm θ).le)
    (ae_of_all _ fun _ _ => hs)
    intervalIntegrable_const
    (ae_of_all _ fun θ _ =>
      (Summable.of_norm (by simpa only [hnorm] using hs)).hasSum)
  have hpoint (θ : ℝ) :
      (∑' n : ℕ, a n * exp ((n : ℂ) * I * θ)) *
        (∑' m : ℕ, b m * exp (-(m : ℂ) * I * θ)) = ∑' nm, f nm θ := by
    have ha' : Summable fun n : ℕ => ‖a n * exp ((n : ℂ) * I * θ)‖ := by
      apply ha.congr
      intro n
      rw [norm_mul, show (n : ℂ) = ((n : ℤ) : ℂ) by simp, hmode, mul_one]
    have hb' : Summable fun m : ℕ => ‖b m * exp (-(m : ℂ) * I * θ)‖ := by
      apply hb.congr
      intro m
      have hm : ‖exp (-(m : ℂ) * I * θ)‖ = 1 := by
        simpa only [Int.cast_neg, Int.cast_natCast] using hmode (-(m : ℤ)) θ
      rw [norm_mul, hm, mul_one]
    rw [tsum_mul_tsum_of_summable_norm ha' hb']
    apply tsum_congr
    intro nm
    dsimp only [f]
    rw [mul_mul_mul_comm, ← exp_add]
    congr 2
    push_cast
    ring
  have hterm (n m : ℕ) :
      (∫ θ in -Real.pi..Real.pi, f (n, m) θ) =
        if m = n then (2 * Real.pi : ℂ) * (a n * b n) else 0 := by
    dsimp only [f]
    rw [intervalIntegral.integral_const_mul, integral_integer_mode ((n : ℤ) - (m : ℤ))]
    by_cases hmn : m = n
    · subst m
      simp [mul_comm]
    · have hnone : (n : ℤ) - (m : ℤ) ≠ 0 := by omega
      simp [hmn, hnone]
  calc
    _ = ∫ θ : ℝ in -Real.pi..Real.pi, ∑' nm, f nm θ := by simp_rw [hpoint]
    _ = ∑' nm, ∫ θ in -Real.pi..Real.pi, f nm θ := hsum.tsum_eq.symm
    _ = ∑' n, ∑' m, ∫ θ in -Real.pi..Real.pi, f (n, m) θ :=
      hsum.summable.tsum_prod
    _ = _ := by simp_rw [hterm, tsum_ite_eq, tsum_mul_left]

end DurfeeCCS.Step06
