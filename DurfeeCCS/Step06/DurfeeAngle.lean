module

public import DurfeeCCS.Step06.AngleCoefficients
public import DurfeeCCS.Step06.GeneratingAnalytic

/-! Equation (4) applied to the Durfee polynomials defined from integer partitions. -/

public section

namespace DurfeeCCS.Step06

open Complex

theorem durfeePolynomials_angular_coefficient (n : ℕ) (r u : ℝ) (hu : 0 < u) :
    (durfeePolynomialComplex n).eval (-(r : ℂ) ^ 2) =
      (2 * Real.pi : ℂ)⁻¹ * ∫ v : ℝ in -Real.pi..Real.pi,
        Complex.exp ((n : ℂ) * ((u : ℂ) + v * I)) *
          durfeeAnalyticF (-(r : ℂ) ^ 2) (Complex.exp (-((u : ℂ) + v * I))) := by
  have hnorm : ‖Complex.exp (-(u : ℂ))‖ < 1 := by
    rw [Complex.norm_exp]
    simpa using Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  exact angular_coefficient_of_summable
    (fun m => (durfeePolynomialComplex m).eval (-(r : ℂ) ^ 2)) n u
    (summable_norm_durfeeAnalyticF _ hnorm)

end DurfeeCCS.Step06
