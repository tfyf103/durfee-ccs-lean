module

public import DurfeeCCS.Core
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace DurfeeCCS

/-- The real polynomial obtained from the integral one by coefficient mapping. -/
noncomputable def durfeePolynomialReal (n : ℕ) : Polynomial ℝ :=
  (durfeePolynomial n).map (Int.castRingHom ℝ)

/-- The complex polynomial obtained from the integral one by coefficient mapping. -/
noncomputable def durfeePolynomialComplex (n : ℕ) : Polynomial ℂ :=
  (durfeePolynomial n).map (Int.castRingHom ℂ)

@[simp] theorem coeff_durfeePolynomialReal (n d : ℕ) :
    (durfeePolynomialReal n).coeff d = (p n d : ℝ) := by
  simp [durfeePolynomialReal]

@[simp] theorem coeff_durfeePolynomialComplex (n d : ℕ) :
    (durfeePolynomialComplex n).coeff d = (p n d : ℂ) := by
  simp [durfeePolynomialComplex]

end DurfeeCCS
