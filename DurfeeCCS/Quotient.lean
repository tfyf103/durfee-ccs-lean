module

public import DurfeeCCS.Degree
public import DurfeeCCS.Scalars
public import Mathlib.Algebra.Polynomial.Inductions

/-! The quotient formed by removing the zero root from a positive-size Durfee polynomial. -/

@[expose] public section

namespace DurfeeCCS

open Polynomial

/-- The shifted Durfee coefficients, extended to `n = 0` by the same operation. -/
noncomputable def durfeeQuotient (n : ℕ) : Polynomial ℤ :=
  (durfeePolynomial n).divX

/-- The real polynomial obtained from the integral Durfee quotient. -/
noncomputable def durfeeQuotientReal (n : ℕ) : Polynomial ℝ :=
  (durfeeQuotient n).map (Int.castRingHom ℝ)

@[simp] theorem coeff_durfeeQuotient (n d : ℕ) :
    (durfeeQuotient n).coeff d = (p n (d + 1) : ℤ) := by
  simp [durfeeQuotient]

@[simp] theorem coeff_durfeeQuotientReal (n d : ℕ) :
    (durfeeQuotientReal n).coeff d = (p n (d + 1) : ℝ) := by
  simp [durfeeQuotientReal]

@[simp] theorem durfeeQuotient_zero : durfeeQuotient 0 = 0 := by
  simp [durfeeQuotient]

theorem durfeePolynomial_eq_X_mul_quotient {n : ℕ} (hn : 0 < n) :
    durfeePolynomial n = X * durfeeQuotient n := by
  symm
  simpa [durfeeQuotient, p_zero_of_pos hn] using (durfeePolynomial n).X_mul_divX_add

theorem durfeePolynomialReal_eq_X_mul_quotient {n : ℕ} (hn : 0 < n) :
    durfeePolynomialReal n = X * durfeeQuotientReal n := by
  simpa only [durfeePolynomialReal, durfeeQuotientReal, Polynomial.map_mul, Polynomial.map_X]
    using congrArg (fun f => f.map (Int.castRingHom ℝ)) (durfeePolynomial_eq_X_mul_quotient hn)

theorem natDegree_durfeePolynomialReal (n : ℕ) : (durfeePolynomialReal n).natDegree = n.sqrt := by
  rw [durfeePolynomialReal, Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    natDegree_durfeePolynomial]

theorem durfeePolynomialComplex_eq_map_real (n : ℕ) :
    durfeePolynomialComplex n = (durfeePolynomialReal n).map Complex.ofRealHom := by
  ext d
  simp [Polynomial.coeff_map]

@[simp] theorem durfeeQuotientReal_eval_zero (n : ℕ) :
    (durfeeQuotientReal n).eval 0 = (n : ℝ) := by
  simp [← Polynomial.coeff_zero_eq_eval_zero]

theorem natDegree_durfeeQuotient (n : ℕ) : (durfeeQuotient n).natDegree = n.sqrt - 1 := by
  rw [durfeeQuotient, Polynomial.natDegree_divX_eq_natDegree_tsub_one, natDegree_durfeePolynomial]

theorem natDegree_durfeeQuotientReal {n : ℕ} (_hn : 0 < n) :
    (durfeeQuotientReal n).natDegree = n.sqrt - 1 := by
  rw [durfeeQuotientReal, Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    natDegree_durfeeQuotient]

theorem leadingCoeff_durfeeQuotientReal_pos {n : ℕ} (hn : 0 < n) :
    0 < (durfeeQuotientReal n).leadingCoeff := by
  have hm : 0 < n.sqrt := Nat.sqrt_pos.mpr hn
  rw [Polynomial.leadingCoeff, natDegree_durfeeQuotientReal hn, coeff_durfeeQuotientReal,
    Nat.sub_add_cancel hm]
  exact_mod_cast p_pos_of_square_le hm (Nat.sqrt_le n)

end DurfeeCCS
