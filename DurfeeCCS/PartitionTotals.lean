module

public import DurfeeCCS.Degree
public import DurfeeCCS.PartitionForm
import Mathlib.Algebra.BigOperators.Fin

/-! The coefficient sum agrees with the ordinary partition total. -/

public section

namespace DurfeeCCS

open scoped BigOperators

/-- Each partition contributes one when the Durfee polynomial is evaluated at one. -/
theorem durfeePolynomial_eval_one_eq_card_partitions (n : ℕ) :
    (durfeePolynomial n).eval 1 = (Fintype.card (Nat.Partition n) : ℤ) := by
  rw [durfeePolynomial_eq_sum_partitions, Polynomial.eval_finsetSum]
  simp

/-- For positive weight the quotient coefficient list has the same total, since the omitted
constant coefficient of the Durfee polynomial vanishes. -/
theorem sum_quotientCoefficients_eq_card_partitions {n : ℕ} (hn : 0 < n) :
    (List.ofFn (fun i : Fin n.sqrt => (p n (i.val + 1) : ℤ))).sum =
      (Fintype.card (Nat.Partition n) : ℤ) := by
  rw [List.sum_ofFn, ← durfeePolynomial_eval_one_eq_card_partitions]
  rw [Fin.sum_univ_eq_sum_range (fun i => (p n (i + 1) : ℤ))]
  simp only [durfeePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    one_pow, mul_one]
  rw [Finset.sum_range_succ' _ n.sqrt, p_zero_of_pos hn, Nat.cast_zero, add_zero]

end DurfeeCCS
