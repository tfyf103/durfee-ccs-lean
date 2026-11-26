module

public import DurfeeCCS.FiniteRoots
public import Mathlib.Algebra.Polynomial.Derivative

/-! The origin and the exact interpretation of the completed Durfee root list. -/

public section

namespace DurfeeCCS.Step11

open Polynomial

theorem durfeePolynomialReal_eval_zero {n : ℕ} (hn : 1 ≤ n) :
    (durfeePolynomialReal n).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_durfeePolynomialReal, p_zero_of_pos hn, Nat.cast_zero]

/-- The coefficient of X is the number of hooks, which is n. -/
theorem durfeePolynomialReal_derivative_eval_zero (n : ℕ) :
    (durfeePolynomialReal n).derivative.eval 0 = (n : ℝ) := by
  simp [← coeff_zero_eq_eval_zero, coeff_derivative]

theorem durfeePolynomialReal_origin_simple {n : ℕ} (hn : 1 ≤ n) :
    (durfeePolynomialReal n).IsRoot 0 ∧ (durfeePolynomialReal n).rootMultiplicity 0 = 1 := by
  refine ⟨durfeePolynomialReal_eval_zero hn, ?_⟩
  have hmap := eq_rootMultiplicity_map (p := durfeePolynomial n)
    (f := Int.castRingHom ℝ) Int.cast_injective 0
  simpa [durfeePolynomialReal, rootMultiplicity_zero_durfeePolynomial hn] using hmap.symm

/-- Counting the negative root subtype counts the distinct roots, independent of ordering. -/
theorem card_negative_roots_of_completed {n : ℕ} (h : HasDurfeeRoots n) :
    Nat.card {x : ℝ // x < 0 ∧ (durfeePolynomialReal n).IsRoot x} = n.sqrt - 1 := by
  obtain ⟨r, hneg, hroots⟩ := h
  let e (i : Fin (n.sqrt - 1)) :
      {x : ℝ // x < 0 ∧ (durfeePolynomialReal n).IsRoot x} :=
    ⟨r i, hneg i, (hroots.real_root_iff (r i)).2 (.inr ⟨i, rfl⟩)⟩
  have he : Function.Bijective e := by
    refine ⟨fun i j hij => r.injective (congrArg Subtype.val hij), ?_⟩
    rintro ⟨x, hx, hroot⟩
    rcases (hroots.real_root_iff x).1 hroot with rfl | ⟨i, rfl⟩
    · exact (lt_irrefl 0 hx).elim
    · exact ⟨i, Subtype.ext rfl⟩
  classical
  rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_fin]

end DurfeeCCS.Step11
