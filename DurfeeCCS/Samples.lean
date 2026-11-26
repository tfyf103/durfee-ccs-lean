module

public import DurfeeCCS.Degree
public import DurfeeCCS.EquationOne
import Mathlib.Tactic.NormNum

/-! Exact small cases derived from the partition counts and the proved recurrence. -/

public section

namespace DurfeeCCS

open Polynomial

theorem durfeePolynomial_one : durfeePolynomial 1 = X := by
  ext d
  by_cases h₀ : d = 0
  · subst d
    simp [p_zero_of_pos]
  by_cases h₁ : d = 1
  · subst d
    simp
  have hs : 1 < d * d := by
    have h₂ : 2 ≤ d := by omega
    have : 2 * 2 ≤ d * d := Nat.mul_le_mul h₂ h₂
    omega
  simp [p_eq_zero_of_sq_gt hs, coeff_X, Ne.symm h₁]

theorem durfeePolynomial_four : durfeePolynomial 4 = C 4 * X + X ^ 2 := by
  ext d
  by_cases h : 2 < d
  · have hs : 4 < d * d := by
      have h₃ : 3 ≤ d := by omega
      have : 3 * 3 ≤ d * d := Nat.mul_le_mul h₃ h₃
      omega
    have hx₂ : d ≠ 2 := by omega
    have hx₁ : 1 ≠ d := by omega
    simp [p_eq_zero_of_sq_gt hs, coeff_X_pow, coeff_X, hx₂, hx₁]
  · have hd : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd with rfl | rfl | rfl
    · norm_num [p_zero_of_pos]
    · norm_num
    · have hp : p 4 2 = 1 := p_square 2
      norm_num [hp, coeff_X]

theorem durfeePolynomial_nine : durfeePolynomial 9 = C 9 * X + C 20 * X ^ 2 + X ^ 3 := by
  have h₂ : p 9 2 = 20 := by
    exact_mod_cast (p_eq_coeff_restrictedPairSeries (n := 9) (d := 2) (by decide)).trans
      coeff_pairSeries_two_five
  have h₃ : p 9 3 = 1 := p_square 3
  ext d
  by_cases h : 3 < d
  · have hs : 9 < d * d := by
      have h₄ : 4 ≤ d := by omega
      have : 4 * 4 ≤ d * d := Nat.mul_le_mul h₄ h₄
      omega
    have hx₁ : 1 ≠ d := by omega
    have hx₂ : d ≠ 2 := by omega
    have hx₃ : d ≠ 3 := by omega
    simp [p_eq_zero_of_sq_gt hs, coeff_X_pow, coeff_X, hx₁, hx₂, hx₃]
  · have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hd with rfl | rfl | rfl | rfl <;>
      norm_num [p_zero_of_pos, h₂, h₃, coeff_X, coeff_X_pow]

end DurfeeCCS
