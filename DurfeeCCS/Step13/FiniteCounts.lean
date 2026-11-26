module

public import DurfeeCCS.Step05.All
public import Mathlib.Order.Interval.Finset.Nat

/-! Counts and exact cross multiplication for the finite root certificate audit. -/

public section

namespace DurfeeCCS.Step13

open Finset

theorem dyadicValue_lt_iff_cross_mul (a b : ℕ × ℕ) :
    dyadicValue a < dyadicValue b ↔
      a.1 * dyadicDenominator b < b.1 * dyadicDenominator a := by
  have ha : 0 < (dyadicDenominator a : ℝ) := by simp [dyadicDenominator_eq]
  have hb : 0 < (dyadicDenominator b : ℝ) := by simp [dyadicDenominator_eq]
  rw [dyadicValue, dyadicValue, div_lt_div_iff₀ ha hb]
  exact_mod_cast Iff.rfl

/-- Count the same pairs by weight first and by square size first. -/
private theorem sum_sqrt_sub (a : ℕ) (ha : 1 ≤ a) :
    ∑ n ∈ Icc 1 6400, (n.sqrt - a) =
      ∑ j ∈ Ioc a 80, (6401 - j * j) := by
  calc
    _ = ∑ n ∈ Icc 1 6400, ∑ j ∈ Ioc a 80, if j * j ≤ n then 1 else 0 := by
      apply sum_congr rfl
      intro n hn
      have hn' : n.sqrt ≤ 80 := by
        apply Nat.le_of_lt_succ
        exact Nat.sqrt_lt.mpr (by have := (mem_Icc.mp hn).2; omega)
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← Nat.card_Ioc]
      congr 1
      ext j
      simp only [mem_Ioc, mem_filter, ← Nat.le_sqrt]
      omega
    _ = ∑ j ∈ Ioc a 80, ∑ n ∈ Icc 1 6400, if j * j ≤ n then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hjpos : 1 ≤ j := by have := (mem_Ioc.mp hj).1; omega
      have hj' : 1 ≤ j * j := by simpa using Nat.mul_le_mul hjpos hjpos
      have hset : ((Icc 1 6400).filter fun n => j * j ≤ n) = Icc (j * j) 6400 := by
        ext n
        simp only [mem_Icc, mem_filter]
        omega
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, hset, Nat.card_Icc]
      rfl

theorem finite_sign_check_count : (∑ n ∈ Icc 1 6400, (n.sqrt - 2)) = 325403 := by
  rw [sum_sqrt_sub 2 (by decide)]
  decide +kernel

theorem finite_order_check_count : (∑ n ∈ Icc 1 6400, (n.sqrt - 3)) = 319011 := by
  rw [sum_sqrt_sub 3 (by decide)]
  decide +kernel

end DurfeeCCS.Step13
