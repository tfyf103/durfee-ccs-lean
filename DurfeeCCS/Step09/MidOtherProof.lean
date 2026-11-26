module

public import DurfeeCCS.Step09.MidOtherSums
public import DurfeeCCS.Step09.MidOtherOpposite

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Lemma 3.10 with the finite, infinite, and opposite-side contributions. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Real MeasureTheory Set DurfeeCCS.Step06

def midOtherRemainderMass (n : ℕ) (r : ℝ) : ℝ :=
  (∑' p : ℤ, if p = 0 ∨ p = -1 then 0 else midOtherMass n r p (-8) 8) +
  midOtherMass n r 0 (-8) 0 + midOtherMass n r (-1) 0 8

theorem midOther_three_ranges_bound {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ exp 1 * √(n : ℝ)) :
    midOtherMassFactor n r * midOtherRemainderMass n r <
      if log r < 1 then 0.000013 else if log r < 5 then 0.0003 else 0.00105 := by
  have hN := (midOther_nonprincipal_sum_bound hn hr hmax).2
  change (∑' p : ℤ, if p = 0 ∨ p = -1 then 0 else midOtherNormalizedMass n r p) < _ at hN
  have hterm (p : ℤ) : (if p = 0 ∨ p = -1 then 0 else midOtherNormalizedMass n r p) =
      midOtherMassFactor n r * (if p = 0 ∨ p = -1 then 0 else midOtherMass n r p (-8) 8) := by
    unfold midOtherNormalizedMass
    split_ifs <;> simp
  simp_rw [hterm, tsum_mul_left] at hN
  have hOpp := midOther_oppositeBudget_at_saddle hn hr hmax
  change midOtherMassFactor n r * (midOtherMass n r 0 (-8) 0 + midOtherMass n r (-1) 0 8) < _ at hOpp
  unfold midOtherRemainderMass
  rw [add_assoc, mul_add]
  by_cases h₁ : log r < 1
  · rw [ite_eq_left h₁] at hN hOpp ⊢
    linarith only [hN,hOpp]
  · rw [ite_eq_right h₁] at hN hOpp ⊢
    by_cases h₅ : log r < 5
    · rw [ite_eq_left h₅] at hN ⊢
      linarith only [hN,hOpp]
    · rw [ite_eq_right h₅] at hN ⊢
      linarith only [hN,hOpp]

theorem lemma310 {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ exp 1 * √(n : ℝ)) :
    midU n r / (4*π^2) *
      ((∑' p : ℤ, if p = 0 ∨ p = -1 then 0 else midOtherMass n r p (-8) 8) +
        midOtherMass n r 0 (-8) 0 + midOtherMass n r (-1) 0 8) <
      0.002 * saddleAmplitude n r := by
  have h := midOther_three_ranges_bound hn hr hmax
  have hp : 0 < saddleAmplitude n r := saddleAmplitude_pos (by omega) (by linarith)
  have hbound : midOtherMassFactor n r * midOtherRemainderMass n r < 0.002 := by
    refine h.trans_le ?_
    split_ifs <;> norm_num
  have H := mul_lt_mul_of_pos_right hbound hp
  unfold midOtherMassFactor midOtherRemainderMass at H
  convert H using 1
  field_simp [hp.ne']

end DurfeeCCS.Step09
