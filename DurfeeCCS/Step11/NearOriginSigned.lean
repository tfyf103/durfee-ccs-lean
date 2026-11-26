module

public import Mathlib.Basic.Real.Sign
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace DurfeeCCS.Step11

theorem signed_positive_of_sign {x : ℝ} {k : ℕ}
    (h : Real.sign x = (-1 : ℝ) ^ k) : 0 < (-1 : ℝ) ^ k * x := by
  have hne : x ≠ 0 := by
    intro hx
    rw [hx, Real.sign_zero] at h
    exact pow_ne_zero _ (by norm_num) h.symm
  rw [← h]
  exact Real.sign_mul_pos_of_ne_zero x hne

theorem pos_of_sign_one {x : ℝ} (h : Real.sign x = 1) : 0 < x := by
  simpa only [pow_zero, one_mul] using signed_positive_of_sign (k := 0) (by simpa using h)

/-- Two values at consecutive parity indices have opposite strict signs. -/
theorem mul_neg_of_consecutive_signs {x y : ℝ} {k : ℕ}
    (hx : Real.sign x = (-1 : ℝ) ^ (k + 1)) (hy : Real.sign y = (-1 : ℝ) ^ k) :
    x * y < 0 := by
  have h := mul_pos (signed_positive_of_sign hx) (signed_positive_of_sign hy)
  rw [pow_succ] at h
  rw [show ((-1 : ℝ) ^ k * -1 * x) * ((-1 : ℝ) ^ k * y) =
    ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * -(x * y) by ring, ← mul_pow] at h
  norm_num at h
  exact h

end DurfeeCCS.Step11
