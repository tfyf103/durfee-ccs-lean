module

public import DurfeeCCS.Step08.FirstSaddleProof
public import Mathlib.Basic.Real.Sign

/-! Exact polynomial signs at the cosine extrema in the first saddle range. -/

public section

namespace DurfeeCCS.Step08

open DurfeeCCS.Step06

/-- At either cosine extremum, the polynomial sign equals the cosine. -/
theorem firstSaddle_sign_at_cosine_extremum {n : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hscale : 4 * Real.pi ≤ Real.sqrt ((n : ℝ) * r))
    (hcos : Real.cos (saddlePhase n r) = 1 ∨ Real.cos (saddlePhase n r) = -1) :
    Real.sign (durfeeNegativeValue n r) = Real.cos (saddlePhase n r) := by
  obtain ⟨hpos, hneg⟩ := firstSaddle_sign hn hr hr₁ hscale
  rcases hcos with h | h
  · rw [Real.sign_of_pos (hpos h), h]
  · rw [Real.sign_of_neg (hneg h), h]

/-- The polynomial sign at a phase of kπ is exactly the alternating sign of k. -/
theorem firstSaddle_sign_at_phase {n k : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hscale : 4 * Real.pi ≤ Real.sqrt ((n : ℝ) * r))
    (hphase : saddlePhase n r = (k : ℝ) * Real.pi) :
    Real.sign (durfeeNegativeValue n r) = (-1 : ℝ) ^ k := by
  have hcos : Real.cos (saddlePhase n r) = (-1 : ℝ) ^ k := by
    rw [hphase, Real.cos_nat_mul_pi]
  have hextreme : Real.cos (saddlePhase n r) = 1 ∨ Real.cos (saddlePhase n r) = -1 := by
    rw [hcos]
    exact neg_one_pow_eq_or ℝ k
  exact (firstSaddle_sign_at_cosine_extremum hn hr hr₁ hscale hextreme).trans hcos

end DurfeeCCS.Step08
