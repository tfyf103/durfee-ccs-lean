module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

/-- The shifted size parameter for the outer estimates. -/
def outerY (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) - 1 / 12)

theorem outerY_sq {n : ℕ} (hn : 0 < n) : (outerY n) ^ 2 = (n : ℝ) - 1 / 12 := by
  apply Real.sq_sqrt
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The radius parameter for the coefficient of index d. -/
def farRadius (n d : ℕ) : ℝ := Real.sqrt ((outerY n) ^ 2 - (d : ℝ) ^ 2)

/-- The logarithmic sample point where the exponent is stationary at d. -/
def farSample (n d : ℕ) : ℝ :=
  2 * Real.pi * (d : ℝ) / (Real.sqrt 3 * farRadius n d)

/-- The common boundary of the two outer estimates. -/
def farThreshold (n : ℕ) : ℝ := 4 * (outerY n) ^ (1 / 3 : ℝ)

end DurfeeCCS.Step10
