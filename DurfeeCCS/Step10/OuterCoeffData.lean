module

public import DurfeeCCS.Step06.BesselSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The main term and comparison scale for the outer coefficient bounds. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Step06

/-- The comparison function in Lemma 4.2. -/
def outerComparisonB (y : ℝ) : ℝ :=
  Real.exp (2 * Real.pi * y / Real.sqrt 3) /
    (4 * (3 : ℝ) ^ (3 / 4 : ℝ) * y ^ (5 / 2 : ℝ))

theorem outerComparisonB_pos {y : ℝ} (hy : 0 < y) : 0 < outerComparisonB y := by
  unfold outerComparisonB
  positivity

/-- The Bessel contribution from the first denominator in (14). -/
def outerBesselMain (y : ℝ) : ℝ :=
  Real.pi * (besselI 2 ((2 * Real.pi * y / Real.sqrt 3 : ℝ) : ℂ)).re / (6 * y ^ 2)

/-- The shifted square root in the two-colour partition asymptotics. -/
def twoColourShift (t : ℕ) : ℝ := Real.sqrt ((t : ℝ) - 1 / 12)

theorem twoColourShift_pos {t : ℕ} (ht : 0 < t) : 0 < twoColourShift t := by
  have h : (1 : ℝ) ≤ t := by exact_mod_cast ht
  exact Real.sqrt_pos.mpr (by linarith)

theorem twoColourShift_sq {t : ℕ} (ht : 0 < t) : twoColourShift t ^ 2 = (t : ℝ) - 1 / 12 := by
  have h : (1 : ℝ) ≤ t := by exact_mod_cast ht
  exact Real.sq_sqrt (by linarith)

end DurfeeCCS.Step10
