module

public import DurfeeCCS.Step10.OuterBesselKernel
public import DurfeeCCS.Step10.OuterCoeffBessel

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Pointwise bounds on the compactly supported kernel of page 39. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Complex DurfeeCCS.Step06

private theorem besselI_two_re_ge_quadratic {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 8 ≤ (besselI 2 (x : ℂ)).re := by
  have hsum := Complex.hasSum_re (summable_besselITerm 2 (x : ℂ)).hasSum
  have hnn (k : ℕ) : 0 ≤ (besselITerm 2 k (x : ℂ)).re := by
    have he : besselITerm 2 k (x : ℂ) =
        (((x / 2) ^ (2 * k + 2) / ((k.factorial : ℝ) * ((k + 2).factorial : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [he, Complex.ofReal_re]
    positivity
  have h := hsum.summable.sum_le_tsum (s := {0}) (fun k _ => hnn k)
  simp only [Finset.sum_singleton] at h
  rw [hsum.tsum_eq] at h
  convert h using 1 <;> try rfl
  have he : besselITerm 2 0 (x : ℂ) = ((x ^ 2 / 8 : ℝ) : ℂ) := by
    norm_num [besselITerm, Nat.factorial]
    ring
  rw [he, Complex.ofReal_re]

/-- The kernel vanishes off its support and lies between zero and the stated exponential bound. -/
theorem outerBesselKernel_bounds {y : ℝ} (hy : 0 < y) (x : ℝ) :
    0 ≤ outerBesselKernel y x ∧
      outerBesselKernel y x ≤ (Real.pi ^ 3 / 36) * Real.exp (2 * Real.pi * y / Real.sqrt 3) := by
  by_cases hx : |x| < y
  · rw [outerBesselKernel_eq_bessel hy hx]
    let u := y ^ 2 - x ^ 2
    let z := 2 * Real.pi / Real.sqrt 3 * Real.sqrt u
    have hu : 0 < u := sub_pos.mpr (sq_lt_sq.2 (by simpa [abs_of_pos hy] using hx))
    have hz : 0 ≤ z := by dsimp [z]; positivity
    have hzsq : z ^ 2 / 8 = Real.pi ^ 2 * u / 6 := by
      dsimp [z]
      rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hu.le]
      ring
    have hfront : Real.pi * (z ^ 2 / 8) / (6 * u) = Real.pi ^ 3 / 36 := by
      rw [hzsq]
      field_simp
      norm_num
    have hzle : z ≤ 2 * Real.pi * y / Real.sqrt 3 := by
      change (2 * Real.pi / Real.sqrt 3) * Real.sqrt u ≤ _
      rw [show 2 * Real.pi * y / Real.sqrt 3 = (2 * Real.pi / Real.sqrt 3) * y by ring]
      gcongr
      exact Real.sqrt_le_left hy.le |>.2 (sub_le_self _ (sq_nonneg _))
    change 0 ≤ Real.pi * (besselI 2 (z : ℂ)).re / (6 * u) - Real.pi ^ 3 / 36 ∧ _
    constructor
    · rw [sub_nonneg, ← hfront]
      gcongr
      exact besselI_two_re_ge_quadratic hz
    · calc
        _ ≤ Real.pi * ((z ^ 2 / 8) * Real.exp z) / (6 * u) := by
          refine (sub_le_self _ (by positivity)).trans ?_
          gcongr
          exact (Complex.re_le_norm _).trans (norm_besselI_two_real_le hz)
        _ = (Real.pi ^ 3 / 36) * Real.exp z := by rw [← hfront]; ring
        _ ≤ _ := by gcongr
  · rw [outerBesselKernel_eq_zero hy.le (le_of_not_gt hx)]
    exact ⟨le_rfl, by positivity⟩

end DurfeeCCS.Step10
