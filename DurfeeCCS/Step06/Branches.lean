module

public import Mathlib.Analysis.RCLike.Sqrt

/-! Compatibility of the principal logarithm, argument and square root. -/

public section

namespace DurfeeCCS.Step06

/-- On the cut plane Mathlib's branch has the range and square-root normalization of the paper. -/
theorem principalBranches {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    -Real.pi < z.arg ∧ z.arg < Real.pi ∧ z.sqrt = Complex.exp (z.log / 2) := by
  exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_lt_pi_iff.mpr
    ((Complex.mem_slitPlane_iff.mp hz).elim (fun h => Or.inl h.le) Or.inr),
    sqrt_eq_exp (Complex.slitPlane_ne_zero hz)⟩

theorem principalSqrt_sq (z : ℂ) : z.sqrt ^ 2 = z := by
  by_cases hz : z = 0
  · simp [hz]
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul]
  convert Complex.exp_log hz using 2
  ring

theorem principalSqrt_arg {z : ℂ} (hz : z ≠ 0) : z.sqrt.arg = z.arg / 2 := by
  have h : (z.log / 2).im = z.arg / 2 := by simp [Complex.log_im]
  have hlog : (Complex.exp (z.log / 2)).log = z.log / 2 :=
    Complex.log_exp (by rw [h]; linarith [Real.pi_pos, Complex.neg_pi_lt_arg z])
      (by rw [h]; linarith [Real.pi_pos, Complex.arg_le_pi z])
  rw [sqrt_eq_exp hz, ← Complex.log_im, hlog, h]

end DurfeeCCS.Step06
