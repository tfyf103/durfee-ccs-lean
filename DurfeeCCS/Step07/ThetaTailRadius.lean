module

public import DurfeeCCS.Step07.MidSaddleTail
public import DurfeeCCS.Step07.SaddleEndpointGrid
public import DurfeeCCS.Step07.SaddleGlobalMonotone
public import DurfeeCCS.Step07.ThetaBoundsTail

/-! Admissibility of the large-radius numerical budget on page 31. -/

@[expose] public section

namespace DurfeeCCS.Step07

open Real DurfeeCCS.Step06

/-- The exact lower saddle bounds at the initial logarithmic radius of the tail. -/
theorem theta38_tail_endpoint :
    (5.29406 : ℝ) ≤ (saddleS (exp 5)).re ∧
      (1.48481 : ℝ) ≤ (saddleS (exp 5)).im := by
  have h := saddleEndpointData_bounds 19
  constructor
  · have ha := h.re_lower
    norm_num [saddleEndpointData] at ha ⊢
    exact ha
  · have hb := h.im_lower
    norm_num [saddleEndpointData] at hb ⊢
    exact hb

/-- The tail parameters chosen in the paper dominate the actual saddle parameters. -/
theorem theta38_tail_inputs {x t : ℝ} (hx : 80 ≤ x) (ht : 5 ≤ t) (htx : t ≤ log x + 1) :
    let a := (saddleS (exp t)).re
    let b := (saddleS (exp t)).im
    (5.29406 : ℝ) ≤ a ∧ (1.48481 : ℝ) ≤ b ∧ b < π / 2 ∧
      exp (-t) ≤ exp (-5) ∧ a / x ≤ 0.072 ∧ b / a ≤ π / (2 * 5.29406) ∧
      theta38TailError x < 0.212 := by
  let a := (saddleS (exp t)).re
  let b := (saddleS (exp t)).im
  have hr := exp_le_exp.mpr ht
  have ha : 5.29406 ≤ a :=
    theta38_tail_endpoint.1.trans (monotoneOn_saddleS_re (exp_pos _) (exp_pos _) hr)
  have hb : 1.48481 ≤ b := theta38_tail_endpoint.2.trans
    (strictMonoOn_saddleS_im.monotoneOn (exp_pos _) (exp_pos _) hr)
  have hbmax := saddleS_exp_im_lt_pi_half (show 0 ≤ t by linarith)
  have hA : a ≤ theta38Growth x := saddleS_exp_re_le_arcGrowth (by linarith) htx
  have hx' : 0 < x := by linarith
  have hsquare : (√(x / 80)) ^ 2 = x / 80 := Real.sq_sqrt (by positivity)
  have hroot₁ : 1 ≤ √(x / 80) := Real.le_sqrt_of_sq_le (by
    rw [one_pow, le_div_iff₀ (by norm_num), one_mul]
    exact hx)
  have hroot₂ : √(x / 80) ≤ x / 80 := by
    calc
      _ ≤ (√(x / 80)) ^ 2 := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg (x / 80)) (sub_nonneg.mpr hroot₁)]
      _ = _ := hsquare
  refine ⟨ha, hb, hbmax, exp_le_exp.mpr (neg_le_neg ht), ?_, ?_, theta38_tail_error_lt hx⟩
  · apply (div_le_iff₀ hx').2
    calc
      _ ≤ theta38Growth x := hA
      _ ≤ 5.76 * √(x / 80) := theta38Growth_le hx
      _ ≤ 5.76 * (x / 80) := mul_le_mul_of_nonneg_left hroot₂ (by norm_num)
      _ = _ := by ring
  · have h := div_le_div₀ (by positivity : 0 ≤ π / 2) hbmax.le (by norm_num) ha
    exact h.trans_eq (by ring)

/-- The verified large-radius row, using the original range `r ≤ e√n`. -/
theorem theta38_tail_radius_verified {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 0 < r)
    (hlo : 5 ≤ log r) (hhi : r ≤ exp 1 * √(n : ℝ)) :
    (5.29406 : ℝ) ≤ (saddleS r).re ∧ (1.48481 : ℝ) ≤ (saddleS r).im ∧
      (saddleS r).im < π / 2 ∧ r⁻¹ ≤ exp (-5) ∧
      (saddleS r).re / √(n : ℝ) ≤ 0.072 ∧
      (saddleS r).im / (saddleS r).re ≤ π / (2 * 5.29406) ∧
      theta38TailError √(n : ℝ) < 0.212 := by
  have hx : 80 ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hx₀ : (√(n : ℝ)) ≠ 0 := (show 0 < √(n : ℝ) by linarith).ne'
  have hh := Real.log_le_log hr hhi
  rw [Real.log_mul (exp_ne_zero _) hx₀, Real.log_exp, add_comm] at hh
  have h := theta38_tail_inputs hx hlo hh
  dsimp only at h
  rwa [Real.exp_log hr, Real.exp_neg, Real.exp_log hr] at h

end DurfeeCCS.Step07
