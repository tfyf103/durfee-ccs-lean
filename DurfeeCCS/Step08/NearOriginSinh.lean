module

public import DurfeeCCS.Step08.MidpointLogSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Taylor and denominator bounds for the hyperbolic sine in the near-origin estimates. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex

/-- In the Taylor tail, successive terms have ratio at most `x² / 20`. -/
private theorem sinh_tail_term_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    x ^ (2 * m + 3) / (((2 * m + 3 : ℕ).factorial : ℕ) : ℝ) ≤
      (x ^ 3 / 6) * (x ^ 2 / 20) ^ m := by
  induction m with
  | zero => norm_num
  | succ m hm =>
    rw [show 2 * (m + 1) + 3 = (2 * m + 3) + 2 by omega, pow_add, pow_succ]
    have hf : (0 : ℝ) < ((2 * m + 3 : ℕ).factorial : ℝ) := by positivity
    have hf' : ((2 * m + 3 + 2 : ℕ).factorial : ℝ) =
        ((2 * m + 3 : ℕ).factorial : ℝ) * (2 * (m : ℝ) + 4) * (2 * (m : ℝ) + 5) := by
      rw [show 2 * m + 3 + 2 = (2 * m + 3 + 1) + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hf']
    have hden : (20 : ℝ) ≤ (2 * (m : ℝ) + 4) * (2 * (m : ℝ) + 5) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) m, sq_nonneg (m : ℝ)]
    calc
      _ = (x ^ (2 * m + 3) / ((2 * m + 3 : ℕ).factorial : ℝ)) *
          (x ^ 2 / ((2 * (m : ℝ) + 4) * (2 * (m : ℝ) + 5))) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
      _ ≤ ((x ^ 3 / 6) * (x ^ 2 / 20) ^ m) * (x ^ 2 / 20) :=
        mul_le_mul hm (div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden)
          (by positivity) (by positivity)
      _ = _ := by ring

theorem norm_sinh_sub_self_le {z : ℂ} (hz : ‖z‖ ^ 2 < 20) :
    ‖sinh z - z‖ ≤ ‖z‖ ^ 3 / (6 * (1 - ‖z‖ ^ 2 / 20)) := by
  let t : ℕ → ℂ := fun m => z ^ (2 * m + 1) / ((2 * m + 1 : ℕ).factorial : ℂ)
  have ht : HasSum t (sinh z) := Complex.hasSum_sinh z
  let tail : ℕ → ℂ := fun m => t (m + 1)
  have hTail : ∑' m, tail m = sinh z - z := by
    have h := ht.summable.sum_add_tsum_nat_add 1
    have h₀ : t 0 = z := by simp [t]
    rw [Finset.sum_range_one, h₀, ht.tsum_eq] at h
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans h
  let b : ℕ → ℝ := fun m => (‖z‖ ^ 3 / 6) * (‖z‖ ^ 2 / 20) ^ m
  have hq : ‖z‖ ^ 2 / 20 < 1 := (div_lt_one (by norm_num : (0 : ℝ) < 20)).2 hz
  have hb : Summable b :=
    (summable_geometric_of_lt_one (by positivity) hq).mul_left _
  have hbound (m : ℕ) : ‖tail m‖ ≤ b m := by
    simpa only [t, tail, b, show 2 * (m + 1) + 1 = 2 * m + 3 by omega,
      norm_div, norm_pow, Complex.norm_natCast] using sinh_tail_term_le (norm_nonneg z) m
  calc
    _ = ‖∑' m, tail m‖ := by rw [hTail]
    _ ≤ ∑' m, b m := norm_tsum_le_tsum_norm ((hb.of_nonneg_of_le (fun _ => norm_nonneg _) hbound)) |>.trans
      ((hb.of_nonneg_of_le (fun _ => norm_nonneg _) hbound).tsum_le_tsum hbound hb)
    _ = _ := by
      rw [show (∑' m, b m) = (‖z‖ ^ 3 / 6) * ∑' m : ℕ, (‖z‖ ^ 2 / 20) ^ m by
          simp only [b, tsum_mul_left], tsum_geometric_of_lt_one (by positivity) hq]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private theorem two_sinh_half_norm_sq (z : ℂ) :
    ‖2 * sinh (z / 2)‖ ^ 2 =
      4 * Real.sinh (z.re / 2) ^ 2 + 4 * Real.sin (z.im / 2) ^ 2 := by
  have hz : z / 2 = ((z.re / 2 : ℝ) : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hz, sinh_add, sinh_mul_I, cosh_mul_I, norm_mul, mul_pow, Complex.norm_ofNat,
    ← normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    sub_zero, add_zero, zero_add, mul_one]
  nlinarith [Real.cosh_sq_sub_sinh_sq (z.re / 2), Real.cos_sq_add_sin_sq (z.im / 2),
    congrArg (fun t : ℝ => t * Real.sinh (z.re / 2) ^ 2)
      (Real.cos_sq_add_sin_sq (z.im / 2)),
    congrArg (fun t : ℝ => t * Real.sin (z.im / 2) ^ 2)
      (Real.cosh_sq_sub_sinh_sq (z.re / 2))]

theorem norm_two_sinh_half_ge {z : ℂ} (hr : 0 ≤ z.re) (hi : |z.im| ≤ Real.pi) :
    2 * ‖z‖ / Real.pi ≤ ‖2 * sinh (z / 2)‖ := by
  have hπ : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hs₀ := (Real.self_le_sinh_iff (x := z.re / 2)).2 (by positivity)
  have hs : z.re / Real.pi ≤ Real.sinh (z.re / 2) := by
    exact (div_le_div_of_nonneg_left hr (by norm_num) hπ).trans hs₀
  have hSin := Real.mul_abs_le_abs_sin (x := z.im / 2) (by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  have hSin' : |z.im| / Real.pi ≤ |Real.sin (z.im / 2)| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hSin
    convert hSin using 1
    ring
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [two_sinh_half_norm_sq, div_pow, mul_pow, ← normSq_eq_norm_sq, Complex.normSq_apply]
  have h₁ := pow_le_pow_left₀ (by positivity) hs 2
  have h₂ := pow_le_pow_left₀ (by positivity) hSin' 2
  simp only [div_pow, sq_abs] at h₂
  rw [div_pow] at h₁
  rw [mul_add, add_div]
  simp only [pow_two] at h₁ h₂
  have h := add_le_add
    (mul_le_mul_of_nonneg_left h₁ (by norm_num : (0 : ℝ) ≤ 4))
    (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ) ≤ 4))
  convert h using 1 <;> ring

theorem norm_two_sinh_half_sub_self_le {z : ℂ} (hz : ‖z‖ ^ 2 < 80) :
    ‖2 * sinh (z / 2) - z‖ ≤ ‖z‖ ^ 3 / (24 * (1 - ‖z‖ ^ 2 / 80)) := by
  have hnorm : ‖z / (2 : ℂ)‖ = ‖z‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
  have h := norm_sinh_sub_self_le (z := z / 2) (by rw [hnorm]; nlinarith)
  rw [hnorm] at h
  rw [show 2 * sinh (z / 2) - z = 2 * (sinh (z / 2) - z / 2) by ring,
    norm_mul, Complex.norm_ofNat]
  convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2) using 1
  rw [show (‖z‖ / 2) ^ 2 / 20 = ‖z‖ ^ 2 / 80 by ring]
  have hd : (1 - ‖z‖ ^ 2 / 80) ≠ 0 := by linarith
  field_simp
  ring

end DurfeeCCS.Step08
