module

public import DurfeeCCS.Step06.Saddle
public import DurfeeCCS.Step08.AngularMeans
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Angular mean and squared norm of the closed-disk saddle function. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06

def saddleGCoeff (r : ℝ) (n : ℕ) : ℂ :=
  -2 * (-(r : ℂ) * I) ^ (n + 1) / (((n + 1 : ℕ) : ℂ) ^ 2)

theorem saddleG_eq_cosineSeries (r θ : ℝ) (hr : |r| ≤ 1) :
    saddleG r θ = ∑' n : ℕ, saddleGCoeff r n * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ) := by
  let z : ℂ := -(r : ℂ) * I
  have hnorm : ‖z‖ = |r| := by simp [z, Real.norm_eq_abs]
  have hp : ‖z * exp ((θ : ℂ) * I)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hnorm]
    exact hr
  have hm : ‖z * exp (-(θ : ℂ) * I)‖ ≤ 1 := by
    rw [← Complex.ofReal_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hnorm]
    exact hr
  have hs := (principalDilog_hasSum hp).neg.sub (principalDilog_hasSum hm)
  symm
  apply HasSum.tsum_eq
  change HasSum _ (-(principalDilog (z * exp ((θ : ℂ) * I))) -
    principalDilog (z * exp (-(θ : ℂ) * I)))
  refine hs.congr_fun ?_
  intro n
  have he (t : ℝ) :
      Complex.exp ((t : ℂ) * I) ^ (n + 1) =
        Complex.exp ((((n + 1 : ℕ) : ℝ) * t : ℝ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [saddleGCoeff, mul_pow, ← Complex.ofReal_neg, he]
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  have heq : ((n : ℂ) + 1) * -(θ : ℂ) * I = -(((n : ℂ) + 1) * θ * I) := by ring
  rw [heq]
  dsimp only [z]
  ring

theorem norm_saddleGCoeff (r : ℝ) (n : ℕ) :
    ‖saddleGCoeff r n‖ = 2 * |r| ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [saddleGCoeff, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  simp [Real.norm_eq_abs]

theorem summable_norm_saddleGCoeff (r : ℝ) (hr : |r| ≤ 1) :
    Summable (fun n => ‖saddleGCoeff r n‖) := by
  have hs₀ := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^2) 1).2
    hasSum_zeta_two.summable
  apply (hs₀.mul_left (2 : ℝ)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [norm_saddleGCoeff, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hr) (by positivity)) (by norm_num)

theorem angularAverage_saddleG (r : ℝ) (hr : |r| ≤ 1) :
    angularAverage (saddleG r) = 0 := by
  change angularAverage (fun t => saddleG r t) = 0
  simp_rw [saddleG_eq_cosineSeries r _ hr]
  exact angularAverage_cosineSeries _ (summable_norm_saddleGCoeff r hr)

theorem angularMean_norm_sq_saddleG (r : ℝ) (hr : |r| ≤ 1) :
    angularMean (fun θ => ‖saddleG r θ‖ ^ 2) =
      2 * ∑' n : ℕ, r ^ (2 * (n + 1)) / (((n + 1 : ℕ) : ℝ) ^ 4) := by
  simp_rw [saddleG_eq_cosineSeries r _ hr]
  rw [angularMean_norm_sq_cosineSeries _ (summable_norm_saddleGCoeff r hr)]
  have he (n : ℕ) : ‖saddleGCoeff r n‖ ^ 2 =
      4 * (r ^ (2 * (n + 1)) / (((n + 1 : ℕ) : ℝ) ^ 4)) := by
    have hp : (|r| ^ (n + 1)) ^ 2 = r ^ (2 * (n + 1)) := by
      rw [← pow_mul, Nat.mul_comm (n + 1) 2, pow_mul, sq_abs, ← pow_mul]
    rw [norm_saddleGCoeff, div_pow, mul_pow, hp, ← pow_mul, mul_div_assoc]
    norm_num
  simp_rw [he, tsum_mul_left]
  ring

private theorem tsum_zeta_four_succ :
    (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 4)) = Real.pi ^ 4 / 90 := by
  have h := hasSum_zeta_four.summable.sum_add_tsum_nat_add 1
  rw [hasSum_zeta_four.tsum_eq] at h
  simpa using h

theorem angularMean_norm_sq_saddleG_le {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    angularMean (fun θ => ‖saddleG r θ‖ ^ 2) ≤ 2.17 * r ^ 2 := by
  rw [angularMean_norm_sq_saddleG r (by simpa [abs_of_nonneg hr] using hr₁)]
  have hs := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^4) 1).2
    hasSum_zeta_four.summable
  let a : ℕ → ℝ := fun n => r ^ (2 * (n + 1)) / (((n + 1 : ℕ) : ℝ)^4)
  let b : ℕ → ℝ := fun n => r ^ 2 * (1 / (((n + 1 : ℕ) : ℝ)^4))
  have ha (n : ℕ) : 0 ≤ a n := by dsimp [a]; positivity
  have hab (n : ℕ) : a n ≤ b n := by
    dsimp only [a, b]
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_of_le_one hr hr₁ (by omega)
  have hb : Summable b := hs.mul_left _
  have hsum : (∑' n, a n) ≤ r ^ 2 * (Real.pi ^ 4 / 90) := by
    have h := (hb.of_nonneg_of_le ha hab).tsum_le_tsum hab hb
    simpa only [b, tsum_mul_left, tsum_zeta_four_succ] using h
  have hnum : 2 * (Real.pi ^ 4 / 90) ≤ 2.17 := by
    have ht := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 4
    linarith only [ht]
  calc
    _ ≤ 2 * (r ^ 2 * (Real.pi ^ 4 / 90)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = r ^ 2 * (2 * (Real.pi ^ 4 / 90)) := by ring
    _ ≤ r ^ 2 * 2.17 := mul_le_mul_of_nonneg_left hnum (sq_nonneg _)
    _ = _ := by ring

end DurfeeCCS.Step08
