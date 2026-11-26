module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Gaussian bound for the Fourier transform of a sum of Bernoulli variables. -/

@[expose] public section

open Complex Set

namespace DurfeeCCS

private theorem normSq_bernoulliFactor (p u : ℝ) :
    ‖1 - (p : ℂ) + (p : ℂ) * Complex.exp ((u : ℂ) * I)‖ ^ 2 =
      1 - 4 * p * (1 - p) * Real.sin (u / 2) ^ 2 := by
  have hcos : Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
    conv_lhs => rw [show u = 2 * (u / 2) by ring]
    exact Real.cos_two_mul_eq_one_sub (u / 2)
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, Complex.add_im,
    Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.exp_ofReal_mul_I_im, add_zero]
  calc
    _ = 1 - 2 * p * (1 - p) * (1 - Real.cos u) +
      p ^ 2 * (Real.sin u ^ 2 + Real.cos u ^ 2 - 1) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, sub_self, mul_zero, add_zero, hcos]; ring

/-- For a single Bernoulli factor, the squared modulus identity gives exponential decay. -/
theorem norm_bernoulliFactor_le (p u : ℝ) :
    ‖1 - (p : ℂ) + (p : ℂ) * Complex.exp ((u : ℂ) * I)‖ ≤
      Real.exp (-2 * p * (1 - p) * Real.sin (u / 2) ^ 2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [normSq_bernoulliFactor, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-2 * p * (1 - p) * Real.sin (u / 2) ^ 2) =
    -4 * p * (1 - p) * Real.sin (u / 2) ^ 2 by ring]
  calc
    _ = -4 * p * (1 - p) * Real.sin (u / 2) ^ 2 + 1 := by ring
    _ ≤ _ := Real.add_one_le_exp _

private theorem sin_half_sq_ge {u : ℝ} (hu : |u| ≤ Real.pi) :
    (u / Real.pi) ^ 2 ≤ Real.sin (u / 2) ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht : 0 ≤ |u| / 2 := by positivity
  have hs := Real.mul_le_sin ht (show |u| / 2 ≤ Real.pi / 2 by linarith)
  have hs' : |u| / Real.pi ≤ Real.sin (|u| / 2) := by
    convert hs using 1
    ring
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ |u| / Real.pi)
    ((by positivity : 0 ≤ |u| / Real.pi).trans hs')).2 hs'
  rw [show |u| / Real.pi = |u / Real.pi| by rw [abs_div, abs_of_pos hpi], sq_abs] at hsq
  by_cases h : 0 ≤ u
  · simpa [abs_of_nonneg h] using hsq
  · have hu' := lt_of_not_ge h
    simpa [abs_of_neg hu', neg_div, Real.sin_neg] using hsq

/-- The product of the uncentered Bernoulli factors has a Gaussian envelope on the
Fourier window after standardization by the square root of the total variance. -/
theorem norm_prod_bernoulliFactor_le_gaussian {ι : Type*} [Fintype ι]
    (p : ι → ℝ)
    (V : ℝ) (hV : V = ∑ i, p i * (1 - p i)) (hVpos : 0 < V) (t : ℝ)
    (ht : |t| ≤ Real.pi * Real.sqrt V) :
    ‖∏ i, (1 - (p i : ℂ) + (p i : ℂ) *
        Complex.exp (((t / Real.sqrt V : ℝ) : ℂ) * I))‖ ≤
      Real.exp (-(2 / Real.pi ^ 2) * t ^ 2) := by
  let u : ℝ := t / Real.sqrt V
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.2 hVpos
  have hu : |u| ≤ Real.pi := by
    unfold u
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact ht
  calc
    _ = ∏ i, ‖1 - (p i : ℂ) + (p i : ℂ) * Complex.exp ((u : ℂ) * I)‖ := by rw [norm_prod]
    _ ≤ ∏ i, Real.exp (-2 * p i * (1 - p i) * Real.sin (u / 2) ^ 2) := by
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      exact fun i _ ↦ norm_bernoulliFactor_le (p i) u
    _ = Real.exp (-2 * V * Real.sin (u / 2) ^ 2) := by
      rw [← Real.exp_sum, hV]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ Real.exp (-2 * V * (u / Real.pi) ^ 2) := by
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonpos_left (sin_half_sq_ge hu) (by linarith)
    _ = _ := by
      congr 1
      have hsq : Real.sqrt V ^ 2 = V := Real.sq_sqrt hVpos.le
      dsimp only [u]
      rw [div_pow, div_pow, hsq]
      field

end DurfeeCCS
