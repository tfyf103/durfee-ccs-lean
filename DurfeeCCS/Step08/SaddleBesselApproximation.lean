module

public import DurfeeCCS.Step08.SaddleBesselCutoff
public import DurfeeCCS.Step08.SaddleBesselEstimate

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Lemma 3.4, the uniform Bessel approximation (31). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open DurfeeCCS.Step06 DurfeeCCS.Step07

/-- The real-valued average is the Bessel integral written with the principal
root of `n * gᵣ(θ)`, as in the definition preceding Lemma 3.4. -/
theorem saddleBesselAverage_eq_integral {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : |r| ≤ 1) :
    (saddleBesselAverage n r : ℂ) = (2 * Real.pi : ℂ)⁻¹ *
      ∫ θ in -Real.pi..Real.pi, (saddleG r θ).sqrt / (Real.sqrt n : ℂ) *
        besselI 1 (2 * ((n : ℂ) * saddleG r θ).sqrt) := by
  rw [saddleBesselAverage_ofReal n hr]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have hroot : ((n : ℂ) * saddleG r θ).sqrt = (Real.sqrt n : ℂ) * (saddleG r θ).sqrt := by
    rw [← Complex.ofReal_natCast, sqrt_ofReal_mul _ (by positivity)]
  simp only [saddleBesselKernel_eq_besselI hn, hroot, mul_assoc]

/-- The Bessel error bound with the unrounded coefficient, for every positive integer order. -/
theorem lemma34 {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    |saddleBesselAverage n r - saddleAmplitude n r * Real.cos (saddlePhase n r)| ≤
      saddleAmplitude n r * firstSaddleE (saddleOmega n r) (saddleGamma r) :=
  saddleBessel_error_of_outer_cutoff hn hr hr₁ (saddleBessel_outer_cutoff_error hn hr hr₁)

/-- The manuscript's error function for (31), with its two stated constants. -/
def saddleBesselPaperError (t r : ℝ) : ℝ :=
  let γ := saddleGamma r
  let C : ℝ := if r ≤ 0.1 then 6.273 else 15.961
  C / t + (11.1 / γ + 2.4) / Real.sqrt t * Real.exp (-0.3 * γ * t) +
    19 * t ^ 2 * Real.exp (-t)

private theorem firstSaddleC_lt_of_sq {γ C : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C)
    (hs : 1.5 * (1.845 / γ ^ 2 + 0.435 / γ + 2.7742) ^ 2 < C ^ 2 * γ) :
    firstSaddleC γ < C := by
  unfold firstSaddleC
  rw [div_lt_iff₀ (Real.sqrt_pos.mpr hγ)]
  apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
  rwa [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (1.5 : ℝ)), Real.sq_sqrt hγ.le]

private theorem firstSaddleC_le_paper (r : ℝ) :
    firstSaddleC (saddleGamma r) ≤ if r ≤ 0.1 then 6.273 else 15.961 := by
  by_cases hr : r ≤ 0.1
  · simp only [saddleGamma, ite_eq_left hr]
    exact (firstSaddleC_lt_of_sq (by norm_num) (by norm_num) (by norm_num)).le
  · simp only [saddleGamma, ite_eq_right hr]
    exact (firstSaddleC_lt_of_sq (by norm_num) (by norm_num) (by norm_num)).le

/-- Lemma 3.4 with the exact hypotheses and the stated values of C in the error bound. -/
theorem lemma34_paper {n : ℕ} (hn : 6400 ≤ n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (_hscale : 4 * Real.pi ≤ Real.sqrt ((n : ℝ) * r)) :
    |saddleBesselAverage n r - saddleAmplitude n r * Real.cos (saddlePhase n r)| ≤
      saddleAmplitude n r * saddleBesselPaperError (saddleOmega n r) r := by
  have hn' : 0 < n := by omega
  refine (lemma34 hn' hr hr₁).trans (mul_le_mul_of_nonneg_left ?_ (saddleAmplitude_pos hn' hr).le)
  unfold firstSaddleE saddleBesselPaperError
  exact add_le_add (add_le_add (div_le_div_of_nonneg_right (firstSaddleC_le_paper r)
    (saddleOmega_pos hn' hr).le) le_rfl) le_rfl

end DurfeeCCS.Step08