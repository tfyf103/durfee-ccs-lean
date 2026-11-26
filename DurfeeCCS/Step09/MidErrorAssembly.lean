module

public import DurfeeCCS.Step09.MidContour
public import DurfeeCCS.Step08.FirstSaddlePhaseSign

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Summing the disjoint parts of the middle saddle contour. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step08

theorem hasSum_mid_nonprincipal {f : ℤ → ℂ} {s : ℂ} (hs : HasSum f s) :
    HasSum (fun p : ℤ => if p = 0 ∨ p = (-1 : ℤ) then 0 else f p) (s-f 0-f (-1)) := by
  have h₀ := hasSum_ite_eq (0 : ℤ) (f 0)
  have h₁ := hasSum_ite_eq (-1 : ℤ) (f (-1))
  convert (hs.sub h₀).sub h₁ using 1
  funext p
  by_cases hp : p = 0
  · subst p
    simp
  by_cases hp' : p = -1
  · subst p
    simp
  · simp [hp,hp']

theorem norm_mid_nonprincipal_le {f : ℤ → ℂ} {g : ℤ → ℝ} {s : ℂ}
    (hf : HasSum f s) (hg : Summable g) (h : ∀ p, ‖f p‖ ≤ g p) :
    ‖s - f 0 - f (-1)‖ ≤ ∑' p : ℤ, if p = 0 ∨ p = (-1 : ℤ) then 0 else g p := by
  let G := fun p : ℤ => if p = 0 ∨ p = (-1 : ℤ) then 0 else g p
  let F := fun p : ℤ => if p = 0 ∨ p = (-1 : ℤ) then 0 else f p
  have hp (p : ℤ) : 0 ≤ g p := (norm_nonneg _).trans (h p)
  have hG : Summable G := hg.of_nonneg_of_le (fun p => by unfold G; split <;> simp [hp]) (fun p => by
    unfold G
    split <;> simp [hp])
  have hFG (p : ℤ) : ‖F p‖ ≤ G p := by
    dsimp only [F,G]
    split_ifs <;> simp [h p]
  have hF : Summable (fun p => ‖F p‖) := hG.of_nonneg_of_le (fun _ => norm_nonneg _) hFG
  rw [← (hasSum_mid_nonprincipal hf).tsum_eq]
  exact (norm_tsum_le_tsum_norm hF).trans (hF.tsum_le_tsum hFG hG)

theorem midRelativeError_of_bounds {n : ℕ} {r : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hU : 8 * midU n r ≤ Real.pi)
    (hmain : ‖midContribution n r 0 0 8 + midContribution n r (-1) (-8) 0 -
      (firstSaddlePrediction n r : ℂ)‖ < 0.88 * saddleAmplitude n r)
    (hminor : ‖midOuterContribution n r‖ < 0.05 * saddleAmplitude n r)
    (hother : ‖midCentralContribution n r -
      (midContribution n r 0 0 8 + midContribution n r (-1) (-8) 0)‖ <
        0.002 * saddleAmplitude n r) :
    |durfeeNegativeValue n r - firstSaddlePrediction n r| < 0.95 * saddleAmplitude n r := by
  let M := saddleAmplitude n r
  let P := (firstSaddlePrediction n r : ℂ)
  let C := midCentralContribution n r
  let B := midOuterContribution n r
  let A := midContribution n r 0 0 8 + midContribution n r (-1) (-8) 0
  have hM := saddleAmplitude_pos hn hr
  have heq := durfeeNegativeValue_eq_midContour (saddleU_pos hn hr) hU
  rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, heq]
  change ‖C + B - P‖ < _
  have h : ‖C + B - P‖ ≤ ‖A-P‖ + ‖C-A‖ + ‖B‖ := by
    rw [show C + B - P = ((A-P)+(C-A))+B by abel]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  linarith only [h,hmain,hminor,hother,hM]

/-- The middle and first saddle estimates share the actual endpoint at radius one. -/
theorem midSaddle_radius_one {n : ℕ} (hn : 6400 ≤ n) :
    |durfeeNegativeValue n 1 - firstSaddlePrediction n 1| <
      0.9 * saddleAmplitude n 1 := by
  have hn' : (6400 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (80 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt hn'
    have h80 : Real.sqrt (6400 : ℝ) = 80 := by
      rw [show (6400 : ℝ) = 80^2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    rwa [h80] at h
  have hscale : 4*Real.pi ≤ Real.sqrt ((n : ℝ)*1) := by
    rw [mul_one]
    linarith only [Real.pi_lt_d2,hs]
  simpa only [firstSaddlePrediction, show (0.9 : ℝ) = 9/10 by norm_num] using
    proposition35 hn (by norm_num) le_rfl hscale

theorem midSaddle_sign_of_relativeError {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (herror : |durfeeNegativeValue n r - firstSaddlePrediction n r| <
      0.95 * saddleAmplitude n r) :
    (Real.cos (saddlePhase n r) = 1 → 0 < durfeeNegativeValue n r) ∧
    (Real.cos (saddlePhase n r) = -1 → durfeeNegativeValue n r < 0) := by
  have hM := saddleAmplitude_pos hn hr
  obtain ⟨h₁,h₂⟩ := abs_lt.mp herror
  constructor <;> intro hcos
  · simpa only [firstSaddlePrediction,hcos,mul_one] using
      (show 0 < durfeeNegativeValue n r by
        rw [firstSaddlePrediction,hcos,mul_one] at h₁
        linarith only [h₁,hM])
  · rw [firstSaddlePrediction,hcos,mul_neg_one] at h₂
    linarith only [h₂,hM]

end DurfeeCCS.Step09
