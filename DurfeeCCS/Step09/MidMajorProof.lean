module

public import DurfeeCCS.Step09.MidMajorAssemble
public import DurfeeCCS.Step09.MidMajorGaussianComparison
public import DurfeeCCS.Step09.MidContourSymmetry
public import DurfeeCCS.Step08.SaddleAssembly

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The principal pair of frequency contributions, Lemma 3.8. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step08
open scoped ComplexConjugate

theorem midMajorMainTerm_add_conj (n : ℕ) (r : ℝ) :
    midMajorMainTerm n r + conj (midMajorMainTerm n r) = (firstSaddlePrediction n r : ℂ) := by
  unfold midMajorMainTerm firstSaddlePrediction
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [map_mul, map_add, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- Lemma 3.8 on the complete radius range including r = 1. -/
theorem lemma38 {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) :
    ‖midContribution n r 0 0 8 + midContribution n r (-1) (-8) 0 -
      (firstSaddlePrediction n r : ℂ)‖ < (0.88 : ℝ) * saddleAmplitude n r := by
  have hn' : 0 < n := by omega
  have hE := midMajor_half_arc_error hn hr hmax
  let D := midContribution n r 0 0 8 - midMajorMainTerm n r
  have he : midContribution n r (-1) (-8) 0 = conj (midContribution n r 0 0 8) := by
    simpa only [neg_zero] using midContribution_neg_one_conj hn' hr 0 8
  have hf : midContribution n r 0 0 8 + midContribution n r (-1) (-8) 0 -
      (firstSaddlePrediction n r : ℂ) = D + conj D := by
    rw [he, ← midMajorMainTerm_add_conj]
    dsimp only [D]
    rw [map_sub]
    ring
  rw [hf]
  exact (norm_add_le D (conj D)).trans_lt (by
    rw [Complex.norm_conj]
    change ‖D‖ < (0.88 : ℝ) * (saddleAmplitude n r / 2) at hE
    linarith only [hE])

end DurfeeCCS.Step09
