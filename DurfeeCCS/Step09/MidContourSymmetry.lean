module

public import DurfeeCCS.Step09.MidPhaseSymmetry
public import DurfeeCCS.Step09.MidMultiplierConj

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Reflection of the two principal frequencies about the real axis. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory DurfeeCCS.Step06 DurfeeCCS.Step08
open scoped ComplexConjugate

theorem midIntegrand_neg_one_conj {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 ≤ r) (η χ : ℝ) :
    midIntegrand n r (-1) (-η) χ = conj (midIntegrand n r 0 η χ) := by
  have hζ : 0 < (midEtaPoint n r η).re := by
    rw [midEtaPoint_re]
    exact saddleU_pos hn (by linarith)
  dsimp only [midIntegrand]
  rw [midEtaPoint_neg_conj, midPhase_conj hr, midMultiplier_neg_one_conj hr hζ]
  simp only [map_mul, map_add, map_div₀, Complex.conj_natCast, ← Complex.exp_conj]

theorem midContribution_neg_one_conj {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 ≤ r) (l h : ℝ) :
    midContribution n r (-1) (-h) (-l) = conj (midContribution n r 0 l h) := by
  let f (η : ℝ) := ∫ χ : ℝ, midIntegrand n r (-1) η χ
  let g (η : ℝ) := ∫ χ : ℝ, midIntegrand n r 0 η χ
  have hf : ∀ η, f (-η) = conj (g η) := by
    intro η
    simp_rw [f, g, midIntegrand_neg_one_conj hn hr η]
    exact integral_conj
  unfold midContribution
  rw [map_mul, Complex.conj_ofReal]
  change _ * (∫ η in -h..-l, f η) = _ * conj (∫ η in l..h, g η)
  rw [← intervalIntegral.integral_comp_neg f]
  simp_rw [hf, intervalIntegral.intervalIntegral_conj]

end DurfeeCCS.Step09
