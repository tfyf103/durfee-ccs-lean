module

public import DurfeeCCS.Step10.OuterPreprocessingSwap
public import DurfeeCCS.Step10.OuterPreprocessingExtension

import Mathlib.Tactic.Ring

/-! Applying the absolute replacement estimate to the signed Durfee sum. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step10

open Real Finset

private theorem abs_outerTripleValue_sub_kernelPositive_le (n : ℕ) (h : ℝ)
    (abj : ℕ × ℕ × ℕ) :
    |outerTripleValue n h abj - outerTripleKernelPositive n h abj| ≤
      outerTripleKernelSwapWeight n h abj := by
  obtain ⟨a,b,j⟩ := abj
  let P := (outerMixedCoeff a b j : ℝ)
  let A := fun d : ℕ => clippedTwoColour (outerShiftedIndex n d a b j)
  let B := fun d : ℕ => outerBesselKernel (outerTripleRadius n a b j)
    ((d : ℝ) + ((a : ℝ) + b) / 2)
  let F := fun d : ℕ => (-exp h)^d
  let T := Icc 1 n.sqrt
  have hP : 0 ≤ P := by dsimp only [P]; exact_mod_cast outerMixedCoeff_nonneg a b j
  have hF (d : ℕ) : |F d| = exp (h * (d : ℝ)) := by
    dsimp only [F]
    rw [abs_pow, abs_neg, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    congr 1
    ring
  change |((-1 : ℝ) ^ (a + b) * P) * (∑ d ∈ T, F d * A d) -
      ((-1 : ℝ) ^ (a + b) * P) * (∑ d ∈ T, F d * B d)| ≤
    P * ∑ d ∈ T, exp (h * (d : ℝ)) * |A d - B d|
  rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg hP, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    ← Finset.sum_sub_distrib]
  apply mul_le_mul_of_nonneg_left _ hP
  simp_rw [← mul_sub]
  exact (Finset.abs_sum_le_sum_abs (fun d => F d * (A d - B d)) T).trans_eq
    (by simp_rw [abs_mul, hF])

/-- The signed positive-index Bessel expansion differs from the retained coefficient
expansion by less than `0.0208` times the outer amplitude. -/
theorem abs_outerGoodTriples_values_sub_kernelPositive_lt {n : ℕ} (hn : 6401 ≤ n) {h : ℝ}
    (hh : 8.76 < h) (hLog : 2 * log (outerY n) ≤ h)
    (hCap : h ≤ 4 * (outerY n) ^ (1 / 3 : ℝ)) :
    |(∑ abj ∈ outerGoodTriples n, outerTripleValue n h abj) -
      (∑ abj ∈ outerGoodTriples n, outerTripleKernelPositive n h abj)| <
        0.0208 * outerTransformAmplitude (outerY n) h := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_lt ?_
  exact (Finset.sum_le_sum fun abj _ => abs_outerTripleValue_sub_kernelPositive_le n h abj).trans_lt
    (outerKernelSwap_goodTriples_lt hn hh hLog hCap)

end DurfeeCCS.Step10
