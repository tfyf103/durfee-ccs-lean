module

public import DurfeeCCS.Step10.OuterFiniteExpansionData
public import DurfeeCCS.Step10.OuterPreprocessingExtensionLattice
public import DurfeeCCS.Step10.OuterPreprocessingBudget
public import DurfeeCCS.Step10.OuterCoeffElementary
import Mathlib.Tactic

/-! The aggregate error from adjoining the nonpositive indices to the outer Bessel sums. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset Step06

/-- The Bessel model for one triple before completing its d-sum to the integer lattice. -/
def outerTripleKernelPositive (n : ℕ) (h : ℝ) (abj : ℕ × ℕ × ℕ) : ℝ :=
  (-1 : ℝ) ^ (abj.1 + abj.2.1) * (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) *
    ∑ d ∈ Icc 1 n.sqrt, (-exp h) ^ d *
      outerBesselKernel (outerTripleRadius n abj.1 abj.2.1 abj.2.2)
        ((d : ℝ) + ((abj.1 : ℝ) + abj.2.1) / 2)

/-- The absolute mass of the terms adjoined for one triple. -/
def outerTripleNegativeMass (n : ℕ) (h : ℝ) (abj : ℕ × ℕ × ℕ) : ℝ :=
  let y := outerTripleRadius n abj.1 abj.2.1 abj.2.2
  let k := abj.1 + abj.2.1
  (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) *
    ∑ d ∈ outerNegativeIndices y k, |outerKernelSummand y h k d|

private theorem outerGoodTriples_card_bound {n : ℕ} (hn : 6401 ≤ n) :
    ((outerGoodTriples n).card : ℝ) ≤ 2 * (outerY n) ^ 6 := by
  let Y := outerY n
  have hcard : (outerGoodTriples n).card ≤ (outerTripleBox n).card := Finset.card_filter_le _ _
  have hc : ((outerGoodTriples n).card : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by
    have h : ((outerTripleBox n).card : ℝ) = ((n : ℝ) + 1) ^ 3 := by
      simp only [outerTripleBox, Finset.card_product, Finset.card_range, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [← h]
    exact_mod_cast hcard
  have hY : 80 < Y := eighty_lt_outerY hn
  have hsq : Y ^ 2 = (n : ℝ) - 1 / 12 := outerY_sq (by omega)
  have hsc : (n : ℝ) + 1 ≤ 1.01 * Y ^ 2 := by nlinarith
  calc
    _ ≤ ((n : ℝ) + 1) ^ 3 := hc
    _ ≤ (1.01 * Y ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hsc 3
    _ = (1.01 : ℝ) ^ 3 * Y ^ 6 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

private theorem outerTripleNegativeMass_bound {n : ℕ} (hn : 6401 ≤ n) {h : ℝ}
    (hh : 0 ≤ h) {abj : ℕ × ℕ × ℕ} (habj : abj ∈ outerGoodTriples n) :
    outerTripleNegativeMass n h abj ≤
      (2 * outerY n + 1) * (π ^ 3 / 36) * exp (4 * π * outerY n / sqrt 3) := by
  let Y := outerY n
  let y := outerTripleRadius n abj.1 abj.2.1 abj.2.2
  let k := abj.1 + abj.2.1
  have hY : 0 < Y := by linarith [eighty_lt_outerY hn]
  have hy : 0 < y := by
    have h : 0.9 * Y ≤ y := (Finset.mem_filter.mp habj).2
    linarith
  have hyY : y ≤ Y := outerTripleRadius_le _ _ _ _
  have hγ : outerGamma abj.1 abj.2.1 abj.2.2 ≤ Y ^ 2 := by
    have hh := sqrt_pos.mp hy
    linarith
  have hj : (abj.2.2 : ℝ) ≤ Y ^ 2 := by
    have h := outerGamma_lower abj.1 abj.2.1 abj.2.2
    have hk : 0 ≤ (abj.1 : ℝ) + abj.2.1 := by positivity
    linarith
  have hje : (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) ≤ exp (2 * π * Y / sqrt 3) := by
    refine (show (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) ≤ (twoColourPartitionCount abj.2.2 : ℝ)
      by exact_mod_cast outerMixedCoeff_le_twoColour _ _ _).trans
      ((twoColour_exp_bound abj.2.2).trans ?_)
    rw [show 2 * π * Y / sqrt 3 = 2 * π * (Y / sqrt 3) by ring]
    apply exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hh : (abj.2.2 : ℝ) / 3 ≤ Y ^ 2 / 3 := div_le_div_of_nonneg_right hj (by norm_num)
    exact (sqrt_le_sqrt hh).trans_eq (by rw [sqrt_div (by positivity), sqrt_sq hY.le])
  have hsum := outerNegativeIndices_abs_sum_bound hy hyY hh k
  have hsum0 : 0 ≤ ∑ d ∈ outerNegativeIndices y k, |outerKernelSummand y h k d| :=
    Finset.sum_nonneg fun d _ => abs_nonneg _
  unfold outerTripleNegativeMass
  change (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) *
    (∑ d ∈ outerNegativeIndices y k, |outerKernelSummand y h k d|) ≤ _
  calc
    _ ≤ exp (2 * π * Y / sqrt 3) *
        ((2 * Y + 1) * (π ^ 3 / 36) * exp (2 * π * Y / sqrt 3)) :=
      mul_le_mul hje hsum hsum0 (exp_nonneg _)
    _ = _ := by rw [show 4 * π * Y / sqrt 3 = 2 * π * Y / sqrt 3 + 2 * π * Y / sqrt 3 by ring, exp_add]; ring

private theorem outerTripleKernel_sub_pos_abs {n : ℕ} (hn : 6401 ≤ n) (h : ℝ)
    (abj : ℕ × ℕ × ℕ) :
    |outerTripleKernel n h abj - outerTripleKernelPositive n h abj| ≤
      outerTripleNegativeMass n h abj := by
  let y := outerTripleRadius n abj.1 abj.2.1 abj.2.2
  let k := abj.1 + abj.2.1
  let P := (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ)
  have hp : 0 ≤ P := by dsimp only [P]; exact_mod_cast outerMixedCoeff_nonneg _ _ _
  have hy : 0 ≤ y := sqrt_nonneg _
  have hm : y ≤ (n.sqrt : ℝ) + 1 := (outerTripleRadius_le _ _ _ _).trans
    (outerY_lt_sqrtNat_succ (by omega)).le
  have hlat := outerKernel_tsum_sub_pos_eq (h := h) (k := k) hy hm
  have hcast : (k : ℝ) = (abj.1 : ℝ) + (abj.2.1 : ℝ) := by simp [k]
  unfold outerTripleKernel outerTripleKernelPositive outerTripleNegativeMass
  rw [← mul_sub, ← hcast]
  change |((-1 : ℝ) ^ k * P) * _| ≤ P * ∑ d ∈ outerNegativeIndices y k, |outerKernelSummand y h k d|
  rw [hlat, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hp

/-- The total absolute mass of all nonpositive indices added to the good triples. -/
theorem outerNegativeExtension_mass {n : ℕ} (hn : 6401 ≤ n) {h : ℝ} (hh : 0 ≤ h) :
    (∑ abj ∈ outerGoodTriples n, outerTripleNegativeMass n h abj) ≤
      40 * (outerY n) ^ 7 * exp (4 * π * outerY n / sqrt 3) := by
  let Y := outerY n
  have hY : 80 < Y := eighty_lt_outerY hn
  have hπ : π ^ 3 / 36 ≤ (1 : ℝ) := by
    have h := pow_lt_pow_left₀ Real.pi_lt_d2 pi_pos.le (by decide : 3 ≠ 0)
    linarith
  calc
    _ ≤ ∑ _abj ∈ outerGoodTriples n, (2 * Y + 1) * (π ^ 3 / 36) * exp (4 * π * Y / sqrt 3) :=
      Finset.sum_le_sum fun _ hmem => outerTripleNegativeMass_bound hn hh hmem
    _ = ((outerGoodTriples n).card : ℝ) *
        ((2 * Y + 1) * (π ^ 3 / 36) * exp (4 * π * Y / sqrt 3)) := by simp
    _ ≤ (2 * Y ^ 6) * ((3 * Y) * 1 * exp (4 * π * Y / sqrt 3)) := by
      apply mul_le_mul (outerGoodTriples_card_bound hn) _ (by positivity) (by positivity)
      gcongr; linarith
    _ ≤ _ := by
      change _ ≤ 40 * Y ^ 7 * exp (4 * π * Y / sqrt 3)
      rw [mul_one, ← mul_assoc, show (2 * Y ^ 6) * (3 * Y) = 6 * Y ^ 7 by ring]
      apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
      gcongr
      norm_num

/-- The absolute mass of the added nonpositive indices is below the tolerance on page 45. -/
theorem outerNegativeExtension_mass_lt {n : ℕ} (hn : 6401 ≤ n) {h : ℝ}
    (hhLog : 2 * log (outerY n) ≤ h) :
    (∑ abj ∈ outerGoodTriples n, outerTripleNegativeMass n h abj) <
      1e-30 * outerTransformAmplitude (outerY n) h := by
  let Y := outerY n
  have hY : 80 < Y := eighty_lt_outerY hn
  have hY0 : 0 < Y := by linarith
  have hlog := log_pos (show 1 < Y by linarith)
  have hh : 0 < h := (show 0 < 2 * log Y by positivity).trans_le hhLog
  have hamp := outerTransformAmplitude_pos hY0 hh
  exact (outerNegativeExtension_mass hn hh.le).trans_lt
    ((div_lt_iff₀ hamp).mp (negativeExtension_budget hY.le hhLog))

/-- Extending all the good triples to the full shifted lattice costs less than 10⁻³⁰ times the amplitude. -/
theorem outerNegativeExtension_error {n : ℕ} (hn : 6401 ≤ n) {h : ℝ}
    (hhLog : 2 * log (outerY n) ≤ h) :
    |(∑ abj ∈ outerGoodTriples n, outerTripleKernel n h abj) -
      ∑ abj ∈ outerGoodTriples n, outerTripleKernelPositive n h abj| <
        1e-30 * outerTransformAmplitude (outerY n) h := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ abj ∈ outerGoodTriples n, |outerTripleKernel n h abj - outerTripleKernelPositive n h abj| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ abj ∈ outerGoodTriples n, outerTripleNegativeMass n h abj :=
      Finset.sum_le_sum fun abj _ => outerTripleKernel_sub_pos_abs hn h abj
    _ < _ := outerNegativeExtension_mass_lt hn hhLog

end DurfeeCCS.Step10
