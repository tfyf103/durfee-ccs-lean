module

public import DurfeeCCS.Step10.OuterPreprocessingSwapTerms
public import DurfeeCCS.Step10.OuterFiniteExpansionData
public import DurfeeCCS.Step10.OuterPreprocessingGeom
public import DurfeeCCS.Step10.OuterPreprocessingBudget

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The summed Bessel kernel replacement estimate on page 45. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step10

open Real Finset

/-- The coefficient-weighted sum of the absolute errors incurred on the positive indices
of one triple. -/
def outerTripleKernelSwapWeight (n : ℕ) (h : ℝ) (abj : ℕ × ℕ × ℕ) : ℝ :=
  (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) *
    ∑ d ∈ Icc 1 n.sqrt, exp (h * (d : ℝ)) *
      |clippedTwoColour (outerShiftedIndex n d abj.1 abj.2.1 abj.2.2) -
        outerBesselKernel (outerTripleRadius n abj.1 abj.2.1 abj.2.2)
          ((d : ℝ) + ((abj.1 : ℝ) + abj.2.1) / 2)|

/-- The global replacement error summed over the triples in the retained radius range. -/
theorem outerKernelSwap_goodTriples_lt {n : ℕ} (hn : 6401 ≤ n) {h : ℝ}
    (hh : 8.76 < h) (hLog : 2 * log (outerY n) ≤ h)
    (hCap : h ≤ 4 * (outerY n) ^ (1 / 3 : ℝ)) :
    (∑ abj ∈ outerGoodTriples n, outerTripleKernelSwapWeight n h abj) <
      0.0208 * outerTransformAmplitude (outerY n) h := by
  let Y := outerY n
  let u := sqrt (h ^ 2 + π ^ 2 / 3)
  let w := exp (-h / 2)
  let q := exp (-(u / (3 * Y)))
  let C := exp ((Y + 1 / (24 * Y)) * u)
  let f := fun abj : ℕ × ℕ × ℕ =>
    (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) * w ^ (abj.1 + abj.2.1) * q ^ abj.2.2
  have hY : 80 ≤ Y := (eighty_lt_outerY hn).le
  have hY₀ : 0 < Y := by linarith
  have hh₀ : 0 < h := by linarith
  have hu : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hw : 0 ≤ w := Real.exp_nonneg _
  have hq₀ : 0 ≤ q := Real.exp_nonneg _
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))
  have hZ : w / (1 - q) < 0.355 := kernelSwap_geomFactor_lt hY hh hLog
  have hN : (n : ℝ) = Y ^ 2 + 1 / 12 := by
    have h := outerY_sq (show 1 ≤ n by omega)
    dsimp only [Y]
    linarith only [h]
  have hSub : outerGoodTriples n ⊆ outerTripleBox n := Finset.filter_subset _ _
  have hP (abj : ℕ × ℕ × ℕ) : (0 : ℝ) ≤ outerMixedCoeff abj.1 abj.2.1 abj.2.2 :=
    by exact_mod_cast outerMixedCoeff_nonneg abj.1 abj.2.1 abj.2.2
  have hF (abj : ℕ × ℕ × ℕ) : 0 ≤ f abj := by
    dsimp only [f]
    exact mul_nonneg (mul_nonneg (hP abj) (pow_nonneg hw _)) (pow_nonneg hq₀ _)
  have hT (abj : ℕ × ℕ × ℕ) (habj : abj ∈ outerGoodTriples n) :
      outerTripleKernelSwapWeight n h abj ≤ (2 * Y * C) * f abj := by
    obtain ⟨a,b,j⟩ := abj
    let y := outerTripleRadius n a b j
    have hyy : 0.9 * Y ≤ y := (mem_filter.mp habj).2
    have hy : 0 < y := (by positivity : 0 < 0.9 * Y).trans_le hyy
    have hyΓ : outerGamma a b j ≤ Y^2 := by
      by_contra! H
      exact hy.ne' (Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr H.le))
    have hySq : y^2 = Y^2 - outerGamma a b j := Real.sq_sqrt (sub_nonneg.mpr hyΓ)
    have hI (d : ℕ) (_ : d ∈ Icc 1 n.sqrt) :
        y ^ 2 - ((d : ℝ) + ((a : ℝ) + b) / 2) ^ 2 = (outerShiftedIndex n d a b j : ℝ) - 1 / 12 :=
      outerShiftedIndex_sq (show 1 ≤ n by omega) hyΓ
    have h := outerSwap_weighted_sum_le hY hN hh₀ hy.le hySq hI
    have h' := mul_le_mul_of_nonneg_left h (hP (a,b,j))
    change _ ≤ (2 * Y * C) * ((outerMixedCoeff a b j : ℝ) * w ^ (a + b) * q ^ j)
    convert h' using 1 <;> simp only [outerTripleKernelSwapWeight, Y, u, w, q, C] <;> ring
  have hGeom := outerMixedGeom_sum_le hq₀ hq hw (hZ.trans (by norm_num)) n
  have hGeo : (2 : ℝ) * (1 - w / (1 - q))⁻¹ ^ 2 ≤ 5 := by
    have hZ₁ : 0.645 ≤ 1 - w / (1 - q) := by linarith only [hZ]
    have hZ₀ : 0 < 1 - w / (1 - q) := by linarith only [hZ]
    calc
      _ ≤ 2 * ((0.645 : ℝ)⁻¹)^2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (inv_nonneg.mpr hZ₀.le) ((inv_le_inv₀ hZ₀ (by norm_num : (0 : ℝ) < 0.645)).mpr hZ₁) 2)
          (by norm_num)
      _ ≤ _ := by norm_num
  have hAmp : 0 < outerTransformAmplitude Y h := by unfold outerTransformAmplitude; positivity
  have hBudget : 5 * Y * C < 0.0208 * outerTransformAmplitude Y h :=
    (div_lt_iff₀ hAmp).mp (kernelSwap_budget hY hh hCap)
  calc
    _ ≤ ∑ abj ∈ outerGoodTriples n, (2 * Y * C) * f abj :=
      Finset.sum_le_sum hT
    _ = (2 * Y * C) * ∑ abj ∈ outerGoodTriples n, f abj := by rw [Finset.mul_sum]
    _ ≤ (2 * Y * C) * ∑ abj ∈ outerTripleBox n, f abj :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun abj _ _ => hF abj)) (by positivity)
    _ ≤ (2 * Y * C) * (1 - w / (1 - q))⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left hGeom (by positivity)
    _ ≤ 5 * Y * C := by
      calc
        _ = (2 * (1 - w / (1 - q))⁻¹ ^ 2) * (Y * C) := by ring
        _ ≤ 5 * (Y * C) := mul_le_mul_of_nonneg_right hGeo (by positivity)
        _ = _ := by ring
    _ < _ := hBudget

end DurfeeCCS.Step10
