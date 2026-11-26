module

public import DurfeeCCS.Step10.OuterPreprocessingBudget
public import DurfeeCCS.Step10.OuterFiniteExpansionData
public import DurfeeCCS.Step10.OuterPreprocessingGeom
public import DurfeeCCS.Step10.OuterCoeffElementary

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Discarding the shifted radii below nine tenths of the main radius. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset DurfeeCCS.Step06

private theorem smallRadius_gamma_gt {n a b j : ℕ}
    (hsmall : outerTripleRadius n a b j < 0.9 * outerY n) :
    0.19 * (outerY n) ^ 2 < outerGamma a b j := by
  by_contra! hγ
  have hr : (0.9 * outerY n) ^ 2 ≤ (outerY n) ^ 2 - outerGamma a b j := by nlinarith only [hγ]
  exact hsmall.not_ge (Real.le_sqrt_of_sq_le hr)

private theorem shiftedIndex_complete_square (n d a b j : ℕ) :
    (outerShiftedIndex n d a b j : ℝ) +
      ((d : ℝ) + ((a : ℝ) + b) / 2) ^ 2 = (n : ℝ) - outerGamma a b j := by
  have h := outerGamma_complete_square d a b j
  unfold outerShiftedIndex
  push_cast at h ⊢
  linarith only [h]

private theorem smallRadius_term_bound {n d a b j : ℕ} {h : ℝ} (hn : 0 < n) (hh : 0 < h)
    (hγ : 0.19 * (outerY n) ^ 2 ≤ outerGamma a b j) :
    let X := sqrt (n : ℝ)
    let p := sqrt (h ^ 2 + 4 * π ^ 2 / 3)
    let w := exp (-h / 2)
    let q := exp (-(p / (4 * X)))
    let E := exp (X * p - 0.19 * p * (outerY n) ^ 2 / (4 * X))
    |(-exp h) ^ d * clippedTwoColour (outerShiftedIndex n d a b j)| ≤ E * (w ^ (a + b) * q ^ j) := by
  dsimp only
  let X := sqrt (n : ℝ)
  let p := sqrt (h ^ 2 + 4 * π ^ 2 / 3)
  let t := outerShiftedIndex n d a b j
  let x := (d : ℝ) + ((a : ℝ) + b) / 2
  let γ := outerGamma a b j
  let c := 2 * π / sqrt 3
  let w := exp (-h / 2)
  let q := exp (-(p / (4 * X)))
  let E := exp (X * p - 0.19 * p * (outerY n) ^ 2 / (4 * X))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hX : 0 < X := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hp : 0 < p := by dsimp [p]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hγj : (j : ℝ) ≤ γ := by
    have h := outerGamma_lower a b j
    dsimp only [γ]
    linarith only [h, (by positivity : 0 ≤ ((a : ℝ) + b) / 2)]
  change |(-exp h) ^ d * clippedTwoColour t| ≤ E * (w ^ (a + b) * q ^ j)
  by_cases ht : 0 ≤ t
  · have ht₀ : 0 ≤ (t : ℝ) := by exact_mod_cast ht
    have htNat : (t.toNat : ℝ) = t := by exact_mod_cast Int.toNat_of_nonneg ht
    have hsq : (t : ℝ) + x ^ 2 = (n : ℝ) - γ := shiftedIndex_complete_square n d a b j
    have hN : 0 ≤ (n : ℝ) - γ := hsq ▸ add_nonneg ht₀ (sq_nonneg x)
    have hB : h * x + c * sqrt t ≤ p * sqrt ((n : ℝ) - γ) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      have hp₂ : p ^ 2 = h ^ 2 + c ^ 2 := by
        dsimp [p, c]
        rw [Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt (by norm_num)]
        ring
      have hvSq : (sqrt (t : ℝ)) ^ 2 + x ^ 2 = (n : ℝ) - γ := by rw [Real.sq_sqrt ht₀, hsq]
      rw [mul_pow, hp₂, Real.sq_sqrt hN, ← hvSq]
      nlinarith only [sq_nonneg (h * sqrt (t : ℝ) - c * x)]
    have hConc : sqrt ((n : ℝ) - γ) ≤ X - γ / (2 * X) := by
      let R := sqrt ((n : ℝ) - γ)
      have hR : R ^ 2 = (n : ℝ) - γ := Real.sq_sqrt hN
      have hX₂ : X ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
      change R ≤ X - γ / (2 * X)
      rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le, div_le_iff₀ (by positivity : 0 < 2 * X)]
      nlinarith only [hR, hX₂, sq_nonneg (X - R)]
    have hLoss : 0.19 * p * (outerY n) ^ 2 / (4 * X) + p * j / (4 * X) ≤ p * γ / (2 * X) := by
      change 0.19 * (outerY n) ^ 2 ≤ γ at hγ
      have hp' := mul_le_mul_of_nonneg_left (add_le_add hγ hγj)
        (by positivity : 0 ≤ p / (4 * X))
      field_simp [hX.ne'] at hp' ⊢
      nlinarith only [hp']
    have hExp : h * d + c * sqrt t ≤
        X * p - 0.19 * p * (outerY n) ^ 2 / (4 * X) +
          (-h / 2) * ((a : ℝ) + b) + (-(p / (4 * X))) * j := by
      have hC := hB.trans (mul_le_mul_of_nonneg_left hConc hp.le)
      have hxEq : h * x = h * d + h / 2 * ((a : ℝ) + b) := by dsimp [x]; ring
      rw [hxEq, show p * (X - γ / (2 * X)) = X * p - p * γ / (2 * X) by ring] at hC
      rw [show -(p / (4 * X)) * (j : ℝ) = -(p * j / (4 * X)) by ring,
        show (-h / 2) * ((a : ℝ) + b) = -(h / 2 * ((a : ℝ) + b)) by ring]
      linarith only [hC, hLoss]
    have htExp : 2 * π * sqrt ((t.toNat : ℝ) / 3) = c * sqrt (t : ℝ) := by
      rw [htNat, Real.sqrt_div ht₀]
      dsimp [c]
      ring
    have hnonneg : 0 ≤ (twoColourPartitionCount t.toNat : ℝ) := by
      rw [twoColourPartitionCount_eq_convolution]
      push_cast
      positivity
    rw [clippedTwoColour, ite_eq_left ht, abs_mul, abs_pow, abs_neg, abs_of_pos (exp_pos h),
      abs_of_nonneg hnonneg, ← Real.exp_nat_mul]
    calc
      _ ≤ exp ((d : ℝ) * h) * exp (2 * π * sqrt ((t.toNat : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left (twoColour_exp_bound t.toNat) (exp_nonneg _)
      _ = exp (h * d + c * sqrt t) := by rw [← exp_add, htExp, mul_comm h (d : ℝ)]
      _ ≤ E * (w ^ (a + b) * q ^ j) := by
        dsimp only [E, w, q]
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← exp_add, ← exp_add]
        push_cast
        apply Real.exp_le_exp.mpr
        linarith only [hExp]
  · rw [clippedTwoColour, ite_eq_right ht, mul_zero, abs_zero]
    dsimp [E, w, q]
    positivity

/-- Sum of the absolute values discarded by the small-radius preprocessing, normalized by the
main-mode envelope. -/
theorem smallRadius_sum_error_lt {n : ℕ} {h : ℝ} (hn : 6401 ≤ n) (hh : outerStart n ≤ h)
    (hhCap : h ≤ farThreshold n) :
    (∑ abj ∈ outerTripleBox n \ outerGoodTriples n, |outerTripleValue n h abj|) /
      outerTransformAmplitude (outerY n) h < 0.00004 := by
  let y := outerY n
  let X := sqrt (n : ℝ)
  let p := sqrt (h ^ 2 + 4 * π ^ 2 / 3)
  let w := exp (-h / 2)
  let q := exp (-(p / (4 * X)))
  let E := exp (X * p - 0.19 * p * y ^ 2 / (4 * X))
  let z := outerGeomFactor h (p / (4 * X))
  have hn₀ : 0 < n := by omega
  have hy : 80 ≤ y := (eighty_lt_outerY hn).le
  have hy₀ : 0 < y := by linarith
  have hh₈ : 8.76 < h := (outerStart_gt hn).trans_le hh
  have hh₀ : 0 < h := by linarith
  have hhLog : 2 * log y ≤ h := by rw [← outerStart_eq (by omega : 1 ≤ n)]; exact hh
  have hX : 0 < X := Real.sqrt_pos.mpr (by exact_mod_cast hn₀)
  have hX₂ : X ^ 2 = y ^ 2 + 1 / 12 := by
    change (sqrt (n : ℝ)) ^ 2 = (outerY n) ^ 2 + 1 / 12
    rw [Real.sq_sqrt (by positivity), outerY_sq (by omega)]
    ring
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos hp (by positivity)))
  have hq₀ : 0 < q := Real.exp_pos _
  have hw : 0 < w := Real.exp_pos _
  have hz : z < 0.47 := smallRadius_geomFactor_lt hy hX (outerSqrtRatio_le hy hX₂) hh₈ hhLog
  have hzE : w / (1 - q) = z := rfl
  have hAmp : 0 < outerTransformAmplitude y h := by unfold outerTransformAmplitude; positivity
  have hC (a b j : ℕ) (habj : (a, b, j) ∈ outerTripleBox n \ outerGoodTriples n) :
      |outerTripleValue n h (a, b, j)| ≤
      (X * E) * ((outerMixedCoeff a b j : ℝ) * w ^ (a + b) * q ^ j) := by
    have hbad : outerTripleRadius n a b j < 0.9 * y := by
      have hs := mem_sdiff.mp habj
      by_contra! h
      exact hs.2 (Finset.mem_filter.mpr ⟨hs.1, h⟩)
    have hg := (smallRadius_gamma_gt hbad).le
    have hP : 0 ≤ (outerMixedCoeff a b j : ℝ) := by exact_mod_cast outerMixedCoeff_nonneg a b j
    have hsum :
        (∑ d ∈ Icc 1 n.sqrt,
          |(-exp h) ^ d * clippedTwoColour (outerShiftedIndex n d a b j)|) ≤
          X * (E * (w ^ (a + b) * q ^ j)) := by
      have hm : 0 ≤ E * (w ^ (a + b) * q ^ j) := by dsimp [E, w, q]; positivity
      calc
        _ ≤ ∑ _ ∈ Icc 1 n.sqrt, E * (w ^ (a + b) * q ^ j) :=
          Finset.sum_le_sum (fun d _ => smallRadius_term_bound (d := d) hn₀ hh₀ hg)
        _ = (n.sqrt : ℝ) * (E * (w ^ (a + b) * q ^ j)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.nat_sqrt_le_real_sqrt (a := n)) hm
    unfold outerTripleValue
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hP]
    calc
      _ ≤ (outerMixedCoeff a b j : ℝ) * ∑ d ∈ Icc 1 n.sqrt,
          |(-exp h) ^ d * clippedTwoColour (outerShiftedIndex n d a b j)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hP
      _ ≤ (outerMixedCoeff a b j : ℝ) * (X * (E * (w ^ (a + b) * q ^ j))) :=
        mul_le_mul_of_nonneg_left hsum hP
      _ = _ := by ring
  have hTotal :
      (∑ abj ∈ outerTripleBox n \ outerGoodTriples n, |outerTripleValue n h abj|) ≤
        X / (1 - z) ^ 2 * E := by
    calc
      _ ≤ ∑ abj ∈ outerTripleBox n \ outerGoodTriples n,
          (X * E) * ((outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) *
            w ^ (abj.1 + abj.2.1) * q ^ abj.2.2) := by
        apply Finset.sum_le_sum
        rintro ⟨a, b, j⟩ hmem
        exact hC a b j hmem
      _ ≤ ∑ abj ∈ outerTripleBox n, (X * E) * ((outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) *
          w ^ (abj.1 + abj.2.1) * q ^ abj.2.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg sdiff_subset
        intro ⟨a, b, j⟩ _ _
        have hP : 0 ≤ (outerMixedCoeff a b j : ℝ) := by exact_mod_cast outerMixedCoeff_nonneg a b j
        have hE : 0 < E := Real.exp_pos _
        positivity
      _ ≤ (X * E) * ((1 - z)⁻¹ ^ 2) := by
        rw [← Finset.mul_sum]
        have hGeo := outerMixedGeom_sum_le hq₀.le hq hw.le (by rw [hzE]; linarith only [hz]) n
        rw [hzE] at hGeo
        exact mul_le_mul_of_nonneg_left hGeo (mul_nonneg hX.le (exp_nonneg _))
      _ = _ := by rw [inv_pow]; ring
  exact (div_le_div_of_nonneg_right hTotal hAmp.le).trans_lt
    (smallRadius_budget hy hX hX₂ hh₈ hhLog hhCap)

end DurfeeCCS.Step10
