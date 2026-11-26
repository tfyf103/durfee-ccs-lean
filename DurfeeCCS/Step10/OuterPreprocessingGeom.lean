module

public import DurfeeCCS.Step06.GeneratingAnalytic
public import DurfeeCCS.GeneratingFunction
public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Geometric summation of the positive mixed restricted-partition coefficients. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset PowerSeries

private theorem mixedCoeff_nonneg (a b j : ℕ) : 0 ≤ coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) := by
  rw [PowerSeries.coeff_mul]
  simp only [coeff_restrictedPartitionSeries]
  positivity

theorem outerMixedCoeff_geom_sum_le {q : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1) (a b : ℕ)
    (s : Finset ℕ) :
    (∑ j ∈ s, ((coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℝ) * q ^ j) ≤ ((1 - q)⁻¹) ^ (a + b) := by
  have hqNorm : ‖(q : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_nonneg hq₀] using hq
  have hS := Complex.hasSum_re (hasSum_coeff_restrictedMixedSeries hqNorm a b).1
  have hR : HasSum (fun j => ((coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℝ) * q ^ j)
      (((qPochhammer (q : ℂ) (q : ℂ) a)⁻¹ * (qPochhammer (q : ℂ) (q : ℂ) b)⁻¹).re) := by
    refine hS.congr_fun (fun j => ?_)
    rw [← Complex.ofReal_pow, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hg (j : ℕ) : 0 ≤ ((coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℝ) * q ^ j :=
    mul_nonneg (by exact_mod_cast mixedCoeff_nonneg a b j) (pow_nonneg hq₀ j)
  have hNormQ : ‖(q : ℂ)‖ = q := by simp [Complex.norm_real, abs_of_nonneg hq₀]
  calc
    _ ≤ ∑' j, ((coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℝ) * q ^ j :=
      hR.summable.sum_le_tsum s (fun j _ => hg j)
    _ = _ := hR.tsum_eq
    _ ≤ ‖(qPochhammer (q : ℂ) (q : ℂ) a)⁻¹ * (qPochhammer (q : ℂ) (q : ℂ) b)⁻¹‖ :=
      Complex.re_le_norm _
    _ ≤ _ := by
      rw [norm_mul, pow_add]
      have hA := norm_inv_qPochhammer_self_le hqNorm a
      have hB := norm_inv_qPochhammer_self_le hqNorm b
      rw [hNormQ] at hA hB
      exact mul_le_mul hA hB (norm_nonneg _) (by positivity : 0 ≤ ((1 - q)⁻¹) ^ a)

/-- The total mass of a finite coefficient box is bounded by the square of a geometric sum. -/
theorem outerMixedGeom_sum_le {q w : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1)
    (hw : 0 ≤ w) (hz : w / (1 - q) < 1) (n : ℕ) :
    (∑ abj ∈ Finset.range (n + 1) ×ˢ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)),
      ((coeff abj.2.2 (restrictedPartitionSeries abj.1 * restrictedPartitionSeries abj.2.1) : ℤ) : ℝ) * w ^ (abj.1 + abj.2.1) * q ^ abj.2.2) ≤
        (1 - w / (1 - q))⁻¹ ^ 2 := by
  let z := w / (1 - q)
  have hz₀ : 0 ≤ z := div_nonneg hw (sub_nonneg.mpr hq.le)
  have hInner (a b : ℕ) :
      (∑ j ∈ Finset.range (n + 1), ((coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℝ) * w ^ (a + b) * q ^ j) ≤ z ^ a * z ^ b := by
    simp_rw [mul_comm (↑(coeff _ (restrictedPartitionSeries _ * restrictedPartitionSeries _)) : ℝ) (w ^ _), mul_assoc]
    rw [← Finset.mul_sum]
    calc
      _ ≤ w ^ (a + b) * ((1 - q)⁻¹) ^ (a + b) :=
        mul_le_mul_of_nonneg_left (outerMixedCoeff_geom_sum_le hq₀ hq a b _) (pow_nonneg hw _)
      _ = _ := by rw [← mul_pow, ← div_eq_mul_inv, pow_add]
  have hGeom : (∑ j ∈ Finset.range (n + 1), z ^ j) ≤ (1 - z)⁻¹ := by
    have hs := summable_geometric_of_lt_one hz₀ hz
    exact (hs.sum_le_tsum _ (fun j _ => pow_nonneg hz₀ _)).trans_eq (by
      rw [tsum_geometric_of_lt_one hz₀ hz])
  simp_rw [Finset.sum_product]
  calc
    _ ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1), z ^ a * z ^ b :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hInner a b))
    _ = (∑ j ∈ Finset.range (n + 1), z ^ j) ^ 2 := by rw [pow_two, Finset.sum_mul]; simp_rw [Finset.mul_sum]
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => pow_nonneg hz₀ _)) hGeom 2

end DurfeeCCS.Step10
