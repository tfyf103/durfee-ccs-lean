module

public import DurfeeCCS.Step07.FirstSaddleArcTable
public import DurfeeCCS.Step08.MidpointLogSeries
public import Mathlib.Analysis.PSeries

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The two truncation bounds in the first-saddle minor-arc table. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex Filter DurfeeCCS.Step07

private theorem inv_sq_shift_summable (a b : ℕ) (ha : 0 < a) :
    Summable (fun k : ℕ => (1 : ℝ) / ((a * k + b : ℕ) : ℝ) ^ 2) :=
  (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).comp_injective
    (fun _ _ h => Nat.eq_of_mul_eq_mul_left ha (Nat.add_right_cancel h))

private theorem tsum_le_of_telescoping {f g : ℕ → ℝ} (hf : Summable f)
    (h : ∀ k, f k ≤ g k - g (k + 1)) (hg : ∀ k, 0 ≤ g k) :
    (∑' k, f k) ≤ g 0 := by
  apply le_of_tendsto hf.hasSum.tendsto_sum_nat
  filter_upwards with n
  calc
    _ ≤ ∑ k ∈ Finset.range n, (g k - g (k + 1)) := Finset.sum_le_sum (fun k _ => h k)
    _ = g 0 - g n := Finset.sum_range_sub' g n
    _ ≤ g 0 := sub_le_self _ (hg n)

private theorem ordinary_tail_at_one_le :
    (∑' k : ℕ, (2 : ℝ) / ((k : ℝ) + 8) ^ 2) ≤ 2 / 7 := by
  have hs := (inv_sq_shift_summable 1 8 (by decide)).mul_left (2 : ℝ)
  refine (tsum_le_of_telescoping (f := fun k => 2 / ((k : ℝ) + 8) ^ 2)
    (g := fun k => 2 / ((k : ℝ) + 7)) ?_ ?_ ?_).trans_eq (by norm_num)
  · simpa [div_eq_mul_inv, Nat.cast_add] using hs
  · intro k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    push_cast
    field_simp
    nlinarith only [hk, sq_nonneg (k : ℝ)]
  · intro k
    positivity

private theorem odd_tail_at_one_le :
    (∑' k : ℕ, (2 : ℝ) / (2 * (k : ℝ) + 33) ^ 2) ≤ 1 / 32 := by
  have hs := (inv_sq_shift_summable 2 33 (by decide)).mul_left (2 : ℝ)
  refine (tsum_le_of_telescoping (f := fun k => 2 / (2 * (k : ℝ) + 33) ^ 2)
    (g := fun k => 1 / (2 * (k : ℝ) + 32)) ?_ ?_ ?_).trans_eq (by norm_num)
  · simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_mul] using hs
  · intro k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    push_cast
    field_simp
    nlinarith only [hk, sq_nonneg (k : ℝ)]
  · intro k
    positivity

theorem firstSaddleTail_series_le {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    (∑' k : ℕ, 2 * r ^ (k + 7) / ((k : ℝ) + 8) ^ 2) ≤ firstSaddleTail r := by
  let f (k : ℕ) := 2 * r ^ (k + 7) / ((k : ℝ) + 8) ^ 2
  have hs : Summable (fun k : ℕ => (2 : ℝ) / ((k : ℝ) + 8) ^ 2) := by
    simpa [div_eq_mul_inv, Nat.cast_add] using (inv_sq_shift_summable 1 8 (by decide)).mul_left (2 : ℝ)
  have hpoint (k : ℕ) : f k ≤ 2 / ((k : ℝ) + 8) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr₁) (by norm_num : (0 : ℝ) ≤ 2)
  have hf : Summable f := hs.of_nonneg_of_le (fun _ => by dsimp [f]; positivity) hpoint
  have hfirst := (hf.tsum_le_tsum hpoint hs).trans ordinary_tail_at_one_le
  change (∑' k, f k) ≤ _
  unfold firstSaddleTail
  split_ifs with h
  · exact hfirst
  · refine le_min hfirst ?_
    have hlt := lt_of_le_of_ne hr₁ h
    have hb := (summable_geometric_of_lt_one hr hlt).mul_left (r ^ 7 / 32)
    have hB (k : ℕ) : f k ≤ r ^ 7 / 32 * r ^ k := by
      calc
        _ ≤ 2 * r ^ (k + 7) / ((8 : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num)
            (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
        _ = _ := by rw [pow_add]; ring
    refine (hf.tsum_le_tsum hB hb).trans_eq ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr hlt]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem firstSaddleOddTail_series_le {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    (∑' k : ℕ, 2 * r ^ (2*k + 32) / (2 * (k : ℝ) + 33) ^ 2) ≤ firstSaddleOddTail r := by
  let f (k : ℕ) := 2 * r ^ (2*k + 32) / (2 * (k : ℝ) + 33) ^ 2
  have hs : Summable (fun k : ℕ => (2 : ℝ) / (2 * (k : ℝ) + 33) ^ 2) := by
    simpa [div_eq_mul_inv, Nat.cast_mul, Nat.cast_add] using (inv_sq_shift_summable 2 33 (by decide)).mul_left (2 : ℝ)
  have hpoint (k : ℕ) : f k ≤ 2 / (2 * (k : ℝ) + 33) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr₁) (by norm_num : (0 : ℝ) ≤ 2)
  have hf : Summable f := hs.of_nonneg_of_le (fun _ => by dsimp [f]; positivity) hpoint
  change (∑' k, f k) ≤ _
  unfold firstSaddleOddTail
  split_ifs with h
  · exact (hf.tsum_le_tsum hpoint hs).trans odd_tail_at_one_le
  · have hlt := lt_of_le_of_ne hr₁ h
    have hsq : r ^ 2 < 1 := pow_lt_one₀ hr hlt (by decide)
    have hb := (summable_geometric_of_lt_one (sq_nonneg r) hsq).mul_left (2 * r ^ 32 / 33 ^ 2)
    have hB (k : ℕ) : f k ≤ (2 * r ^ 32 / 33 ^ 2) * (r ^ 2) ^ k := by
      calc
        _ ≤ 2 * r ^ (2*k + 32) / ((33 : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num)
            (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
        _ = _ := by rw [pow_add, pow_mul]; ring
    refine (hf.tsum_le_tsum hB hb).trans_eq ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg r) hsq]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem norm_pairedLogMode_le_radius {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) {ζ : ℂ}
    (hζ : 0 < ζ.re) (n : ℕ) :
    ‖pairedLogMode r θ ζ n‖ ≤ 2 * r ^ (n + 1) / (ζ.re * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hcos := Real.abs_cos_le_one (((n + 1 : ℕ) : ℝ) * θ)
  rw [pairedLogMode, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine (mul_le_of_le_one_right (norm_nonneg _) hcos).trans ?_
  rw [norm_pairedLogCoeff_eq, abs_of_nonneg hr]
  have h := re_mul_nat_le_norm_sinh hζ.le (n + 1)
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  calc
    _ = ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * ζ.re) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

end DurfeeCCS.Step08
