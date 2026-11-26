module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact enclosures of elementary functions for the numerical estimates. -/

@[expose] public section

namespace DurfeeCCS.Step07

open Finset

/-- The rational bounds for π used in the outer error table. -/
theorem pi_enclosure :
    (314159265358979 : ℝ) / 10 ^ 14 < Real.pi ∧
      Real.pi < (314159265358980 : ℝ) / 10 ^ 14 := by
  constructor
  · refine lt_trans ?_ Real.pi_gt_d20
    norm_num
  · refine lt_trans Real.pi_lt_d20 ?_
    norm_num

/-- Square a pair of nonnegative endpoints to check a square-root enclosure. -/
theorem sqrt_enclosure {x lo hi : ℝ} (hhi : 0 ≤ hi)
    (hl : lo ^ 2 ≤ x) (hu : x ≤ hi ^ 2) : lo ≤ Real.sqrt x ∧ Real.sqrt x ≤ hi :=
  ⟨Real.le_sqrt_of_sq_le hl, Real.sqrt_le_iff.mpr ⟨hhi, hu⟩⟩

/-- The polynomial with (n) terms starting at degree zero. -/
noncomputable def expTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, x ^ k / (k.factorial : ℝ)

/-- The remainder obtained by bounding the ratios in the Taylor tail by (x/(n+1)). -/
noncomputable def expRemainder (n : ℕ) (x : ℝ) : ℝ :=
  (x ^ n / (n.factorial : ℝ)) / (1 - x / ((n : ℝ) + 1))

theorem expTaylor_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : expTaylor n x ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx n

private theorem exp_term_succ (x : ℝ) (n : ℕ) :
    x ^ (n + 1) / ((n + 1).factorial : ℝ) =
      (x ^ n / (n.factorial : ℝ)) * (x / ((n : ℝ) + 1)) := by
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  field_simp

private theorem exp_tail_term_le {x : ℝ} (hx : 0 ≤ x) (n k : ℕ) :
    x ^ (k + n) / ((k + n).factorial : ℝ) ≤
      (x ^ n / (n.factorial : ℝ)) * (x / ((n : ℝ) + 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + n = k + n + 1 by omega, exp_term_succ, pow_succ, ← mul_assoc]
    refine mul_le_mul ih ?_ (by positivity) (by positivity)
    apply div_le_div_of_nonneg_left hx (by positivity)
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]

/-- Taylor remainder bound for any nonnegative exponent below the next denominator. -/
theorem exp_le_expTaylor_add_remainder {x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hn : x < (n : ℝ) + 1) : Real.exp x ≤ expTaylor n x + expRemainder n x := by
  have hs := NormedSpace.expSeries_div_summable x
  have hq₀ : 0 ≤ x / ((n : ℝ) + 1) := by positivity
  have hq₁ : x / ((n : ℝ) + 1) < 1 := (div_lt_one (by positivity)).2 hn
  have htail := (summable_nat_add_iff n).2 hs
  have hgeo := (summable_geometric_of_lt_one hq₀ hq₁).mul_left (x ^ n / (n.factorial : ℝ))
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  change (∑' k : ℕ, x ^ k / (k.factorial : ℝ)) ≤ expTaylor n x + expRemainder n x
  rw [← hs.sum_add_tsum_nat_add n]
  change expTaylor n x + _ ≤ expTaylor n x + _
  apply add_le_add_right
  calc
    (∑' k : ℕ, x ^ (k + n) / ((k + n).factorial : ℝ)) ≤
        ∑' k : ℕ, (x ^ n / (n.factorial : ℝ)) * (x / ((n : ℝ) + 1)) ^ k :=
      htail.tsum_le_tsum (exp_tail_term_le hx n) hgeo
    _ = expRemainder n x := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁]
      simp only [expRemainder, div_eq_mul_inv]

/-- Use a smaller exponent and a natural power to enclose the exponential. -/
theorem exp_scaled_enclosure {x lo hi : ℝ} {m : ℕ} (hm : 0 < m) (hlo : 0 ≤ lo)
    (hl : lo ≤ Real.exp (x / m)) (hu : Real.exp (x / m) ≤ hi) :
    lo ^ m ≤ Real.exp x ∧ Real.exp x ≤ hi ^ m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have heq : Real.exp (x / m) ^ m = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [← heq]
  exact ⟨pow_le_pow_left₀ hlo hl _, pow_le_pow_left₀ (Real.exp_pos _).le hu _⟩

/-- A positive exponential enclosure bounds its negative exponent by reciprocation. -/
theorem exp_neg_enclosure {x lo hi : ℝ} (hlo : 0 < lo) (hl : lo ≤ Real.exp x)
    (hu : Real.exp x ≤ hi) : hi⁻¹ ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ lo⁻¹ := by
  rw [Real.exp_neg]
  exact ⟨inv_anti₀ (Real.exp_pos _) hu, inv_anti₀ hlo hl⟩

/-- Partial sum of the rapidly converging logarithm series on (x ≥ 1). -/
noncomputable def logTaylor (n : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ k ∈ range n, ((x - 1) / (x + 1)) ^ (2 * k + 1) / (2 * (k : ℝ) + 1)

noncomputable def logRemainder (n : ℕ) (x : ℝ) : ℝ :=
  let z := (x - 1) / (x + 1)
  2 * (z ^ (2 * n + 1) / (1 - z ^ 2))

theorem log_enclosure {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    logTaylor n x ≤ Real.log x ∧ Real.log x ≤ logTaylor n x + logRemainder n x := by
  let z := (x - 1) / (x + 1)
  have hz₀ : 0 ≤ z := div_nonneg (sub_nonneg.mpr hx) (by linarith)
  have hz₁ : z < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have heq : (1 + z) / (1 - z) = x := by
    have hsum : x + 1 ≠ 0 := by linarith
    have hsub : 1 - z ≠ 0 := (sub_pos.mpr hz₁).ne'
    apply (div_eq_iff hsub).2
    dsimp [z]
    field_simp
    ring
  have hl := Real.sum_range_le_log_div hz₀ hz₁ n
  have hu := Real.log_div_le_sum_range_add hz₀ hz₁ n
  rw [heq] at hl hu
  unfold logTaylor logRemainder
  change 2 * (∑ k ∈ range n, z ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) ≤ Real.log x ∧
    Real.log x ≤ 2 * (∑ k ∈ range n, z ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) +
      2 * (z ^ (2 * n + 1) / (1 - z ^ 2))
  exact ⟨by linarith, by linarith⟩

/-- For (0<x≤1), apply the logarithm enclosure to the reciprocal. -/
theorem log_enclosure_of_le_one {x : ℝ} (hx : 0 < x) (h1 : x ≤ 1) (n : ℕ) :
    -(logTaylor n x⁻¹ + logRemainder n x⁻¹) ≤ Real.log x ∧
      Real.log x ≤ -logTaylor n x⁻¹ := by
  have h := log_enclosure ((one_le_inv₀ hx).mpr h1) n
  rw [Real.log_inv] at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- A power times an exponential decays beyond the cutoff where (q≤bm). -/
theorem antitoneOn_rpow_mul_exp_neg {q b m : ℝ} (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hm : 0 < m) (hcut : q ≤ b * m) :
    AntitoneOn (fun t : ℝ => t ^ q * Real.exp (-b * t)) (Set.Ici m) := by
  intro x hx y _ hxy
  have hx₀ := hm.trans_le hx
  have hy₀ := hx₀.trans_le hxy
  have hlog := Real.log_le_sub_one_of_pos (div_pos hy₀ hx₀)
  rw [Real.log_div hy₀.ne' hx₀.ne', div_sub_one hx₀.ne'] at hlog
  have hqbx := hcut.trans (mul_le_mul_of_nonneg_left hx hb)
  have hdiff : q * (Real.log y - Real.log x) ≤ b * (y - x) := by
    calc
      _ ≤ q * ((y - x) / x) := mul_le_mul_of_nonneg_left hlog hq
      _ ≤ (b * x) * ((y - x) / x) :=
        mul_le_mul_of_nonneg_right hqbx (div_nonneg (sub_nonneg.mpr hxy) hx₀.le)
      _ = _ := by field_simp
  change y ^ q * Real.exp (-b * y) ≤ x ^ q * Real.exp (-b * x)
  rw [Real.rpow_def_of_pos hy₀, Real.rpow_def_of_pos hx₀, ← Real.exp_add, ← Real.exp_add,
    Real.exp_le_exp]
  nlinarith

theorem antitoneOn_pow_mul_exp_neg (q : ℕ) {b m : ℝ} (hb : 0 ≤ b)
    (hm : 0 < m) (hcut : (q : ℝ) ≤ b * m) :
    AntitoneOn (fun t : ℝ => t ^ q * Real.exp (-b * t)) (Set.Ici m) := by
  simpa only [Real.rpow_natCast] using
    (antitoneOn_rpow_mul_exp_neg (Nat.cast_nonneg q) hb hm hcut)

end DurfeeCCS.Step07
