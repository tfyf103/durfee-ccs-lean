module

public import DurfeeCCS.Step08.NearOriginLaplace
public import DurfeeCCS.Step08.MidpointSinh
public import DurfeeCCS.Step08.MinorArcSeries

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Bounds for the paired logarithm after the minor arcs have been classified. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07

def logScaledMode (r θ u v : ℝ) (k : ℕ) : ℝ :=
  ‖pairedLogMode r θ (verticalPoint u v) k‖ / (r / u)

theorem logScaledMode_le_radius {r r₀ u : ℝ} (hr : 0 < r) (hrle : r ≤ r₀) (hu : 0 < u)
    (θ v : ℝ) (k : ℕ) :
    logScaledMode r θ u v k ≤ 2 * r₀ ^ k / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  have h := norm_pairedLogMode_le_radius hr.le θ (by simpa using hu : 0 < (verticalPoint u v).re) k
  rw [verticalPoint_re] at h
  unfold logScaledMode
  apply (div_le_iff₀ (div_pos hr hu)).mpr
  refine h.trans ?_
  calc
    _ = (2 * r ^ k / ((k + 1 : ℕ) : ℝ) ^ 2) * (r / u) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hr.le hrle _) (by norm_num)) (sq_nonneg _)) (by positivity)

theorem logScaledMode_le_sin {r r₀ u a : ℝ} (hr : 0 < r) (hrle : r ≤ r₀) (hu : 0 < u)
    (ha : 0 < a) (θ v : ℝ) (k : ℕ)
    (hsin : a ≤ |Real.sin ((((k + 1 : ℕ) : ℝ) * v) / 2)|) :
    logScaledMode r θ u v k ≤ (u / a) * (r₀ ^ k / ((k + 1 : ℕ) : ℝ)) := by
  let w : ℂ := ((k + 1 : ℕ) : ℂ) * verticalPoint u v / 2
  have him : w.im = (((k + 1 : ℕ) : ℝ) * v) / 2 := by
    dsimp only [w]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im]
    simp [Complex.mul_im]
  have hs : 2 * a ≤ ‖2 * Complex.sinh w‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [norm_two_mul_sinh_sq, him]
    have h := pow_le_pow_left₀ ha.le hsin 2
    rw [sq_abs] at h
    nlinarith only [h, sq_nonneg (Real.sinh w.re)]
  unfold logScaledMode
  apply (div_le_iff₀ (div_pos hr hu)).mpr
  have hcos := Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * θ)
  rw [pairedLogMode, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine (mul_le_of_le_one_right (norm_nonneg _) hcos).trans ?_
  rw [norm_pairedLogCoeff_eq, abs_of_pos hr]
  calc
    _ ≤ 2 * r ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * (2 * a)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = (u / a) * (r ^ k / ((k + 1 : ℕ) : ℝ)) * (r / u) := by rw [pow_succ]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hr.le hrle _) (by positivity)) (by positivity))
      (by positivity)

theorem summable_logScaledMode {r u : ℝ} (hr₁ : |r| ≤ 1) (hu : 0 < u)
    (θ v : ℝ) : Summable (logScaledMode r θ u v) := by
  have h := (summable_norm_pairedLogMode r θ hr₁
    (by simpa using hu : 0 < (verticalPoint u v).re)).mul_right ((r / u)⁻¹)
  exact h.congr (fun k => (div_eq_mul_inv _ _).symm)

theorem norm_pairedLog_le_logScaledMode {r u : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hu : 0 < u)
    (θ v : ℝ) :
    ‖pairedLog r θ (verticalPoint u v)‖ / (r / u) ≤ ∑' k, logScaledMode r θ u v k := by
  have hζ : 0 < (verticalPoint u v).re := by simpa using hu
  have hr' : |r| ≤ 1 := by rwa [abs_of_pos hr]
  rw [pairedLog_eq_tsum_mode r θ hr' hζ]
  calc
    _ ≤ (∑' k, ‖pairedLogMode r θ (verticalPoint u v) k‖) / (r / u) :=
      div_le_div_of_nonneg_right (norm_tsum_le_tsum_norm (summable_norm_pairedLogMode r θ hr' hζ))
        (by positivity)
    _ = _ := by simp only [logScaledMode, div_eq_mul_inv, tsum_mul_right]

theorem norm_pairedLog_le_seven {r r₀ u M : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀)
    (hr₁ : r₀ ≤ 1) (hu : 0 < u) (θ v : ℝ)
    (hhead : (∑ k ∈ Finset.range 7, logScaledMode r θ u v k) ≤ M) :
    ‖pairedLog r θ (verticalPoint u v)‖ / (r / u) ≤ M + firstSaddleTail r₀ := by
  have hR := hr.le.trans hr₀
  have hs := summable_logScaledMode (by rw [abs_of_pos hr]; linarith) hu θ v
  have htail : Summable (fun k : ℕ => 2 * r₀ ^ (k + 7) / ((k : ℝ) + 8) ^ 2) := by
    let f (k : ℕ) := 2 * r₀ ^ (k + 7) / ((k : ℝ) + 8) ^ 2
    have h2 := (summable_nat_add_iff (f := fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) 8).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide))
    have h2' : Summable (fun k : ℕ => 2 / ((k : ℝ) + 8) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, mul_one_div] using h2.mul_left (2 : ℝ)
    apply h2'.of_nonneg_of_le (fun _ => by positivity)
    intro k
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_one₀ hR hr₁ (n := k + 7)) (by norm_num : (0 : ℝ) ≤ 2)
  have hb (k : ℕ) : logScaledMode r θ u v (k + 7) ≤
      2 * r₀ ^ (k + 7) / ((k : ℝ) + 8) ^ 2 := by
    convert logScaledMode_le_radius hr hr₀ hu θ v (k + 7) using 2
    push_cast
    ring
  refine (norm_pairedLog_le_logScaledMode hr (hr₀.trans hr₁) hu θ v).trans ?_
  rw [← hs.sum_add_tsum_nat_add 7]
  refine add_le_add hhead ?_
  exact ((hs.comp_injective (add_left_injective 7)).tsum_le_tsum hb htail).trans
    (firstSaddleTail_series_le hR hr₁)

theorem norm_pairedLog_off_arcs {r r₀ u : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀) (hr₁ : r₀ ≤ 1)
    (hu : 0 < u) (θ v : ℝ)
    (hs : ∀ k ∈ Finset.range 7,
      0.99 * 0.07 * ((k + 1 : ℕ) : ℝ) / 2 ≤ |Real.sin ((((k + 1 : ℕ) : ℝ) * v) / 2)|) :
    ‖pairedLog r θ (verticalPoint u v)‖ / (r / u) ≤ firstSaddleOffArcs r₀ u := by
  unfold firstSaddleOffArcs
  apply norm_pairedLog_le_seven hr hr₀ hr₁ hu
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  refine (logScaledMode_le_sin hr hr₀ hu (by positivity) θ v k (hs k hk)).trans_eq ?_
  field_simp

theorem norm_pairedLog_zero_arc {r u : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hu : 0 < u) (θ v : ℝ)
    (hs : ∀ k ∈ Finset.range 7,
      0.99 * 8 * u * ((k + 1 : ℕ) : ℝ) ≤ |Real.sin ((((k + 1 : ℕ) : ℝ) * v) / 2)|) :
    ‖pairedLog r θ (verticalPoint u v)‖ / (r / u) ≤ 0.478 := by
  have hm : (∑ k ∈ Finset.range 7, logScaledMode r θ u v k) ≤
      ∑ k ∈ Finset.range 7, 1 / (0.99 * 8 * ((k + 1 : ℕ) : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro k hk
    refine (logScaledMode_le_sin hr hr₁ hu (by positivity) θ v k (hs k hk)).trans_eq ?_
    simp only [one_pow]
    field_simp
  refine (norm_pairedLog_le_seven hr hr₁ le_rfl hu θ v hm).trans ?_
  norm_num [firstSaddleTail, Finset.sum_range_succ]

end DurfeeCCS.Step08
