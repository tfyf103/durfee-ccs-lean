module

public import DurfeeCCS.Step08.GeometricArcMean
public import DurfeeCCS.Step08.MidpointLogSeries
public import DurfeeCCS.Step08.NearOriginLaplace
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.NumberTheory.ZetaValues

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The angular and vertical squared means on the first saddle. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06

theorem continuous_pairedLogCoeff_vertical (r : ℝ) {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Continuous (fun v => pairedLogCoeff r (verticalPoint u v) n) := by
  unfold pairedLogCoeff
  apply Continuous.div
  · fun_prop
  · unfold verticalPoint
    fun_prop
  · intro v
    have h := re_mul_nat_le_norm_sinh (show 0 ≤ (verticalPoint u v).re by simpa using hu.le) (n + 1)
    rw [verticalPoint_re] at h
    exact mul_ne_zero (by exact_mod_cast (Nat.succ_ne_zero n)) (norm_pos_iff.mp ((show
      0 < ((n + 1 : ℕ) : ℝ) * u by positivity).trans_le h))

theorem continuous_pairedLog_vertical (r : ℝ) (hr : |r| ≤ 1) {u : ℝ} (hu : 0 < u) :
    Continuous (fun p : ℝ × ℝ => pairedLog r p.2 (verticalPoint u p.1)) := by
  simp_rw [pairedLog_eq_tsum_mode r _ hr (show 0 < (verticalPoint u _).re by simpa using hu)]
  apply continuous_tsum (u := fun n : ℕ => 2 / (u * ((n + 1 : ℕ) : ℝ) ^ 2))
  · intro n
    exact ((continuous_pairedLogCoeff_vertical r hu n).comp continuous_fst).mul
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (Real.cos (((n + 1 : ℕ) : ℝ) * p.2) : ℂ)))
  · simpa only [verticalPoint_re] using summable_pairedLog_majorant (verticalPoint u 0)
  · intro n p
    simpa only [verticalPoint_re] using norm_pairedLogMode_le r p.2 hr
      (show 0 < (verticalPoint u p.1).re by simpa using hu) n

theorem angularAverage_pairedLog (r : ℝ) (hr : |r| ≤ 1) {ζ : ℂ} (hζ : 0 < ζ.re) :
    angularAverage (fun θ => pairedLog r θ ζ) = 0 := by
  simp_rw [pairedLog_eq_tsum_mode r _ hr hζ]
  exact angularAverage_cosineSeries _ (summable_norm_pairedLogCoeff r hr hζ)

theorem angularMean_norm_sq_pairedLog (r : ℝ) (hr : |r| ≤ 1) {ζ : ℂ} (hζ : 0 < ζ.re) :
    angularMean (fun θ => ‖pairedLog r θ ζ‖ ^ 2) =
      (1 / 2) * ∑' n : ℕ, ‖pairedLogCoeff r ζ n‖ ^ 2 := by
  simp_rw [pairedLog_eq_tsum_mode r _ hr hζ]
  exact angularMean_norm_sq_cosineSeries _ (summable_norm_pairedLogCoeff r hr hζ)

theorem integral_sq_pairedLogCoeff (r : ℝ) {u : ℝ} (hu : 0 < u) (n : ℕ) :
    angularMean (fun v => ‖pairedLogCoeff r (verticalPoint u v) n‖ ^ 2) =
      2 * r ^ (2 * (n + 1)) / ((((n + 1 : ℕ) : ℝ) ^ 2) * Real.sinh (((n + 1 : ℕ) : ℝ) * u)) := by
  have hrpow : (|r| ^ (n + 1)) ^ 2 = r ^ (2 * (n + 1)) := by
    rw [← pow_mul, Nat.mul_comm (n + 1) 2, pow_mul, sq_abs, ← pow_mul]
  have hfactor (v : ℝ) : ‖pairedLogCoeff r (verticalPoint u v) n‖ ^ 2 =
      (4 * r ^ (2 * (n + 1)) / (((n + 1 : ℕ) : ℝ)^2)) *
        (‖2 * sinh (((n + 1 : ℕ) : ℂ) * verticalPoint u v / 2)‖ ^ 2)⁻¹ := by
    rw [norm_pairedLogCoeff_eq, div_pow, mul_pow, mul_pow, hrpow]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  simp_rw [hfactor]
  rw [angularMean_const_mul]
  change _ * angularMean (fun v => (‖2 * sinh (((n + 1 : ℕ) : ℂ) *
    ((u : ℂ) + (v : ℂ) * I) / 2)‖ ^ 2)⁻¹) = _
  rw [angularMean_inv_norm_sinh_sq (k := n + 1) hu (Nat.succ_ne_zero n)]
  have hs : 0 < Real.sinh (((n + 1 : ℕ) : ℝ) * u) :=
    (show 0 < (((n + 1 : ℕ) : ℝ) * u) by positivity).trans_le (Real.self_le_sinh_iff.mpr (by positivity))
  field_simp
  ring

/-- The exact double squared mean of the logarithm, as used on page 19. -/
theorem double_angularMean_norm_sq_pairedLog (r : ℝ) (hr : |r| ≤ 1) {u : ℝ} (hu : 0 < u) :
    angularMean (fun v => angularMean (fun θ => ‖pairedLog r θ (verticalPoint u v)‖ ^ 2)) =
      ∑' n : ℕ, r ^ (2 * (n + 1)) /
        ((((n + 1 : ℕ) : ℝ) ^ 2) * Real.sinh (((n + 1 : ℕ) : ℝ) * u)) := by
  have hv (v : ℝ) : 0 < (verticalPoint u v).re := by simpa using hu
  simp_rw [angularMean_norm_sq_pairedLog r hr (hv _)]
  rw [angularMean_const_mul]
  have hs := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^4) 1).2
    hasSum_zeta_four.summable
  have hb : Summable (fun n : ℕ => (4 / u ^ 2) / (((n + 1 : ℕ) : ℝ)^4)) := by
    simpa only [mul_one_div] using hs.mul_left (4 / u ^ 2)
  rw [angularMean_tsum_uniform (F := fun n v => ‖pairedLogCoeff r (verticalPoint u v) n‖ ^ 2)
    (fun n => (continuous_pairedLogCoeff_vertical r hu n).norm.pow 2) hb]
  · simp_rw [integral_sq_pairedLogCoeff r hu, mul_div_assoc, tsum_mul_left]
    ring
  · intro n v
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := norm_pairedLogCoeff_le r hr (hv v) n
    rw [verticalPoint_re] at h
    calc
      _ ≤ (2 / (u * (((n + 1 : ℕ) : ℝ) ^ 2))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := by field_simp; ring

theorem double_angularMean_norm_sq_pairedLog_le {r u : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1)
    (hu : 0 < u) :
    angularMean (fun v => angularMean (fun θ => ‖pairedLog r θ (verticalPoint u v)‖ ^ 2)) ≤
      r ^ 2 / (u * (1 - r ^ 2)) := by
  rw [double_angularMean_norm_sq_pairedLog r (by simpa [abs_of_nonneg hr] using hr₁.le) hu]
  have hR : r ^ 2 < 1 := pow_lt_one₀ hr hr₁ (by decide)
  let f (n : ℕ) : ℝ := r ^ (2 * (n + 1)) /
    ((((n + 1 : ℕ) : ℝ) ^ 2) * Real.sinh (((n + 1 : ℕ) : ℝ) * u))
  have hg : Summable (fun n : ℕ => (r ^ 2 / u) * (r ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg _) hR).mul_left _
  have hf (n : ℕ) : 0 ≤ f n := by
    exact div_nonneg (pow_nonneg hr _) (mul_nonneg (sq_nonneg _)
      ((Real.self_le_sinh_iff.mpr (by positivity)).trans' (by positivity)))
  have hb (n : ℕ) : f n ≤ (r ^ 2 / u) * (r ^ 2) ^ n := by
    have hk : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hs : u ≤ Real.sinh (((n + 1 : ℕ) : ℝ) * u) :=
      (le_mul_of_one_le_left hu.le hk).trans (Real.self_le_sinh_iff.mpr (by positivity))
    have hd : u ≤ (((n + 1 : ℕ) : ℝ) ^ 2) * Real.sinh (((n + 1 : ℕ) : ℝ) * u) :=
      hs.trans (le_mul_of_one_le_left (hu.le.trans hs) (by nlinarith only [hk, sq_nonneg (((n + 1 : ℕ) : ℝ) - 1)]))
    unfold f
    calc
      _ ≤ r ^ (2 * (n + 1)) / u := div_le_div_of_nonneg_left (pow_nonneg hr _) hu hd
      _ = _ := by rw [pow_mul, pow_succ]; ring
  have hfs := hg.of_nonneg_of_le hf hb
  change (∑' n, f n) ≤ _
  refine (hfs.tsum_le_tsum hb hg).trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg _) hR]
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  rw [mul_comm u⁻¹]

end DurfeeCCS.Step08
