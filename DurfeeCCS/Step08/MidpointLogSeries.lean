module

public import DurfeeCCS.Step06.PairedProduct
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The absolutely convergent logarithmic Fourier expansion used on the first saddle. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06

/-- Sum of principal logarithms of the two factors in each layer of the product. -/
noncomputable def pairedLog (r θ : ℝ) (ζ : ℂ) : ℂ :=
  ∑' j, (log (1 + pairedTerm r θ ζ j) + log (1 + pairedTerm r (-θ) ζ j))

/-- The coefficient of the cosine of frequency `n+1` in equation (39). -/
noncomputable def pairedLogCoeff (r : ℝ) (ζ : ℂ) (n : ℕ) : ℂ :=
  -2 * (-(r : ℂ) * I) ^ (n + 1) /
    (((n + 1 : ℕ) : ℂ) * (2 * Complex.sinh (((n + 1 : ℕ) : ℂ) * ζ / 2)))

noncomputable def pairedLogMode (r θ : ℝ) (ζ : ℂ) (n : ℕ) : ℂ :=
  pairedLogCoeff r ζ n * Real.cos (((n + 1 : ℕ) : ℝ) * θ)

theorem exp_pairedLog (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    Complex.exp (pairedLog r θ ζ) = pairedProduct r θ ζ :=
  exp_sum_log_pairedProduct r θ hr hζ

theorem two_mul_re_le_norm_two_mul_sinh {z : ℂ} (hz : 0 ≤ z.re) :
    2 * z.re ≤ ‖2 * Complex.sinh z‖ := by
  have hEq : 2 * Complex.sinh z = Complex.exp z - Complex.exp (-z) := by
    rw [Complex.sinh]
    ring
  have hReEq : Real.exp z.re - Real.exp (-z.re) = 2 * Real.sinh z.re := by
    rw [Real.sinh_eq]
    ring
  have h := norm_sub_norm_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, hReEq] at h
  rw [hEq]
  exact (mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr hz) (by norm_num)).trans h

theorem re_mul_nat_le_norm_sinh {ζ : ℂ} (hζ : 0 ≤ ζ.re) (k : ℕ) :
    (k : ℝ) * ζ.re ≤ ‖2 * Complex.sinh ((k : ℂ) * ζ / 2)‖ := by
  have hr : ((k : ℂ) * ζ / 2).re = (k : ℝ) * ζ.re / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
    simp [Complex.mul_re]
  have h := two_mul_re_le_norm_two_mul_sinh (z := (k : ℂ) * ζ / 2) (by rw [hr]; positivity)
  rwa [hr, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at h

theorem norm_pairedLogCoeff_eq (r : ℝ) (ζ : ℂ) (n : ℕ) :
    ‖pairedLogCoeff r ζ n‖ = 2 * |r| ^ (n + 1) /
      (((n + 1 : ℕ) : ℝ) * ‖2 * Complex.sinh (((n + 1 : ℕ) : ℂ) * ζ / 2)‖) := by
  rw [pairedLogCoeff, norm_div, norm_mul, norm_mul, norm_pow, norm_mul, norm_neg, norm_neg,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  norm_num

/-- Bound independent of the angle and of the imaginary part of ζ. -/
theorem norm_pairedLogCoeff_le (r : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) (n : ℕ) :
    ‖pairedLogCoeff r ζ n‖ ≤ 2 / (ζ.re * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hn := re_mul_nat_le_norm_sinh hζ.le (n + 1)
  rw [norm_pairedLogCoeff_eq]
  apply div_le_div₀ (by positivity) (by nlinarith [pow_le_one₀ (n := n + 1) (abs_nonneg r) hr])
    (by positivity)
  calc
    _ = ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * ζ.re) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)

theorem norm_pairedLogMode_le (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) (n : ℕ) :
    ‖pairedLogMode r θ ζ n‖ ≤ 2 / (ζ.re * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hcos := Real.abs_cos_le_one (((n + 1 : ℕ) : ℝ) * θ)
  rw [pairedLogMode, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (norm_nonneg _) hcos).trans (norm_pairedLogCoeff_le r hr hζ n)

theorem summable_pairedLog_majorant (ζ : ℂ) :
    Summable (fun n : ℕ => 2 / (ζ.re * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hp := ((summable_nat_add_iff 1).mpr hs).mul_left (2 / ζ.re)
  refine hp.congr fun n => ?_
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ac_rfl

theorem summable_norm_pairedLogCoeff (r : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    Summable (fun n : ℕ => ‖pairedLogCoeff r ζ n‖) :=
  (summable_pairedLog_majorant ζ).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_pairedLogCoeff_le r hr hζ)

theorem summable_norm_pairedLogMode (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    Summable (fun n : ℕ => ‖pairedLogMode r θ ζ n‖) :=
  (summable_pairedLog_majorant ζ).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_pairedLogMode_le r θ hr hζ)

private noncomputable def logModeKernel (w ζ : ℂ) (j n : ℕ) : ℂ :=
  -(w * Complex.exp (-((j : ℂ) + 1 / 2) * ζ)) ^ (n + 1) / ((n + 1 : ℕ) : ℂ)

private theorem logModeKernel_factor (w ζ : ℂ) (j n : ℕ) :
    logModeKernel w ζ j n =
      (-w ^ (n + 1) * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ζ / 2)) /
        ((n + 1 : ℕ) : ℂ)) *
        (Complex.exp ( -(((n + 1 : ℕ) : ℂ) * ζ))) ^ j := by
  have hExp : (((n + 1 : ℕ) : ℂ) * (-((j : ℂ) + 1 / 2) * ζ)) =
      -(((n + 1 : ℕ) : ℂ) * ζ / 2) + (j : ℂ) * (-(((n + 1 : ℕ) : ℂ) * ζ)) := by ring
  rw [logModeKernel, mul_pow, ← Complex.exp_nat_mul, hExp, Complex.exp_add,
    Complex.exp_nat_mul]
  ring

private theorem logModeKernel_summable {w ζ : ℂ} (hw : ‖w‖ ≤ 1) (hζ : 0 < ζ.re) :
    Summable (fun p : ℕ × ℕ => ‖logModeKernel w ζ p.1 p.2‖) := by
  let q := Real.exp (-ζ.re / 2)
  have hq₀ : 0 ≤ q := Real.exp_nonneg _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := summable_geometric_of_lt_one hq₀ hq₁
  have hb : Summable (fun p : ℕ × ℕ => q ^ p.1 * q ^ p.2) :=
    hs.mul_of_nonneg hs (fun n => pow_nonneg hq₀ n) (fun n => pow_nonneg hq₀ n)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hb
  rintro ⟨j, n⟩
  rw [logModeKernel_factor, norm_mul, norm_div, norm_mul, norm_neg, norm_pow,
    Complex.norm_exp, Complex.norm_natCast, norm_pow, Complex.norm_exp]
  have hhalf : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  simp only [hhalf, Complex.neg_re, Complex.div_ofReal_re]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  calc
    _ ≤ Real.exp (-(((n + 1 : ℕ) : ℝ) * ζ.re / 2)) *
        Real.exp (-(((n + 1 : ℕ) : ℝ) * ζ.re)) ^ j := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      refine (div_le_self (by positivity) hn).trans ?_
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg w) hw)
    _ ≤ q ^ n * q ^ j := by
      apply mul_le_mul
      · dsimp [q]
        rw [← Real.exp_nat_mul]
        exact Real.exp_le_exp.mpr (by push_cast; nlinarith)
      · exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr (by push_cast; nlinarith)) _
      · positivity
      · positivity
    _ = _ := mul_comm _ _

private theorem tsum_logModeKernel (w : ℂ) {ζ : ℂ} (hζ : 0 < ζ.re) (n : ℕ) :
    (∑' j, logModeKernel w ζ j n) =
      -w ^ (n + 1) / (((n + 1 : ℕ) : ℂ) *
        (2 * Complex.sinh (((n + 1 : ℕ) : ℂ) * ζ / 2))) := by
  let v := ((n + 1 : ℕ) : ℂ) * ζ
  have hv : 0 < v.re := by
    dsimp [v]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    positivity
  have hρ : ‖Complex.exp (-v)‖ < 1 := by
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_lt_one_iff]
    linarith
  have hρ' : 1 - Complex.exp (-v) ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    simp [he] at hρ
  have hmul : (2 * Complex.sinh (v / 2)) * Complex.exp (-(v / 2)) =
      1 - Complex.exp (-v) := by
    rw [Complex.sinh, show (2 : ℂ) * ((Complex.exp (v / 2) - Complex.exp (-(v / 2))) / 2) =
      Complex.exp (v / 2) - Complex.exp (-(v / 2)) by ring, sub_mul, ← Complex.exp_add,
      ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    congr 2
    ring
  have hden : (2 * Complex.sinh (v / 2)) ≠ 0 := by
    intro h
    exact hρ' (by simpa [h] using hmul.symm)
  simp_rw [logModeKernel_factor]
  rw [tsum_mul_left]
  change (-w ^ (n + 1) * Complex.exp (-(v / 2)) / ((n + 1 : ℕ) : ℂ)) *
      (∑' j : ℕ, Complex.exp (-v) ^ j) = _
  rw [tsum_geometric_of_norm_lt_one hρ, ← hmul]
  change _ = -w ^ (n + 1) / (((n + 1 : ℕ) : ℂ) * (2 * Complex.sinh (v / 2)))
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hden, Complex.exp_ne_zero]

private theorem log_mode_hasSum (w : ℂ) {ζ : ℂ} (hw : ‖w‖ ≤ 1) (hζ : 0 < ζ.re)
    (j : ℕ) : HasSum (fun n => logModeKernel w ζ j n)
      (Complex.log (1 - w * Complex.exp (-((j : ℂ) + 1 / 2) * ζ))) := by
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hre : (-((j : ℂ) + 1 / 2) * ζ).re < 0 := by
    rw [hhalf]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im,
      add_zero, zero_mul, sub_zero, neg_lt_zero]
    positivity
  have hnorm : ‖w * Complex.exp (-((j : ℂ) + 1 / 2) * ζ)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp]
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) hw).trans_lt (Real.exp_lt_one_iff.mpr hre)
  simpa only [logModeKernel, neg_div, neg_neg, Nat.cast_add, Nat.cast_one] using
    (Complex.hasSum_taylorSeries_neg_log' hnorm).neg

private theorem tsum_singleLog (w : ℂ) {ζ : ℂ} (hw : ‖w‖ ≤ 1) (hζ : 0 < ζ.re) :
    (∑' j : ℕ, Complex.log (1 - w * Complex.exp (-((j : ℂ) + 1 / 2) * ζ))) =
      ∑' n : ℕ, -w ^ (n + 1) / (((n + 1 : ℕ) : ℂ) *
        (2 * Complex.sinh (((n + 1 : ℕ) : ℂ) * ζ / 2))) := by
  have h : Summable (Function.uncurry (logModeKernel w ζ)) :=
    (logModeKernel_summable hw hζ).of_norm
  calc
    _ = ∑' j : ℕ, ∑' n : ℕ, logModeKernel w ζ j n :=
      tsum_congr (fun j => (log_mode_hasSum w hw hζ j).tsum_eq.symm)
    _ = ∑' n : ℕ, ∑' j : ℕ, logModeKernel w ζ j n :=
      (Summable.tsum_comm (f := logModeKernel w ζ) h).symm
    _ = _ := tsum_congr (tsum_logModeKernel w hζ)

private theorem summable_singleLog_modes {w ζ : ℂ} (hw : ‖w‖ ≤ 1) (hζ : 0 < ζ.re) :
    Summable (fun n : ℕ => -w ^ (n + 1) / (((n + 1 : ℕ) : ℂ) *
      (2 * Complex.sinh (((n + 1 : ℕ) : ℂ) * ζ / 2)))) := by
  have h : Summable (fun p : ℕ × ℕ => logModeKernel w ζ p.1 p.2) :=
    (logModeKernel_summable hw hζ).of_norm
  exact h.prod_symm.prod.congr (tsum_logModeKernel w hζ)

private theorem norm_log_angle (r θ : ℝ) : ‖(-(r : ℂ) * I) * Complex.exp (θ * I)‖ = |r| := by
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    Complex.norm_exp]
  simp [Complex.mul_re]

private theorem log_pairedTerm_eq (r θ : ℝ) (ζ : ℂ) (j : ℕ) :
    Complex.log (1 + pairedTerm r θ ζ j) =
      Complex.log (1 - ((-(r : ℂ) * I) * Complex.exp (θ * I)) *
        Complex.exp (-((j : ℂ) + 1 / 2) * ζ)) := by
  rw [pairedTerm, Complex.exp_add]
  ring_nf

private theorem singleLog_modes_add (r θ : ℝ) (ζ : ℂ) (n : ℕ) :
    -((-(r : ℂ) * I) * Complex.exp (θ * I)) ^ (n + 1) /
        (((n + 1 : ℕ) : ℂ) * (2 * Complex.sinh (((n + 1 : ℕ) : ℂ) * ζ / 2))) +
      -((-(r : ℂ) * I) * Complex.exp ((-(θ : ℝ) : ℂ) * I)) ^ (n + 1) /
        (((n + 1 : ℕ) : ℂ) * (2 * Complex.sinh (((n + 1 : ℕ) : ℂ) * ζ / 2))) =
     pairedLogMode r θ ζ n := by
  rw [pairedLogMode, pairedLogCoeff, Complex.ofReal_cos, Complex.cos]
  simp only [mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  rw [show ((n + 1 : ℕ) : ℂ) * (θ * I) = ((n + 1 : ℕ) : ℂ) * θ * I by ring,
    show ((n + 1 : ℕ) : ℂ) * (-↑θ * I) = -(((n + 1 : ℕ) : ℂ) * θ) * I by ring]
  ring

/-- Equation (39), with absolute convergence controlled by a summable majorant. -/
theorem pairedLog_eq_tsum_mode (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    pairedLog r θ ζ = ∑' n, pairedLogMode r θ ζ n := by
  let w : ℝ → ℂ := fun t => (-(r : ℂ) * I) * Complex.exp (t * I)
  have hw (t : ℝ) : ‖w t‖ ≤ 1 := by dsimp only [w]; rwa [norm_log_angle]
  rw [pairedLog, ((summable_norm_log_pairedTerm r θ hr hζ).of_norm).tsum_add
    ((summable_norm_log_pairedTerm r (-θ) hr hζ).of_norm)]
  simp_rw [log_pairedTerm_eq]
  change (∑' j : ℕ, _) + (∑' j : ℕ, _) = _
  rw [tsum_singleLog (w θ) (hw θ) hζ, tsum_singleLog (w (-θ)) (hw (-θ)) hζ]
  rw [← (summable_singleLog_modes (hw θ) hζ).tsum_add (summable_singleLog_modes (hw (-θ)) hζ)]
  apply tsum_congr
  intro n
  simpa only [w, Complex.ofReal_neg] using singleLog_modes_add r θ ζ n

end DurfeeCCS.Step08
