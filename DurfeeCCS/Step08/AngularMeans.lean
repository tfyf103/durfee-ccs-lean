module

public import DurfeeCCS.Step06.AngleCoefficients
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Angular means, orthogonality, and Parseval with explicit convergence. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex MeasureTheory DurfeeCCS.Step06

/-- Average on the interval used for Fourier coefficient extraction. -/
def angularAverage (f : ℝ → ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ t in -Real.pi..Real.pi, f t

def angularMean (f : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in -Real.pi..Real.pi, f t

theorem angularAverage_const (z : ℂ) : angularAverage (fun _ => z) = z := by
  unfold angularAverage
  rw [intervalIntegral.integral_const]
  have h : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp only [sub_neg_eq_add, ← two_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]

theorem angularAverage_add {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g volume (-Real.pi) Real.pi) :
    angularAverage (fun t => f t + g t) = angularAverage f + angularAverage g := by
  simp only [angularAverage, intervalIntegral.integral_add hf hg, mul_add]

theorem angularAverage_sub {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g volume (-Real.pi) Real.pi) :
    angularAverage (fun t => f t - g t) = angularAverage f - angularAverage g := by
  simp only [angularAverage, intervalIntegral.integral_sub hf hg, mul_sub]

theorem angularAverage_const_mul (z : ℂ) (f : ℝ → ℂ) :
    angularAverage (fun t => z * f t) = z * angularAverage f := by
  unfold angularAverage
  rw [intervalIntegral.integral_const_mul]
  ring

theorem angularAverage_ofReal (f : ℝ → ℝ) :
    angularAverage (fun t => (f t : ℂ)) = (angularMean f : ℂ) := by
  simp [angularAverage, angularMean, intervalIntegral.integral_ofReal]

private theorem angular_period_nonzero : (2 * Real.pi : ℂ) ≠ 0 :=
  mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- Uniform absolute bounds justify termwise integration. -/
theorem hasSum_angular_integral_uniform {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hf : ∀ i, Continuous (F i)) {b : ι → ℝ} (hb : Summable b)
    (hn : ∀ i t, ‖F i t‖ ≤ b i) :
    HasSum (fun i => ∫ t in -Real.pi..Real.pi, F i t)
      (∫ t in -Real.pi..Real.pi, ∑' i, F i t) := by
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (F := F) (f := fun t => ∑' i, F i t) (fun i _ => b i)
    (fun i => (hf i).aestronglyMeasurable)
    (fun i => ae_of_all _ fun t _ => hn i t)
    (ae_of_all _ fun _ _ => hb) intervalIntegrable_const
    (ae_of_all _ fun t _ => (Summable.of_norm
      (hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hn i t))).hasSum)

theorem angularAverage_tsum_uniform {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hf : ∀ i, Continuous (F i)) {b : ι → ℝ} (hb : Summable b)
    (hn : ∀ i t, ‖F i t‖ ≤ b i) :
    angularAverage (fun t => ∑' i, F i t) = ∑' i, angularAverage (F i) := by
  unfold angularAverage
  rw [← (hasSum_angular_integral_uniform hf hb hn).tsum_eq, tsum_mul_left]

theorem angularMean_tsum_uniform {ι : Type*} [Countable ι] {F : ι → ℝ → ℝ}
    (hf : ∀ i, Continuous (F i)) {b : ι → ℝ} (hb : Summable b)
    (hn : ∀ i t, |F i t| ≤ b i) :
    angularMean (fun t => ∑' i, F i t) = ∑' i, angularMean (F i) := by
  apply Complex.ofReal_injective
  rw [← angularAverage_ofReal]
  simp_rw [Complex.ofReal_tsum]
  have h := angularAverage_tsum_uniform (F := fun i t => (F i t : ℂ))
    (fun i => Complex.continuous_ofReal.comp (hf i)) hb
    (fun i t => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hn i t)
  simpa only [angularAverage_ofReal] using h

theorem angularMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    angularMean (fun t => c * f t) = c * angularMean f := by
  unfold angularMean
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Integrate the product of two uniformly absolutely convergent series. -/
theorem integral_mul_tsum_of_orthogonality {ι : Type*} [Countable ι]
    {F G : ι → ℝ → ℂ} (hf : ∀ i, Continuous (F i)) (hg : ∀ i, Continuous (G i))
    {b c : ι → ℝ} (hb : Summable b) (hc : Summable c)
    (hnf : ∀ i t, ‖F i t‖ ≤ b i) (hng : ∀ i t, ‖G i t‖ ≤ c i)
    (d : ι → ℂ) [DecidableEq ι]
    (horth : ∀ i j, (∫ t in -Real.pi..Real.pi, F i t * G j t) = if j = i then d i else 0) :
    (∫ t in -Real.pi..Real.pi, (∑' i, F i t) * (∑' i, G i t)) = ∑' i, d i := by
  let H : ι × ι → ℝ → ℂ := fun ij t => F ij.1 t * G ij.2 t
  have hb₀ i : 0 ≤ b i := (norm_nonneg (F i 0)).trans (hnf i 0)
  have hc₀ i : 0 ≤ c i := (norm_nonneg (G i 0)).trans (hng i 0)
  have hsum := hasSum_angular_integral_uniform (F := H) (fun ij => (hf _).mul (hg _))
    (hb.mul_of_nonneg hc hb₀ hc₀) (fun ij t => by
      dsimp only [H]
      rw [norm_mul]
      exact mul_le_mul (hnf _ t) (hng _ t) (norm_nonneg _) (hb₀ _))
  have hprod (t : ℝ) : (∑' i, F i t) * (∑' j, G j t) = ∑' ij, H ij t := by
    exact tsum_mul_tsum_of_summable_norm
      (hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hnf i t))
      (hc.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hng i t))
  calc
    _ = ∫ t in -Real.pi..Real.pi, ∑' ij, H ij t := by simp_rw [hprod]
    _ = ∑' ij, ∫ t in -Real.pi..Real.pi, H ij t := hsum.tsum_eq.symm
    _ = ∑' i, ∑' j, ∫ t in -Real.pi..Real.pi, H (i, j) t := hsum.summable.tsum_prod
    _ = _ := by simp only [H, horth, tsum_ite_eq]

private theorem integral_cos_integer_mode (k : ℤ) :
    (∫ t in -Real.pi..Real.pi, (Real.cos ((k : ℝ) * t) : ℂ)) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  let f (t : ℝ) : ℂ := Complex.exp ((k : ℂ) * I * (t : ℂ))
  have hcont : Continuous f := by unfold f; fun_prop
  have hre (t : ℝ) : (f t).re = Real.cos ((k : ℝ) * t) := by
    rw [show f t = exp ((((k : ℝ) * t : ℝ) : ℂ) * I) by
      simp only [f, Complex.ofReal_mul, Complex.ofReal_intCast]; ac_rfl]
    exact Complex.exp_ofReal_mul_I_re _
  have hi : (∫ t in -Real.pi..Real.pi, f t).re =
      ∫ t in -Real.pi..Real.pi, (f t).re :=
    (intervalIntegral.intervalIntegral_re (hcont.intervalIntegrable _ _)).symm
  rw [intervalIntegral.integral_ofReal]
  simp_rw [← hre]
  rw [← hi, show (∫ t in -Real.pi..Real.pi, f t) = if k = 0 then _ else _ from
    integral_integer_mode k]
  split_ifs <;> simp [Complex.mul_re]

private theorem integral_cos_modes (i j : ℕ) :
    (∫ t in -Real.pi..Real.pi,
      (Real.cos (((i + 1 : ℕ) : ℝ) * t) : ℂ) * ↑(Real.cos (((j + 1 : ℕ) : ℝ) * t))) =
      if j = i then (Real.pi : ℂ) else 0 := by
  have ht (t : ℝ) :
      (Real.cos (((i + 1 : ℕ) : ℝ) * t) : ℂ) * ↑(Real.cos (((j + 1 : ℕ) : ℝ) * t)) =
        (2 : ℂ)⁻¹ * ((Real.cos (((((i + 1 : ℕ) : ℤ) + ((j + 1 : ℕ) : ℤ) : ℤ) : ℝ) * t) : ℂ) +
          ↑(Real.cos (((((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) : ℤ) : ℝ) * t))) := by
    simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    push_cast
    ring
  simp_rw [ht]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun t : ℝ =>
      (Real.cos ((↑((↑(i + 1) : ℤ) + ↑(j + 1)) : ℝ) * t) : ℂ))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun t : ℝ =>
      (Real.cos ((↑((↑(i + 1) : ℤ) - ↑(j + 1)) : ℝ) * t) : ℂ))).intervalIntegrable _ _)]
  rw [integral_cos_integer_mode, integral_cos_integer_mode]
  have hplus : (i : ℤ) + 1 + ((j : ℤ) + 1) ≠ 0 := by omega
  have hminus : (i : ℤ) - j = 0 ↔ j = i := by omega
  simp [hplus, hminus]

/-- A cosine series with no constant term has zero mean. -/
theorem angularAverage_cosineSeries (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    angularAverage (fun t => ∑' n : ℕ, a n * (Real.cos (((n + 1 : ℕ) : ℝ) * t) : ℂ)) = 0 := by
  rw [angularAverage_tsum_uniform (fun _ => by fun_prop) ha (fun n t => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _))]
  have h (n : ℕ) : angularAverage
      (fun t => a n * (Real.cos (((n + 1 : ℕ) : ℝ) * t) : ℂ)) = 0 := by
    rw [angularAverage_const_mul, angularAverage]
    have hn : (↑(n + 1 : ℕ) : ℤ) ≠ 0 := by omega
    rw [show (∫ t in -Real.pi..Real.pi, (Real.cos (((n + 1 : ℕ) : ℝ) * t) : ℂ)) =
      0 by simpa only [Int.cast_natCast, ite_eq_right hn] using
        integral_cos_integer_mode (↑(n + 1 : ℕ) : ℤ)]
    simp
  simp_rw [h, tsum_zero]

/-- Parseval for the absolutely convergent cosine series. -/
theorem angularMean_norm_sq_cosineSeries (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    angularMean (fun t => ‖∑' n : ℕ, a n * (Real.cos (((n + 1 : ℕ) : ℝ) * t) : ℂ)‖ ^ 2) =
      (1 / 2) * ∑' n : ℕ, ‖a n‖ ^ 2 := by
  let G (n : ℕ) (t : ℝ) := a n * (Real.cos (((n + 1 : ℕ) : ℝ) * t) : ℂ)
  let F (n : ℕ) (t : ℝ) := starRingEnd ℂ (G n t)
  have hg : ∀ n, Continuous (G n) := by intro n; unfold G; fun_prop
  have hf : ∀ n, Continuous (F n) := by intro n; exact Complex.continuous_conj.comp (hg n)
  have hG (n : ℕ) (t : ℝ) : ‖G n t‖ ≤ ‖a n‖ := by
    dsimp only [G]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
  have hF (n : ℕ) (t : ℝ) : ‖F n t‖ ≤ ‖a n‖ := by simpa [F] using hG n t
  have horth (i j : ℕ) : (∫ t in -Real.pi..Real.pi, F i t * G j t) =
      if j = i then (Real.pi : ℂ) * (‖a i‖ ^ 2 : ℝ) else 0 := by
    simp only [F, G, map_mul, Complex.conj_ofReal, mul_mul_mul_comm]
    rw [intervalIntegral.integral_const_mul, integral_cos_modes]
    split_ifs with h
    · subst j
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, mul_comm]
    · simp
  have h := integral_mul_tsum_of_orthogonality hf hg ha ha hF hG _ horth
  have hpoint (t : ℝ) : ((‖∑' i, G i t‖ ^ 2 : ℝ) : ℂ) =
      (∑' i, F i t) * (∑' i, G i t) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, Complex.conj_tsum]
  apply Complex.ofReal_injective
  rw [← angularAverage_ofReal]
  change angularAverage (fun t => ((‖∑' i, G i t‖ ^ 2 : ℝ) : ℂ)) = _
  simp_rw [hpoint]
  unfold angularAverage
  rw [h, tsum_mul_left, ← Complex.ofReal_tsum, Complex.ofReal_mul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

end DurfeeCCS.Step08
