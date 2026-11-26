module

public import DurfeeCCS.Step09.MidModelLaplace
public import DurfeeCCS.Step09.MidModelParts
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integrating the differentiated series and summing the hyperbolic functions in (52). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Filter Set

def midModelExpTerm (x : ℂ) (k : ℕ) : ℂ := x ^ k / (k.factorial : ℂ)

private theorem hasSum_expTerm (x : ℂ) : HasSum (midModelExpTerm x) (Complex.exp x) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp x

private theorem weighted_expTerm_bound {f : ℕ → ℂ} (hf : ∀ k, ‖f k‖ ≤ ((k : ℝ) + 1) ^ 2)
    (x : ℂ) (k : ℕ) :
    ‖f k * midModelExpTerm x k‖ ≤ (4 * ‖x‖) ^ k / (k.factorial : ℝ) := by
  have hpow (j : ℕ) : j + 1 ≤ 2 ^ j := by
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ]
      omega
  have hr : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by exact_mod_cast hpow k
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ k := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (k : ℝ) + 1) hr 2
    rw [← pow_mul, mul_comm k, pow_mul] at h
    norm_num at h ⊢
    exact h
  rw [midModelExpTerm, norm_mul, norm_div, norm_pow, Complex.norm_natCast, mul_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ((hf k).trans hsq) (by positivity))
    (by positivity)

private theorem summable_weighted_expTerm {f : ℕ → ℂ} (hf : ∀ k, ‖f k‖ ≤ ((k : ℝ) + 1) ^ 2)
    (x : ℂ) : Summable (fun k => f k * midModelExpTerm x k) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial _) (weighted_expTerm_bound hf x)

private theorem tsum_nat_mul_expTerm (x : ℂ) :
    (∑' k : ℕ, (k : ℂ) * midModelExpTerm x k) = x * Complex.exp x := by
  have hs := summable_weighted_expTerm (f := fun k => (k : ℂ)) (fun k => by
    rw [Complex.norm_natCast]
    nlinarith [show (0 : ℝ) ≤ k by positivity]) x
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  have he (k : ℕ) : ((k + 1 : ℕ) : ℂ) * midModelExpTerm x (k + 1) = x * midModelExpTerm x k := by
    rw [midModelExpTerm, midModelExpTerm, pow_succ, Nat.factorial_succ]
    push_cast
    have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  simp_rw [he, tsum_mul_left, (hasSum_expTerm x).tsum_eq]

private theorem tsum_falling_mul_expTerm (x : ℂ) :
    (∑' k : ℕ, ((k : ℂ) * ((k : ℂ) - 1)) * midModelExpTerm x k) = x ^ 2 * Complex.exp x := by
  have hs := summable_weighted_expTerm (f := fun k => (k : ℂ) * ((k : ℂ) - 1)) (fun k => by
    refine (norm_mul_le _ _).trans ?_
    have h : ‖(k : ℂ) - 1‖ ≤ (k : ℝ) + 1 := by
      simpa only [Complex.norm_natCast, norm_one] using norm_sub_le (k : ℂ) (1 : ℂ)
    rw [Complex.norm_natCast, pow_two]
    exact mul_le_mul (by linarith) h (by positivity) (by positivity)) x
  have hs' : Summable (fun k : ℕ =>
      (((k + 1 : ℕ) : ℂ) * (((k + 1 : ℕ) : ℂ) - 1)) * midModelExpTerm x (k + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  rw [hs.tsum_eq_zero_add, hs'.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  have he (k : ℕ) :
      (((k + 1 + 1 : ℕ) : ℂ) * (((k + 1 + 1 : ℕ) : ℂ) - 1)) * midModelExpTerm x (k + 1 + 1) =
        x ^ 2 * midModelExpTerm x k := by
    rw [midModelExpTerm, midModelExpTerm, pow_succ, pow_succ,
      Nat.factorial_succ (k + 1), Nat.factorial_succ k]
    push_cast
    rw [add_sub_cancel_right]
    have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hk' : (k : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  simp_rw [he, tsum_mul_left, (hasSum_expTerm x).tsum_eq]
  norm_num

private theorem coefficient_norm_bound (k : ℕ) : ‖(1 / 4 : ℂ) - (k : ℂ) ^ 2‖ ≤
    ((k : ℝ) + 1) ^ 2 := by
  have h := norm_sub_le (1 / 4 : ℂ) ((k : ℂ) ^ 2)
  norm_num [norm_pow, Complex.norm_natCast] at h
  nlinarith [show (0 : ℝ) ≤ k by positivity]

private theorem hasSum_model_exp (x : ℂ) :
    HasSum (fun k : ℕ => ((1 / 4 : ℂ) - (k : ℂ) ^ 2) * midModelExpTerm x k)
      ((1 / 4 - x - x ^ 2) * Complex.exp x) := by
  have hs₀ := HasSum.mul_left (1 / 4 : ℂ) (hasSum_expTerm x)
  have hs₁ := summable_weighted_expTerm (f := fun k => (k : ℂ)) (fun k => by
    rw [Complex.norm_natCast]
    nlinarith [show (0 : ℝ) ≤ k by positivity]) x
  have hs₂ := summable_weighted_expTerm (f := fun k => (k : ℂ) * ((k : ℂ) - 1)) (fun k => by
    have h := norm_sub_le (k : ℂ) (1 : ℂ)
    simp only [Complex.norm_natCast, norm_one] at h
    rw [norm_mul, Complex.norm_natCast, pow_two]
    exact mul_le_mul (by linarith) h (by positivity) (by positivity)) x
  have h₁ := hs₁.hasSum
  have h₂ := hs₂.hasSum
  rw [tsum_nat_mul_expTerm] at h₁
  rw [tsum_falling_mul_expTerm] at h₂
  have h := (hs₀.sub h₁).sub h₂
  have e : (1 / 4 : ℂ) * exp x - x * exp x - x ^ 2 * exp x =
      (1 / 4 - x - x ^ 2) * exp x := by ring
  rw [e] at h
  exact h.congr_fun (by intro k; ring)

def midModelHsecondTerm (t ρ : ℝ) (k : ℕ) (η : ℝ) : ℂ :=
  (((1 / 4 : ℂ) - (k : ℂ) ^ 2) * midModelExpTerm (midModelK t ρ) k) *
    ((midModelZ η).sqrt / midModelZ η ^ (k + 2))

theorem hasSum_midModelHsecond (t ρ η : ℝ) :
    HasSum (fun k => midModelHsecondTerm t ρ k η) (midModelHsecond t ρ η) := by
  let z := midModelZ η
  let K := midModelK t ρ
  have hz : z ≠ 0 := midModelZ_ne_zero η
  have h := HasSum.mul_right (z.sqrt / z ^ 2) (hasSum_model_exp (K / z))
  have e : (1 / 4 - K / z - (K / z) ^ 2) * exp (K / z) * (z.sqrt / z ^ 2) =
      midModelHsecond t ρ η := by
    unfold midModelHsecond midModelH
    change _ = (z.sqrt * exp (K / z)) / z ^ 2 * _
    ring
  rw [e] at h
  apply h.congr_fun
  intro k
  unfold midModelHsecondTerm midModelExpTerm
  dsimp only [K, z]
  rw [div_pow, pow_add]
  ring

/-- The differentiated expansion may be integrated term by term. -/
theorem hasSum_integral_midModelHsecond (t ρ : ℝ) :
    HasSum (fun k => ∫ η : ℝ, midModelOsc t η * midModelHsecondTerm t ρ k η)
      (∫ η : ℝ, midModelOsc t η * midModelHsecond t ρ η) := by
  let B := fun k : ℕ => (4 * ‖midModelK t ρ‖) ^ k / (k.factorial : ℝ)
  let M := fun k η => B k * midModelDecay (3 / 2) η
  apply MeasureTheory.hasSum_integral_of_dominated_convergence M
  · intro k
    refine ((continuous_midModelOsc t).mul ?_).aestronglyMeasurable
    unfold midModelHsecondTerm
    exact continuous_const.mul (continuous_midHalfKernel k)
  · intro k
    filter_upwards with η
    rw [norm_mul, norm_midModelOsc, one_mul, midModelHsecondTerm, norm_mul,
      norm_midModelSqrt_div_pow]
    have hp : (3 / 2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) - 1 / 2 := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) k]
    exact mul_le_mul (weighted_expTerm_bound coefficient_norm_bound _ _)
      (midModelDecay_mono hp η) (midModelDecay_nonneg _ _) (by unfold B; positivity)
  · filter_upwards with η
    exact (Real.summable_pow_div_factorial _).mul_right (midModelDecay (3 / 2) η)
  · have h := (integrable_midModelDecay (q := 3 / 2) (by norm_num)).const_mul (∑' k, B k)
    convert h using 1
    ext η
    simp only [M, tsum_mul_right]
  · filter_upwards with η
    exact HasSum.mul_left _ (hasSum_midModelHsecond t ρ η)

theorem tsum_midModelHyperbolic (x : ℂ) :
    (∑' k : ℕ, ((2 : ℂ) * (k : ℂ) - 1) * x ^ (2 * k) / ((2 * k).factorial : ℂ)) =
      x * Complex.sinh x - Complex.cosh x := by
  let f := fun k : ℕ => ((2 : ℂ) * (k : ℂ)) *
    (x ^ (2 * k) / ((2 * k).factorial : ℂ))
  let g := fun k : ℕ => x ^ (2 * k) / ((2 * k).factorial : ℂ)
  have he (k : ℕ) : f (k + 1) = x * (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℂ)) := by
    unfold f
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.factorial_succ (2 * k + 1), pow_succ]
    push_cast
    have hk : (2 * (k : ℂ) + 1 + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (2 * k + 1)
    have hf : ((2 * k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
    ring
  have hs := HasSum.mul_left x (Complex.hasSum_sinh x)
  have hf : Summable f := (summable_nat_add_iff 1).mp (hs.summable.congr (fun k => (he k).symm))
  have hcosh : HasSum g (Complex.cosh x) := Complex.hasSum_cosh x
  have hsumf : (∑' k, f k) = x * Complex.sinh x := by
    rw [hf.tsum_eq_zero_add]
    simp_rw [he, hs.tsum_eq]
    simp [f]
  have hh := hf.hasSum.sub hcosh
  rw [hsumf] at hh
  refine ((hh.congr_fun ?_).tsum_eq)
  intro k
  unfold f g
  ring

private theorem midHalfGamma_coeff_collapse (k : ℕ) :
    -(2 * ((1 / 4 : ℂ) - (k : ℂ) ^ 2)) / ((k.factorial : ℂ) * (midHalfGammaCoeff k : ℂ)) =
      ((2 : ℂ) * (k : ℂ) - 1) * (4 : ℂ) ^ k / ((2 * k).factorial : ℂ) := by
  unfold midHalfGammaCoeff
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ (2 * k + 1),
    Nat.factorial_succ (2 * k), Nat.factorial_succ k, pow_succ (4 : ℝ)]
  push_cast
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hk₁ : (2 * (k : ℂ) + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k)
  have hk₂ : (2 * (k : ℂ) + 1 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k + 1)
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hf₂ : ((2 * k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  ring

private theorem integral_midModelHsecondTerm (t ρ : ℝ) (k : ℕ) (ht : 0 < t) :
    (∫ η : ℝ, midModelOsc t η * midModelHsecondTerm t ρ k η) =
      (((1 / 4 : ℂ) - (k : ℂ) ^ 2) * midModelExpTerm (midModelK t ρ) k) *
        (((2 * Real.pi : ℝ) : ℂ) / ((midHalfGammaCoeff k * Real.sqrt Real.pi : ℝ) : ℂ) *
          ((t ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.exp (-(t : ℂ))) := by
  unfold midModelHsecondTerm
  simp_rw [mul_left_comm (midModelOsc t _), integral_const_mul]
  rw [integral_midHalfKernel_fourier k ht]

private theorem midModelIntegrationCoefficient {t : ℝ} (ht : 0 < t) (ρ : ℝ) (k : ℕ) :
    midModelWeight t ρ *
        ((∫ η : ℝ, midModelOsc t η * midModelHsecondTerm t ρ k η) * (midModelD t ^ 2)⁻¹) =
      ((Real.sqrt Real.pi : ℂ) * Complex.exp (-2 * (t : ℂ) * midModelZ ρ) /
          ((t : ℂ) * (Real.sqrt t : ℂ))) *
        (((2 : ℂ) * (k : ℂ) - 1) * (2 * (t : ℂ) * midModelZ ρ) ^ (2 * k) /
          ((2 * k).factorial : ℂ)) := by
  let X : ℂ := 2 * (t : ℂ) * midModelZ ρ
  let K : ℂ := midModelK t ρ
  let A : ℂ := midHalfGammaCoeff k
  let a : ℂ := (1 / 4 : ℂ) - (k : ℂ) ^ 2
  let P : ℂ := Real.sqrt Real.pi
  let T : ℂ := Real.sqrt t
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hP : P ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : T ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  have hA : A ≠ 0 := ofReal_ne_zero.mpr (midHalfGammaCoeff_pos k).ne'
  have hPP : P ^ 2 = (Real.pi : ℂ) := by dsimp [P]; rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hTT : T ^ 2 = (t : ℂ) := by dsimp [T]; rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
  have hw : midModelWeight t ρ * Complex.exp (-(t : ℂ)) = Complex.exp (-X) := by
    rw [midModelWeight, ← exp_add]
    congr 1
    unfold X midModelZ DurfeeCCS.Step08.verticalPoint
    push_cast
    ring
  have htp : ((t ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) = (t : ℂ) ^ k * T := by
    rw [Real.rpow_add ht, Real.rpow_natCast, ← Real.sqrt_eq_rpow, Complex.ofReal_mul,
      Complex.ofReal_pow]
  have hdt : midModelD t ^ 2 = - (t : ℂ) ^ 2 := by
    rw [midModelD, mul_pow, Complex.I_sq, mul_neg_one]
  have hs : T * (midModelD t ^ 2)⁻¹ = -1 / ((t : ℂ) * T) := by
    rw [hdt]
    field_simp [ht', hT]
    rw [hTT]
  have hp : ((2 * Real.pi : ℝ) : ℂ) / ((midHalfGammaCoeff k * Real.sqrt Real.pi : ℝ) : ℂ) =
      2 * P / A := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    change 2 * (Real.pi : ℂ) / (A * P) = _
    rw [← hPP]
    field_simp
  have hx : (4 : ℂ) ^ k * (K ^ k * (t : ℂ) ^ k) = X ^ (2 * k) := by
    rw [pow_mul, ← mul_pow, ← mul_pow]
    congr 1
    unfold K X midModelK
    ring
  rw [integral_midModelHsecondTerm t ρ k ht, hp, htp]
  change midModelWeight t ρ * ((a * (K ^ k / (k.factorial : ℂ))) *
    (2 * P / A * ((t : ℂ) ^ k * T) * exp (-(t : ℂ))) * (midModelD t ^ 2)⁻¹) = _
  calc
    _ = (P * (midModelWeight t ρ * exp (-(t : ℂ)))) *
        (T * (midModelD t ^ 2)⁻¹) *
        (2 * a / ((k.factorial : ℂ) * A)) * (K ^ k * (t : ℂ) ^ k) := by ring
    _ = (P * exp (-X) / ((t : ℂ) * T)) *
        (-(2 * a) / ((k.factorial : ℂ) * A)) * (K ^ k * (t : ℂ) ^ k) := by
      rw [hw, hs]
      ring
    _ = _ := by
      change _ * (-(2 * ((1 / 4 : ℂ) - (k : ℂ) ^ 2)) /
        ((k.factorial : ℂ) * (midHalfGammaCoeff k : ℂ))) * _ = _
      rw [midHalfGamma_coeff_collapse]
      calc
        _ = (P * exp (-X) / ((t : ℂ) * T)) *
          (((2 : ℂ) * (k : ℂ) - 1) * ((4 : ℂ) ^ k * (K ^ k * (t : ℂ) ^ k)) /
            ((2 * k).factorial : ℂ)) := by ring
        _ = _ := by
          rw [hx, show -2 * (t : ℂ) * midModelZ ρ = -X by dsimp [X]; ring]

/-- Equation (52), in its series form. -/
theorem midModelJInfinity_eq_series {t : ℝ} (ht : 0 < t) (ρ : ℝ) :
    midModelJInfinity t ρ =
      ((Real.sqrt Real.pi : ℂ) * Complex.exp (-2 * (t : ℂ) * midModelZ ρ) /
          ((t : ℂ) * (Real.sqrt t : ℂ))) *
        ∑' k : ℕ, ((2 : ℂ) * (k : ℂ) - 1) * (2 * (t : ℂ) * midModelZ ρ) ^ (2 * k) /
          ((2 * k).factorial : ℂ) := by
  have hSum := (HasSum.mul_left (midModelWeight t ρ)
    (HasSum.mul_right (midModelD t ^ 2)⁻¹ (hasSum_integral_midModelHsecond t ρ))).tsum_eq
  simp_rw [midModelIntegrationCoefficient ht ρ, tsum_mul_left] at hSum
  exact hSum.symm

/-- Equation (52), with the hyperbolic series summed exactly. -/
theorem midModelJInfinity_eq {t : ℝ} (ht : 0 < t) (ρ : ℝ) :
    midModelJInfinity t ρ = (Real.sqrt (Real.pi / t) : ℂ) *
      (midModelZ ρ - 1 / (2 * (t : ℂ)) -
        (midModelZ ρ + 1 / (2 * (t : ℂ))) * Complex.exp (-4 * (t : ℂ) * midModelZ ρ)) := by
  let x : ℂ := 2 * (t : ℂ) * midModelZ ρ
  let W : ℂ := midModelZ ρ
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hs : (Real.sqrt (Real.pi / t) : ℂ) = (Real.sqrt Real.pi : ℂ) / (Real.sqrt t : ℂ) := by
    rw [Real.sqrt_div Real.pi_pos.le, Complex.ofReal_div]
  have he : Complex.exp (-x) * Complex.exp x = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have he' : Complex.exp (-x) * Complex.exp (-x) = Complex.exp (-2 * x) := by
    rw [← exp_add]
    congr 1
    ring
  have harg : -2 * x = -4 * (t : ℂ) * W := by unfold x W; ring
  have harg' : -2 * (t : ℂ) * midModelZ ρ = -x := by dsimp [x]; ring
  rw [midModelJInfinity_eq_series ht, tsum_midModelHyperbolic, hs, ← harg, harg']
  change ((Real.sqrt Real.pi : ℂ) * exp (-x) / ((t : ℂ) * (Real.sqrt t : ℂ))) *
    (x * sinh x - cosh x) = _
  calc
    _ = ((Real.sqrt Real.pi : ℂ) / ((t : ℂ) * (Real.sqrt t : ℂ))) *
        (exp (-x) * (x * Complex.sinh x - Complex.cosh x)) := by
      ring
    _ = ((Real.sqrt Real.pi : ℂ) / ((t : ℂ) * (Real.sqrt t : ℂ))) *
        (((x - 1) - (x + 1) * Complex.exp (-2 * x)) / 2) := by
      congr 1
      rw [Complex.sinh, Complex.cosh, ← he']
      linear_combination ((x - 1) / 2) * he
    _ = _ := by
      dsimp only [x, W]
      field_simp

end DurfeeCCS.Step09
