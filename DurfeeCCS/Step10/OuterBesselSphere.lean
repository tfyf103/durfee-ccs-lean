module

public import DurfeeCCS.Step10.OuterBesselKernel
public import DurfeeCCS.Step10.OuterBesselEndpoints
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Termwise proof of the spherical Bessel identity used in (69). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Complex Filter MeasureTheory Set intervalIntegral DurfeeCCS.Step06

private def radialMoment (y : ℝ) (j k : ℕ) : ℝ :=
  ∫ x in -y..y, x ^ (2 * j) * (y ^ 2 - x ^ 2) ^ k

private theorem radialMoment_succ (y : ℝ) (j k : ℕ) :
    (2 * (j : ℝ) + 1) * radialMoment y j (k + 1) =
      2 * ((k : ℝ) + 1) * radialMoment y (j + 1) k := by
  let F := fun x : ℝ => x ^ (2 * j + 1) * (y ^ 2 - x ^ 2) ^ (k + 1)
  have hd (x : ℝ) : HasDerivAt F
      ((2 * (j : ℝ) + 1) * (x ^ (2 * j) * (y ^ 2 - x ^ 2) ^ (k + 1)) -
        2 * ((k : ℝ) + 1) * (x ^ (2 * (j + 1)) * (y ^ 2 - x ^ 2) ^ k)) x := by
    have h₁ := (hasDerivAt_id x).pow (2 * j + 1)
    have h₂ := ((hasDerivAt_id x).pow 2).const_sub (y ^ 2)
    have h := h₁.mul (h₂.pow (k + 1))
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel, Pi.pow_apply, id_eq, mul_one, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 by decide, pow_one]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add x _ 2, pow_succ x (2 * j)]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -y) (b := y)
    (fun x _ => hd x) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  simp only [F, neg_sq, sub_self, zero_pow (Nat.succ_ne_zero k), mul_zero, sub_self] at h
  exact sub_eq_zero.mp h

private theorem radialMoment_formula (y : ℝ) (j k : ℕ) :
    radialMoment y j k =
      2 * y ^ (2 * (j + k) + 1) * 4 ^ k * (k.factorial : ℝ) *
        ((2 * j).factorial : ℝ) * ((j + k).factorial : ℝ) /
        ((j.factorial : ℝ) * ((2 * (j + k) + 1).factorial : ℝ)) := by
  induction k generalizing j with
  | zero =>
    simp only [radialMoment, pow_zero, mul_one, Nat.add_zero, Nat.factorial_zero, Nat.cast_one]
    rw [integral_pow, Nat.factorial_succ (2 * j)]
    have hodd : (-y) ^ (2 * j + 1) = -(y ^ (2 * j + 1)) := by
      rw [pow_succ, pow_succ, pow_mul, pow_mul, neg_sq]
      ring
    rw [hodd]
    push_cast
    field_simp
    ring
  | succ k ih =>
    have h := radialMoment_succ y j k
    rw [ih] at h
    have h0 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
    have he₁ : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    have he₂ : j + 1 + k = j + (k + 1) := by omega
    rw [he₁, he₂, Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (2 * j),
      Nat.factorial_succ j] at h
    rw [Nat.factorial_succ k, pow_succ (4 : ℝ)] at *
    push_cast at *
    have hne₁ : (j.factorial : ℝ) ≠ 0 := by positivity
    have hne₂ : ((2 * (j + (k + 1)) + 1).factorial : ℝ) ≠ 0 := by positivity
    apply (mul_right_inj' h0).1
    rw [h]
    field_simp
    ring

def sphereBesselFactor (y τ x : ℝ) : ℂ :=
  besselI 0 ((τ * Real.sqrt (y ^ 2 - x ^ 2) : ℝ) : ℂ)

private theorem continuous_sphereBesselFactor (y τ : ℝ) :
    Continuous (sphereBesselFactor y τ) := by
  refine (continuous_iff_continuousAt.mpr fun z => (analyticAt_besselI 0 z).continuousAt).comp ?_
  fun_prop

private theorem integral_exp_sphere_eq_cosh (y τ : ℝ) (ζ : ℂ) :
    (∫ x in -y..y, Complex.exp (ζ * (x : ℂ)) * sphereBesselFactor y τ x) =
      ∫ x in -y..y, Complex.cosh (ζ * (x : ℂ)) * sphereBesselFactor y τ x := by
  let f (x : ℝ) := Complex.exp (ζ * (x : ℂ)) * sphereBesselFactor y τ x
  have hc : Continuous f := (by fun_prop : Continuous (fun x : ℝ => Complex.exp (ζ * (x : ℂ)))).mul
    (continuous_sphereBesselFactor y τ)
  have h := intervalIntegral.integral_comp_neg (a := -y) (b := y) f
  rw [neg_neg] at h
  have hg (x : ℝ) : Complex.cosh (ζ * (x : ℂ)) * sphereBesselFactor y τ x =
      (f x + f (-x)) / 2 := by
    unfold f sphereBesselFactor
    rw [Complex.ofReal_neg, mul_neg, neg_sq, Complex.cosh]
    ring
  simp_rw [hg]
  have hi : IntervalIntegrable (fun x => f (-x)) volume (-y) y :=
    (hc.comp continuous_neg).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hc.intervalIntegrable _ _) hi, h]
  change (∫ x in -y..y, f x) = _
  ring

private theorem summable_even_exponential_norm (z : ℂ) :
    Summable (fun j : ℕ => ‖z ^ (2 * j) / ((2 * j).factorial : ℂ)‖) := by
  have h : Function.Injective (fun j : ℕ => 2 * j) := by
    intro a b h
    change 2 * a = 2 * b at h
    omega
  simp only [norm_div, norm_pow, Complex.norm_natCast]
  exact (Real.summable_pow_div_factorial ‖z‖).comp_injective h

set_option maxHeartbeats 500000 in
private theorem sphereBessel_cosh_series {y : ℝ} (hy : 0 ≤ y) (τ : ℝ) (ζ : ℂ) :
    HasSum (fun m : ℕ =>
      2 * (y : ℂ) ^ (2 * m + 1) * (ζ ^ 2 + (τ : ℂ) ^ 2) ^ m / ((2 * m + 1).factorial : ℂ))
      (∫ x in -y..y, Complex.cosh (ζ * (x : ℂ)) * sphereBesselFactor y τ x) := by
  let c (x : ℝ) (j : ℕ) : ℂ := (ζ * (x : ℂ)) ^ (2 * j) / ((2 * j).factorial : ℂ)
  let b (x : ℝ) (k : ℕ) : ℂ := besselITerm 0 k ((τ * Real.sqrt (y ^ 2 - x ^ 2) : ℝ) : ℂ)
  let F (m : ℕ) (x : ℝ) : ℂ := ∑ p ∈ Finset.antidiagonal m, c x p.1 * b x p.2
  let L (j : ℕ) : ℝ := ‖c y j‖
  let R (k : ℕ) : ℝ := ‖besselITerm 0 k ((τ * y : ℝ) : ℂ)‖
  let U (m : ℕ) : ℝ := ∑ p ∈ Finset.antidiagonal m, L p.1 * R p.2
  have hc (x : ℝ) : Summable (fun j => ‖c x j‖) := summable_even_exponential_norm (ζ * (x : ℂ))
  have hb (x : ℝ) : Summable (fun j => ‖b x j‖) :=
    summable_norm_besselITerm 0 ((τ * Real.sqrt (y ^ 2 - x ^ 2) : ℝ) : ℂ)
  have hR : Summable R := summable_norm_besselITerm 0 ((τ * y : ℝ) : ℂ)
  have hL : Summable L := hc y
  have hprod : Summable (fun p : ℕ × ℕ => L p.1 * R p.2) :=
    hL.mul_of_nonneg hR (fun j => norm_nonneg (c y j))
      (fun k => norm_nonneg (besselITerm 0 k ((τ * y : ℝ) : ℂ)))
  have hU : Summable U :=
    summable_sum_mul_antidiagonal_of_summable_mul (f := L) (g := R) hprod
  have hlim (x : ℝ) : HasSum (fun m => F m x)
      (Complex.cosh (ζ * (x : ℂ)) * sphereBesselFactor y τ x) := by
    have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm (hc x) (hb x)).of_norm.hasSum
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hc x) (hb x),
      (Complex.hasSum_cosh _).tsum_eq] at hs
    exact hs
  have hcont (m : ℕ) : Continuous (F m) := by
    refine continuous_finsetSum _ (fun p _ => ?_)
    dsimp [c, b, besselITerm]
    fun_prop
  have hbound (m : ℕ) (x : ℝ) (hx : x ∈ uIoc (-y) y) : ‖F m x‖ ≤ U m := by
    rw [uIoc_of_le (by linarith)] at hx
    have hxy : |x| ≤ y := abs_le.2 ⟨hx.1.le, hx.2⟩
    have hsy : Real.sqrt (y ^ 2 - x ^ 2) ≤ y :=
      (Real.sqrt_le_left hy).2 (sub_le_self _ (sq_nonneg _))
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro p _
    simp only [L, R, c, b, norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, besselITerm, Nat.add_zero, Complex.norm_ofNat,
      abs_of_nonneg hy, abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -y) (b := y) (μ := volume) (F := F)
    (fun m _ => U m) (fun m => (hcont m).aestronglyMeasurable)
    (fun m => Eventually.of_forall (hbound m))
    (Eventually.of_forall (fun _ _ => hU)) intervalIntegrable_const
    (Eventually.of_forall (fun t _ => hlim t))
  refine hsum.congr_fun (fun m => ?_)
  symm
  change (∫ x in -y..y, ∑ p ∈ Finset.antidiagonal m, c x p.1 * b x p.2) = _
  rw [intervalIntegral.integral_finsetSum]
  · have he (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal m) :
      (∫ x in -y..y, c x p.1 * b x p.2) =
        (2 * (y : ℂ) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ)) *
          ((ζ ^ 2) ^ p.1 * ((τ : ℂ) ^ 2) ^ p.2 * (m.choose p.1 : ℂ)) := by
      obtain ⟨j, k⟩ := p
      have hjk : j + k = m := Finset.mem_antidiagonal.mp hp
      have hconst : (∫ x in -y..y, c x j * b x k) =
          ((ζ ^ 2) ^ j / ((2 * j).factorial : ℂ) *
            (((τ : ℂ) ^ 2) / 4) ^ k / (k.factorial : ℂ) ^ 2) * (radialMoment y j k : ℂ) := by
        rw [radialMoment, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith)] at hx
        have hxy : x ^ 2 ≤ y ^ 2 := sq_le_sq.2 (by rw [abs_of_nonneg hy]; exact abs_le.2 hx)
        simp only [c, b, besselITerm, Nat.add_zero, Complex.ofReal_mul, Complex.ofReal_pow,
          Complex.ofReal_sub]
        have hsq : ((Real.sqrt (y ^ 2 - x ^ 2) : ℝ) : ℂ) ^ 2 = (y : ℂ) ^ 2 - (x : ℂ) ^ 2 := by
          exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hxy)
        rw [pow_mul (ζ * (x : ℂ)), mul_pow ζ (x : ℂ) 2, mul_pow,
          pow_mul (_ / 2 : ℂ), div_pow, mul_pow, hsq, pow_mul (x : ℂ)]
        rw [show ((τ : ℂ) ^ 2 * ((y : ℂ) ^ 2 - (x : ℂ) ^ 2) / 2 ^ 2) =
          (((τ : ℂ) ^ 2) / 4) * ((y : ℂ) ^ 2 - (x : ℂ) ^ 2) by ring, mul_pow]
        ring
      rw [hconst, radialMoment_formula, ← hjk, Nat.cast_choose ℂ (Nat.le_add_right j k)]
      simp only [Nat.add_sub_cancel_left]
      push_cast
      rw [div_pow]
      have hfactorial (n : ℕ) : (n.factorial : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      field_simp [hfactorial]
    rw [Finset.sum_congr rfl he, ← Finset.mul_sum]
    rw [(Commute.all (ζ ^ 2) ((τ : ℂ) ^ 2)).add_pow']
    have hcSum : (∑ p ∈ Finset.antidiagonal m, (ζ ^ 2) ^ p.1 *
        ((τ : ℂ) ^ 2) ^ p.2 * (m.choose p.1 : ℂ)) =
        ∑ p ∈ Finset.antidiagonal m, m.choose p.1 • ((ζ ^ 2) ^ p.1 * ((τ : ℂ) ^ 2) ^ p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [nsmul_eq_mul, mul_comm _ ((ζ ^ 2) ^ p.1 * ((τ : ℂ) ^ 2) ^ p.2)]
    rw [hcSum]
    ring
  · intro p _
    dsimp [c, b, besselITerm]
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Spherical identity on the principal branch wherever the square-root denominator is nonzero. -/
theorem sphereBesselIdentity {y : ℝ} (hy : 0 ≤ y) (τ : ℝ) (ζ : ℂ)
    (hz : ζ ^ 2 + (τ : ℂ) ^ 2 ≠ 0) :
    let w := (ζ ^ 2 + (τ : ℂ) ^ 2).sqrt
    (∫ x in -y..y, Complex.exp (ζ * (x : ℂ)) * sphereBesselFactor y τ x) =
      2 * Complex.sinh ((y : ℂ) * w) / w := by
  dsimp only
  rw [integral_exp_sphere_eq_cosh]
  let w := (ζ ^ 2 + (τ : ℂ) ^ 2).sqrt
  have hw : w ^ 2 = ζ ^ 2 + (τ : ℂ) ^ 2 := principalSqrt_sq _
  have hw' : w ≠ 0 := by intro H; rw [H, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hw; exact hz hw.symm
  have h := (((Complex.hasSum_sinh ((y : ℂ) * w)).mul_left 2).mul_right w⁻¹)
  apply (sphereBessel_cosh_series hy τ ζ).unique
  refine h.congr_fun (fun m => ?_)
  rw [mul_pow, pow_succ w, pow_mul, hw]
  field_simp

/-- The degenerate spherical identity evaluates the removable value at the origin. -/
theorem sphereBesselIdentity_zero {y : ℝ} (hy : 0 ≤ y) (τ : ℝ) (ζ : ℂ)
    (hz : ζ ^ 2 + (τ : ℂ) ^ 2 = 0) :
    (∫ x in -y..y, Complex.exp (ζ * (x : ℂ)) * sphereBesselFactor y τ x) =
      2 * (y : ℂ) := by
  rw [integral_exp_sphere_eq_cosh, ← (sphereBessel_cosh_series hy τ ζ).tsum_eq]
  simp only [hz]
  rw [tsum_eq_single 0]
  · norm_num
  · intro m hm
    simp [zero_pow hm]

end DurfeeCCS.Step10
