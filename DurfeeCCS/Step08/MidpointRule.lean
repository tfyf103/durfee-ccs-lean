module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! The midpoint quadrature bound with the integral of the norm of the second derivative. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Filter MeasureTheory Set
open scoped Interval Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem midpoint_integral_parts {f f' f'' : ℝ → E} {a b : ℝ} (c : ℝ)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ uIcc a b, HasDerivAt f' (f'' x) x)
    (hfi : IntervalIntegrable f'' volume a b) :
    (∫ x in a..b, ((x - c) ^ 2 / 2) • f'' x) =
      ((b - c) ^ 2 / 2) • f' b - ((a - c) ^ 2 / 2) • f' a -
        (b - c) • f b + (a - c) • f a + ∫ x in a..b, f x := by
  have hk (x : ℝ) : HasDerivAt (fun y : ℝ => (y - c) ^ 2 / 2) (x - c) x := by
    convert (((hasDerivAt_id x).sub_const c).pow 2).div_const 2 using 1
    · funext y
      simp [sub_eq_add_neg]
    · simp
  have hk' (x : ℝ) : HasDerivAt (fun y : ℝ => y - c) 1 x := (hasDerivAt_id x).sub_const c
  have hl : Continuous (fun x : ℝ => x - c) := by fun_prop
  have hdc : ContinuousOn f' (uIcc a b) := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have h₁ := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun x _ => hk x) hf' (hl.intervalIntegrable a b) hfi
  have h₂ := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun x _ => hk' x) hf intervalIntegrable_const hdc.intervalIntegrable
  simp only [one_smul] at h₂
  rw [h₁, h₂]
  abel

omit [CompleteSpace E] in
private theorem norm_weighted_interval_integral_le {f : ℝ → E} {K : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hK : Continuous K)
    (hbound : ∀ x ∈ Icc a b, 0 ≤ K x ∧ K x ≤ C) :
    ‖∫ x in a..b, K x • f x‖ ≤ C * ∫ x in a..b, ‖f x‖ := by
  have hf' : ContinuousOn f (uIcc a b) := by rwa [uIcc_of_le hab]
  calc
    _ ≤ ∫ x in a..b, ‖K x • f x‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ x in a..b, C * ‖f x‖ := by
      apply intervalIntegral.integral_mono_on hab
        ((hK.continuousOn.smul hf').norm.intervalIntegrable)
        ((continuousOn_const.mul hf'.norm).intervalIntegrable)
      intro x hx
      change ‖K x • f x‖ ≤ C * ‖f x‖
      rw [norm_smul, Real.norm_of_nonneg (hbound x hx).1]
      exact mul_le_mul_of_nonneg_right (hbound x hx).2 (norm_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul C _

/-- The finite-interval midpoint estimate, with exact constant `1/8`. -/
theorem midpoint_rule_interval {f f' f'' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Icc a b)) :
    ‖(b - a) • f ((a + b) / 2) - ∫ x in a..b, f x‖ ≤
      ((b - a) ^ 2 / 8) * ∫ x in a..b, ‖f'' x‖ := by
  let m := (a + b) / 2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hleft : uIcc a m ⊆ Icc a b := by
    rw [uIcc_of_le ham]
    exact Icc_subset_Icc le_rfl hmb
  have hright : uIcc m b ⊆ Icc a b := by
    rw [uIcc_of_le hmb]
    exact Icc_subset_Icc ham le_rfl
  let l : ℝ → ℝ := fun x => (x - a) ^ 2 / 2
  let r : ℝ → ℝ := fun x => (x - b) ^ 2 / 2
  have hl := midpoint_integral_parts a (fun x hx => hf x (hleft hx))
    (fun x hx => hf' x (hleft hx)) ((hc.mono hleft).intervalIntegrable)
  have hr := midpoint_integral_parts b (fun x hx => hf x (hright hx))
    (fun x hx => hf' x (hright hx)) ((hc.mono hright).intervalIntegrable)
  change (∫ x in a..m, l x • f'' x) = _ at hl
  change (∫ x in m..b, r x • f'' x) = _ at hr
  have hfc : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfa : IntervalIntegrable f volume a m := (hfc.mono hleft).intervalIntegrable
  have hfb : IntervalIntegrable f volume m b := (hfc.mono hright).intervalIntegrable
  have hleft_right : (∫ x in a..m, l x • f'' x) + (∫ x in m..b, r x • f'' x) =
      (∫ x in a..b, f x) - (b - a) • f m := by
    have hK : (m - a) ^ 2 / 2 = (m - b) ^ 2 / 2 := by unfold m; ring
    rw [hl, hr, hK]
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, zero_smul, sub_zero,
      add_zero, zero_sub, ← intervalIntegral.integral_add_adjacent_intervals hfa hfb]
    module
  have hLb : ∀ x ∈ Icc a m, 0 ≤ l x ∧ l x ≤ (b - a) ^ 2 / 8 := by
    intro x hx
    have hxm : x - a ≤ (b - a) / 2 := by dsimp [m] at hx; linarith [hx.2]
    dsimp [l]
    constructor
    · positivity
    · nlinarith [pow_le_pow_left₀ (sub_nonneg.mpr hx.1) hxm 2]
  have hRb : ∀ x ∈ Icc m b, 0 ≤ r x ∧ r x ≤ (b - a) ^ 2 / 8 := by
    intro x hx
    have hxm : b - x ≤ (b - a) / 2 := by dsimp [m] at hx; linarith [hx.1]
    dsimp [r]
    constructor
    · positivity
    · nlinarith [pow_le_pow_left₀ (sub_nonneg.mpr hx.2) hxm 2]
  change ‖(b - a) • f m - _‖ ≤ _
  rw [norm_sub_rev, ← hleft_right]
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ ((b - a) ^ 2 / 8) * (∫ x in a..m, ‖f'' x‖) +
        ((b - a) ^ 2 / 8) * (∫ x in m..b, ‖f'' x‖) := by
      exact add_le_add
        (norm_weighted_interval_integral_le ham (hc.mono (Icc_subset_Icc le_rfl hmb))
          (by unfold l; fun_prop) hLb)
        (norm_weighted_interval_integral_le hmb (hc.mono (Icc_subset_Icc ham le_rfl))
          (by unfold r; fun_prop) hRb)
    _ = _ := by
      rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals
        (hc.mono hleft).norm.intervalIntegrable (hc.mono hright).norm.intervalIntegrable]

/-- Equation (42), obtained by summing the finite-cell estimate and passing to infinity. -/
theorem midpoint_rule_Ioi {f f' f'' : ℝ → E} {u : ℝ} (hu : 0 < u)
    (hf : ∀ x ≥ 0, HasDerivAt f (f' x) x)
    (hf' : ∀ x ≥ 0, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Ici 0))
    (hfi : IntegrableOn f (Ioi 0) volume) (hdi : IntegrableOn f'' (Ioi 0) volume)
    (hs : Summable (fun j : ℕ => f (((j : ℝ) + 1 / 2) * u))) :
    ‖(∑' j : ℕ, f (((j : ℝ) + 1 / 2) * u)) - u⁻¹ • (∫ x in Ioi (0 : ℝ), f x)‖ ≤
      (u / 8) * ∫ x in Ioi (0 : ℝ), ‖f'' x‖ := by
  let t : ℕ → ℝ := fun j => j * u
  have ht₀ (j : ℕ) : 0 ≤ t j := by unfold t; positivity
  have ht₁ (j : ℕ) : t j ≤ t (j + 1) := by unfold t; gcongr; omega
  have hsuc (j : ℕ) : t (j + 1) - t j = u := by unfold t; push_cast; ring
  have hmid (j : ℕ) : (t j + t (j + 1)) / 2 = ((j : ℝ) + 1 / 2) * u := by
    unfold t
    push_cast
    ring
  have hseg (j : ℕ) : uIcc (t j) (t (j + 1)) ⊆ Ici 0 := by
    rw [uIcc_of_le (ht₁ j)]
    exact Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr (ht₀ j))
  have hfc : ContinuousOn f (Ici 0) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hF (N : ℕ) :
      ‖u • (∑ j ∈ Finset.range N, f (((j : ℝ) + 1 / 2) * u)) - ∫ x in 0..t N, f x‖ ≤
        (u ^ 2 / 8) * ∫ x in 0..t N, ‖f'' x‖ := by
    have ht : t 0 = 0 := by simp [t]
    rw [← ht, ← intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => (hfc.mono (hseg j)).intervalIntegrable),
      ← intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => (hc.mono (hseg j)).norm.intervalIntegrable), Finset.smul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    have hsub : Icc (t j) (t (j + 1)) ⊆ Ici 0 := by
      simpa only [uIcc_of_le (ht₁ j)] using hseg j
    simpa only [hsuc j, hmid j] using (midpoint_rule_interval (ht₁ j) (fun x hx => hf x (hsub hx))
      (fun x hx => hf' x (hsub hx)) (hc.mono hsub))
  have ht : Tendsto t atTop atTop := by
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hu
  have hlim₁ := ((hs.hasSum.tendsto_sum_nat.const_smul u).sub
    (intervalIntegral_tendsto_integral_Ioi 0 hfi ht)).norm
  have hlim₂ := (intervalIntegral_tendsto_integral_Ioi 0 hdi.norm ht).const_mul (u ^ 2 / 8)
  have h := le_of_tendsto_of_tendsto' hlim₁ hlim₂ hF
  calc
    _ = u⁻¹ * ‖u • (∑' j : ℕ, f (((j : ℝ) + 1 / 2) * u)) - ∫ x in Ioi (0 : ℝ), f x‖ := by
      have he (v : E) : ‖u⁻¹ • v‖ = u⁻¹ * ‖v‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hu.le)]
      rw [← he, smul_sub, smul_smul, inv_mul_cancel₀ hu.ne', one_smul]
    _ ≤ u⁻¹ * ((u ^ 2 / 8) * ∫ x in Ioi (0 : ℝ), ‖f'' x‖) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hu.le)
    _ = _ := by field_simp

end DurfeeCCS.Step08
