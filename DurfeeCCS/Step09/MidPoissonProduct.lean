module

public import DurfeeCCS.Step09.MidPhase
public import DurfeeCCS.Step06.DurfeePairedAngle
public import DurfeeCCS.Step08.LogArcMean

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Product rearrangement and uniform bounds for the transformed theta law. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step08

/-- The positive product majorizing the reciprocal of the two paired factors. -/
def pairedEulerLower (u : ℝ) : ℝ :=
  ∏' j : ℕ, (1 - Real.exp (-u / 2) * (Real.exp (-u)) ^ j)

private theorem exp_product_factor_lt_one {u : ℝ} (hu : 0 < u) (j : ℕ) :
    Real.exp (-u / 2) * (Real.exp (-u)) ^ j < 1 := by
  have hs : Real.exp (-u / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact (mul_le_of_le_one_right (Real.exp_nonneg _) (pow_le_one₀ (Real.exp_nonneg _) hq)).trans_lt hs

private theorem summable_exp_product_factor {u : ℝ} (hu : 0 < u) :
    Summable (fun j : ℕ => Real.exp (-u / 2) * (Real.exp (-u)) ^ j) :=
  (summable_geometric_of_lt_one (Real.exp_nonneg _) (Real.exp_lt_one_iff.mpr (by linarith))).mul_left _

theorem pairedEulerLower_pos {u : ℝ} (hu : 0 < u) : 0 < pairedEulerLower u := by
  have hs := summable_exp_product_factor hu
  have hn : ∀ j : ℕ, (1 + -(Real.exp (-u / 2) * (Real.exp (-u)) ^ j)) ≠ 0 := fun j => by
    rw [← sub_eq_add_neg]
    exact (sub_pos.mpr (exp_product_factor_lt_one hu j)).ne'
  have h : pairedEulerLower u ≠ 0 := by
    simpa only [pairedEulerLower, ← sub_eq_add_neg] using
      (tprod_one_add_ne_zero_of_summable hn (hs.congr fun j => by
        rw [norm_neg, Real.norm_of_nonneg (by positivity)]))
  exact lt_of_le_of_ne (tprod_nonneg (fun j => (sub_pos.mpr (exp_product_factor_lt_one hu j)).le)) h.symm

/-- Uniform strictly positive lower bound for the denominator of (47). -/
theorem pairedEulerLower_sq_le_norm_pairedProduct {u r : ℝ} (hu : 0 < u) (hr : |r| ≤ 1)
    {ζ : ℂ} (hζ : u ≤ ζ.re) (θ : ℝ) :
    pairedEulerLower u ^ 2 ≤ ‖pairedProduct r θ ζ‖ := by
  let b (j : ℕ) := Real.exp (-u / 2) * (Real.exp (-u)) ^ j
  have hb : Multipliable (fun j : ℕ => 1 - b j) :=
    multipliable_one_sub_of_summable ((summable_exp_product_factor hu).congr fun j => by
      dsimp only [b]
      rw [Real.norm_of_nonneg (by positivity)])
  let f (j : ℕ) := (1 + pairedTerm r θ ζ j) * (1 + pairedTerm r (-θ) ζ j)
  have hf : Multipliable f := multipliable_pairedProduct r θ (hu.trans_le hζ)
  have hlower (φ : ℝ) (j : ℕ) : 1 - b j ≤ ‖1 + pairedTerm r φ ζ j‖ := by
    have hbnd : ‖pairedTerm r φ ζ j‖ ≤ b j := by
      rw [norm_pairedTerm]
      simp only [b]
      calc
        _ ≤ (1 * Real.exp (-u / 2)) * (Real.exp (-u)) ^ j := by
          refine mul_le_mul (mul_le_mul hr (Real.exp_le_exp.mpr (by linarith))
            (Real.exp_nonneg _) zero_le_one)
            (pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr (by linarith)) _)
            (by positivity) (by positivity)
        _ = _ := by rw [one_mul]
    have h := norm_sub_norm_le (1 : ℂ) (-pairedTerm r φ ζ j)
    simpa only [norm_one, norm_neg, sub_neg_eq_add] using (sub_le_sub_left hbnd 1).trans (by
      simpa only [norm_one, norm_neg, sub_neg_eq_add] using h)
  have hsum := ((hb.hasProd.tendsto_prod_nat).pow 2)
  have hnorm := hf.hasProd.tendsto_prod_nat.norm
  refine le_of_tendsto_of_tendsto' hsum hnorm ?_
  intro n
  rw [pow_two, ← Finset.prod_mul_distrib, norm_prod]
  refine Finset.prod_le_prod₀ ?_ ?_
  · intro j _
    exact mul_self_nonneg _
  · intro j _
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_mul (hlower θ j) (hlower (-θ) j)
      (sub_pos.mpr (exp_product_factor_lt_one hu j)).le (norm_nonneg _)

theorem pairedProduct_ne_zero_small {r : ℝ} (hr : |r| ≤ 1) {ζ : ℂ} (hζ : 0 < ζ.re) (θ : ℝ) :
    pairedProduct r θ ζ ≠ 0 := by
  exact norm_pos_iff.mp ((sq_pos_of_pos (pairedEulerLower_pos hζ)).trans_le
    (pairedEulerLower_sq_le_norm_pairedProduct hζ hr le_rfl θ))

theorem eulerProduct_ne_zero_right {ζ : ℂ} (hζ : 0 < ζ.re) :
    eulerProduct ζ ≠ 0 := by
  have hnorm (j : ℕ) : ‖exp (-((j : ℂ) + 1) * ζ)‖ = (Real.exp (-ζ.re)) ^ (j + 1) := by
    rw [norm_exp, ← Real.exp_nat_mul]
    congr 1
    simp [Complex.mul_re, Complex.add_re]
    ring
  have hn (j : ℕ) : 1 + - exp (-((j : ℂ) + 1) * ζ) ≠ 0 := by
    have hh := pow_lt_one₀ (Real.exp_nonneg (-ζ.re)) (Real.exp_lt_one_iff.mpr (by linarith)) (by
      omega : (j + 1 : ℕ) ≠ 0)
    intro h
    have he : exp (-((j : ℂ) + 1) * ζ) = 1 := by
      rw [← sub_eq_add_neg] at h
      exact (sub_eq_zero.mp h).symm
    rw [← hnorm, he, norm_one] at hh
    exact lt_irrefl _ hh
  simpa only [eulerProduct, ← sub_eq_add_neg] using
    (tprod_one_add_ne_zero_of_summable hn
      (by simpa only [norm_neg, hnorm] using
        ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (Real.exp_nonneg (-ζ.re))
          (Real.exp_lt_one_iff.mpr (by linarith : -ζ.re < 0))))))

/-- Continuity on any fixed vertical line of the small-radius denominator. -/
theorem continuous_pairedProduct_vertical_small (r : ℝ) (hr : |r| ≤ 1) {u : ℝ} (hu : 0 < u) :
    Continuous (fun p : ℝ × ℝ => pairedProduct r p.2 (verticalPoint u p.1)) := by
  have h (p : ℝ × ℝ) : exp (pairedLog r p.2 (verticalPoint u p.1)) =
      pairedProduct r p.2 (verticalPoint u p.1) :=
    exp_pairedLog r p.2 hr (by simpa using hu)
  simp_rw [← h]
  exact Complex.continuous_exp.comp (continuous_pairedLog_vertical r hr hu)

theorem continuous_pairedProduct_angle_small (r : ℝ) (hr : |r| ≤ 1) {ζ : ℂ} (hζ : 0 < ζ.re) :
    Continuous (fun θ : ℝ => pairedProduct r θ ζ) := by
  have h : verticalPoint ζ.re ζ.im = ζ := Complex.re_add_im ζ
  have hp : Continuous (fun θ : ℝ => (ζ.im, θ)) := continuous_const.prodMk continuous_id
  simpa only [Function.comp_def, h] using
    (continuous_pairedProduct_vertical_small r hr hζ).comp hp

/-- The two triple products in the proof of (47), before division. -/
theorem theta_mul_theta_eq_pairedProduct {r : ℝ} (hr : r ≠ 0) {ζ : ℂ}
    (hζ : 0 < ζ.re) (θ : ℝ) :
    thetaSeries ((r : ℂ) * I * exp ((θ : ℂ) * I)) ζ *
      thetaSeries ((r : ℂ) * I * exp ((-θ : ℝ) * I)) ζ =
        eulerProduct ζ ^ 2 * pairedProduct r θ ζ * pairedProduct (-r⁻¹) θ ζ := by
  let a (t : ℝ) (j : ℕ) := 1 + pairedTerm r t ζ j
  let b (t : ℝ) (j : ℕ) := 1 + pairedTerm (-r⁻¹) t ζ j
  have ha (t : ℝ) : Multipliable (a t) := multipliable_one_add_of_summable (summable_norm_pairedTerm r t hζ)
  have hb (t : ℝ) : Multipliable (b t) :=
    multipliable_one_add_of_summable (summable_norm_pairedTerm (-r⁻¹) t hζ)
  have hn : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hθ (t : ℝ) : thetaSeries ((r : ℂ) * I * exp ((t : ℂ) * I)) ζ =
      eulerProduct ζ * ((∏' j, a t j) * (∏' j, b (-t) j)) := by
    let z : ℂ := (r : ℂ) * I * exp ((t : ℂ) * I)
    have invz : z⁻¹ = (-r⁻¹ : ℝ) * I * exp ((-t : ℝ) * I) := by
      have ht : ((-t : ℝ) : ℂ) * I = -((t : ℂ) * I) := by push_cast; ring
      rw [ht, exp_neg]
      push_cast
      dsimp [z]
      rw [mul_inv, mul_inv, inv_I]
      ring
    rw [theta_triple_product hζ (mul_ne_zero (mul_ne_zero hn I_ne_zero) (exp_ne_zero _)), invz,
      ← (ha t).tprod_mul (hb (-t))]
    congr 1
    apply tprod_congr
    intro j
    dsimp [a, b, pairedTerm]
    simp only [exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [hθ θ, hθ (-θ), neg_neg, pairedProduct, pairedProduct,
    (ha θ).tprod_mul (ha (-θ)), (hb θ).tprod_mul (hb (-θ))]
  ring

private theorem exp_int_pi_mul_I_parity (p : ℤ) :
    exp ((p : ℂ) * Real.pi * I) = if Even p then 1 else -1 := by
  by_cases hp : Even p
  · obtain ⟨m, hm⟩ := hp
    have hp' : Even p := ⟨m, hm⟩
    rw [ite_eq_left hp']
    have he : (p : ℂ) * Real.pi * I = (m : ℂ) * (2 * Real.pi * I) := by rw [hm]; push_cast; ring
    rw [he, exp_int_mul_two_pi_mul_I]
  · have hd : p = (p / 2) + (p / 2) + 1 := by
      have hh : p % 2 ≠ 0 := fun hz => hp (by
        refine ⟨p / 2, ?_⟩
        omega)
      omega
    rw [ite_eq_right hp, show (p : ℂ) * Real.pi * I = (p / 2 : ℤ) * (2 * Real.pi * I) + Real.pi * I by
      nth_rewrite 1 [hd]
      push_cast
      ring, exp_add, exp_int_mul_two_pi_mul_I, exp_pi_mul_I, one_mul]

/-- Translating each parity class by its Gaussian center changes only the radius sign. -/
theorem pairedProduct_midPoisson_shift (r θ : ℝ) (ζ : ℂ) (p m : ℤ) :
    pairedProduct (midModeRadius r p) (θ + (p + 2 * m : ℤ) * Real.pi) ζ =
      pairedProduct (-r⁻¹) θ ζ := by
  let d : ℤ := p + 2 * m
  have heven : Even d ↔ Even p := by
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨k - m, by dsimp [d] at hk; omega⟩
    · rintro ⟨k,hk⟩
      exact ⟨k + m, by dsimp [d]; omega⟩
  have hneg : Even (-d) ↔ Even p := by simpa only [even_neg] using heven
  have ha (t : ℝ) (j : ℕ) :
      pairedTerm (midModeRadius r p) (t + d * Real.pi) ζ j = pairedTerm (-r⁻¹) t ζ j := by
    have harg : -((j : ℂ) + 1 / 2) * ζ + ((t + d * Real.pi : ℝ) : ℂ) * I =
        (-((j : ℂ) + 1 / 2) * ζ + (t : ℂ) * I) + (d : ℂ) * Real.pi * I := by push_cast; ring
    rw [pairedTerm, pairedTerm, harg, exp_add, exp_int_pi_mul_I_parity]
    by_cases hp : Even p <;> simp only [heven, midModeRadius, hp, ite_true, ite_false,
      Complex.ofReal_neg, mul_one]; ring
  have hb (t : ℝ) (j : ℕ) :
      pairedTerm (midModeRadius r p) (-t + (-d : ℤ) * Real.pi) ζ j = pairedTerm (-r⁻¹) (-t) ζ j := by
    have harg : -((j : ℂ) + 1 / 2) * ζ + ((-t + (-d : ℤ) * Real.pi : ℝ) : ℂ) * I =
        (-((j : ℂ) + 1 / 2) * ζ + ((-t : ℝ) : ℂ) * I) + (-d : ℤ) * Real.pi * I := by push_cast; ring
    rw [pairedTerm, pairedTerm, harg, exp_add, exp_int_pi_mul_I_parity]
    by_cases hp : Even p <;> simp only [hneg, midModeRadius, hp, ite_true, ite_false,
      Complex.ofReal_neg, mul_one]; ring
  unfold pairedProduct
  apply tprod_congr
  intro j
  change (1 + pairedTerm (midModeRadius r p) (θ + d * Real.pi) ζ j) *
    (1 + pairedTerm (midModeRadius r p) (-(θ + d * Real.pi)) ζ j) = _
  rw [ha, show -(θ + (d : ℝ) * Real.pi) = -θ + (-d : ℤ) * Real.pi by push_cast; ring, hb]

end DurfeeCCS.Step09
