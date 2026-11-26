module

public import DurfeeCCS.Step06.ThetaProduct
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-! Theta and eta in the manuscript's right-half-plane coordinates. -/

@[expose] public section

namespace DurfeeCCS.Step06

open Complex
open scoped Real

/-- The ordinary Euler product at `q = exp (-ζ)`. -/
noncomputable def eulerProduct (ζ : ℂ) : ℂ :=
  ∏' j : ℕ, (1 - exp (-((j : ℂ) + 1) * ζ))

/-- The bilateral series in the manuscript's theta normalization. -/
noncomputable def thetaSeries (z ζ : ℂ) : ℂ :=
  ∑' j : ℤ, z ^ j * exp (-ζ * (j : ℂ) ^ 2 / 2)

/-- The terms of the transformed Gaussian series. -/
noncomputable def thetaGaussian (w ζ : ℂ) (j : ℤ) : ℂ :=
  exp ((w + 2 * (π : ℂ) * I * j) ^ 2 / (2 * ζ))

private theorem re_div_real (z : ℂ) (a : ℝ) : (z / (a : ℂ)).re = z.re / a := by
  rw [div_eq_mul_inv, ← ofReal_inv, re_mul_ofReal, div_eq_mul_inv]

private theorem im_div_real (z : ℂ) (a : ℝ) : (z / (a : ℂ)).im = z.im / a := by
  rw [div_eq_mul_inv, ← ofReal_inv, im_mul_ofReal, div_eq_mul_inv]

private theorem ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro h
  simp [h] at hz

private theorem norm_exp_neg_lt_one {ζ : ℂ} (hζ : 0 < ζ.re) : ‖exp (-ζ)‖ < 1 := by
  rw [norm_exp, neg_re]
  simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hζ)

private theorem eulerFactor_eq_power (ζ : ℂ) (j : ℕ) :
    exp (-((j : ℂ) + 1) * ζ) = (exp (-ζ)) ^ (j + 1) := by
  rw [← exp_nat_mul]
  congr 1
  push_cast
  ring

theorem eulerProduct_multipliable {ζ : ℂ} (hζ : 0 < ζ.re) :
    Multipliable fun j : ℕ => (1 - exp (-((j : ℂ) + 1) * ζ)) := by
  simp_rw [eulerFactor_eq_power]
  exact ModularForm.multipliable_one_sub_pow (norm_exp_neg_lt_one hζ)

/-- Jacobi's triple product, the first equality in (12). -/
theorem theta_triple_product {ζ z : ℂ} (hζ : 0 < ζ.re) (hz : z ≠ 0) :
    thetaSeries z ζ = eulerProduct ζ *
      (∏' j : ℕ, ((1 + z * exp (-((j : ℂ) + 1 / 2) * ζ)) *
        (1 + z⁻¹ * exp (-((j : ℂ) + 1 / 2) * ζ)))) := by
  let q := exp (-(ζ / 2))
  have hhalf : 0 < (ζ / 2).re := by
    change 0 < (ζ / ((2 : ℝ) : ℂ)).re
    rw [re_div_real]
    positivity
  have hq : ‖q‖ < 1 := norm_exp_neg_lt_one hhalf
  have hr : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  have hq2 : q ^ 2 = exp (-ζ) := by
    dsimp [q]
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpair (j : ℕ) : q * (q ^ 2) ^ j = exp (-((j : ℂ) + 1 / 2) * ζ) := by
    rw [hq2, ← exp_nat_mul, show q = exp (-(ζ / 2)) from rfl, ← exp_add]
    congr 1
    ring
  have hterm (m : ℤ) : q ^ (m.natAbs ^ 2) = exp (-ζ * (m : ℂ) ^ 2 / 2) := by
    dsimp [q]
    rw [← exp_nat_mul]
    congr 1
    have hcast := congrArg (fun n : ℤ => (n : ℂ)) (Int.natAbs_sq m)
    push_cast at hcast
    rw [Nat.cast_pow, ← Int.cast_natCast, Int.natCast_natAbs, hcast]
    ring
  have hE : (∏' j : ℕ, (1 - (q ^ 2) ^ (j + 1))) = eulerProduct ζ := by
    simp_rw [hq2, ← eulerFactor_eq_power, eulerProduct]
  have h := jacobi_triple_product hq hz
  rw [hE, mul_assoc, ← (qProduct_multipliable hr (z * q)).tprod_mul
    (qProduct_multipliable hr (z⁻¹ * q))] at h
  simp_rw [hterm, mul_assoc _ q, hpair] at h
  exact h

/-- The Euler product in the paper is the eta product with its initial exponential removed. -/
theorem eta_rightHalfPlane (ζ : ℂ) :
    ModularForm.eta (I * ζ / (2 * (π : ℂ))) = exp (-ζ / 24) * eulerProduct ζ := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold ModularForm.eta eulerProduct
  congr 1
  · unfold Function.Periodic.qParam
    congr 1
    push_cast
    field_simp
    ring_nf
    simp [I_sq]
  · congr 1
    funext j
    rw [ModularForm.eta_q_eq_cexp]
    congr 2
    field_simp
    ring_nf
    simp [I_sq]

private theorem sqrt_I_mul_rightHalfPlane {a : ℂ} (ha : 0 < a.re) :
    sqrt (I * a) = sqrt I * sqrt a := by
  apply mul_cpow
  rw [arg_I, Set.mem_Ioc]
  have hb := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  rw [abs_lt] at hb
  constructor <;> linarith [Real.pi_pos, hb.1, hb.2]

private theorem sqrt_inv_rightHalfPlane {a : ℂ} (ha : 0 < a.re) :
    sqrt a⁻¹ = (sqrt a)⁻¹ := by
  apply inv_cpow
  have hb := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  rw [abs_lt] at hb
  intro he
  linarith [Real.pi_pos, hb.2]

/-- Equation (13), with the principal complex square root and the exact normalization of the
    exponential factor. -/
theorem eulerProduct_modular {ζ : ℂ} (hζ : 0 < ζ.re) :
    eulerProduct ζ = sqrt (2 * (π : ℂ) / ζ) *
      exp (ζ / 24 - (π : ℂ) ^ 2 / (6 * ζ)) * eulerProduct (4 * (π : ℂ) ^ 2 / ζ) := by
  let a := ζ / (2 * (π : ℂ))
  let ζ' := 4 * (π : ℂ) ^ 2 / ζ
  let τ := I * a
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hζ₀ := ne_zero_of_re_pos hζ
  have ha : 0 < a.re := by
    have h : a = ζ / ((2 * π : ℝ) : ℂ) := by simp [a]
    rw [h, re_div_real]
    exact div_pos hζ (by positivity)
  have ha₀ := ne_zero_of_re_pos ha
  have hτ : τ ∈ UpperHalfPlane.upperHalfPlaneSet := by
    change 0 < (I * a).im
    simpa only [I_mul_im] using ha
  have hτ_def : τ = I * ζ / (2 * (π : ℂ)) := by simp [τ, a, mul_div_assoc]
  have hτ_inv : -1 / τ = I * ζ' / (2 * (π : ℂ)) := by
    dsimp [τ, a, ζ']
    field_simp
    ring_nf
    simp [I_sq]
  have hS := ModularForm.eta_comp_eq_csqrt_I_inv hτ
  change ModularForm.eta (-1 / τ) = (sqrt I)⁻¹ * (sqrt τ * ModularForm.eta τ) at hS
  have hS' : ModularForm.eta (-1 / τ) = sqrt a * ModularForm.eta τ := by
    rw [hS, show sqrt τ = sqrt I * sqrt a from sqrt_I_mul_rightHalfPlane ha,
      ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (by simp [sqrt, I_ne_zero]), one_mul]
  rw [hτ_inv, eta_rightHalfPlane, hτ_def, eta_rightHalfPlane] at hS'
  have hsqrt : sqrt a ≠ 0 := by simp [sqrt, ha₀]
  have hfac : sqrt (2 * (π : ℂ) / ζ) = (sqrt a)⁻¹ := by
    rw [← sqrt_inv_rightHalfPlane ha]
    simp [a, inv_div]
  have hexp : exp (-ζ / 24) * exp (ζ / 24 - (π : ℂ) ^ 2 / (6 * ζ)) =
      exp (-ζ' / 24) := by
    rw [← exp_add]
    congr 1
    dsimp [ζ']
    field_simp
    ring
  rw [hfac]
  apply mul_left_cancel₀ (a := sqrt a * exp (-ζ / 24)) (mul_ne_zero hsqrt (exp_ne_zero _))
  calc
    sqrt a * exp (-ζ / 24) * eulerProduct ζ = exp (-ζ' / 24) * eulerProduct ζ' := by
      simpa only [mul_assoc] using hS'.symm
    _ = sqrt a * exp (-ζ / 24) *
        ((sqrt a)⁻¹ * exp (ζ / 24 - (π : ℂ) ^ 2 / (6 * ζ)) * eulerProduct ζ') := by
      rw [← hexp]
      field_simp [hsqrt]

private theorem summable_norm_exp_quadratic {b : ℂ} (hb : b.re < 0) (a : ℂ) :
    Summable fun j : ℤ => ‖exp (a * j + b * (j : ℂ) ^ 2)‖ := by
  let z := -I * a / ((2 * π : ℝ) : ℂ)
  let τ := -I * b / (π : ℂ)
  have hτ : 0 < τ.im := by
    dsimp [τ]
    rw [im_div_real, neg_mul, neg_im, I_mul_im]
    exact div_pos (neg_pos.mpr hb) Real.pi_pos
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hterm (j : ℤ) : exp (a * j + b * (j : ℂ) ^ 2) = jacobiTheta₂_term j z τ := by
    rw [jacobiTheta₂_term]
    congr 1
    dsimp [z, τ]
    push_cast
    field_simp
    ring_nf
    simp [I_sq]
  simp_rw [hterm]
  exact (summable_norm_iff (E := ℂ)).mpr ((summable_jacobiTheta₂_term_iff z τ).mpr hτ)

/-- Absolute convergence of the initial bilateral series in (12). -/
theorem thetaSeries_absolutelyConvergent {ζ z : ℂ} (hζ : 0 < ζ.re) (hz : z ≠ 0) :
    Summable fun j : ℤ => ‖z ^ j * exp (-ζ * (j : ℂ) ^ 2 / 2)‖ := by
  have hterm (j : ℤ) : z ^ j * exp (-ζ * (j : ℂ) ^ 2 / 2) =
      exp (log z * j + (-ζ / 2) * (j : ℂ) ^ 2) := by
    rw [exp_add, mul_comm _ (j : ℂ), exp_int_mul, exp_log hz]
    congr 2
    ring
  simp_rw [hterm]
  refine summable_norm_exp_quadratic (b := -ζ / 2) ?_ (log z)
  show (-ζ / ((2 : ℝ) : ℂ)).re < 0
  rw [re_div_real, neg_re]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hζ) (by norm_num)

/-- Absolute convergence on the transformed side of (12), for arbitrary complex `w`. -/
theorem thetaGaussian_absolutelyConvergent {ζ : ℂ} (hζ : 0 < ζ.re) (w : ℂ) :
    Summable fun j : ℤ => ‖thetaGaussian w ζ j‖ := by
  let b : ℂ := (-((2 * π ^ 2 : ℝ) : ℂ)) * ζ⁻¹
  let a : ℂ := (2 * (π : ℂ) * I * w) / ζ
  have hb : b.re < 0 := by
    dsimp [b]
    rw [← ofReal_neg, re_ofReal_mul, inv_re]
    refine mul_neg_of_neg_of_pos (neg_neg_of_pos (show 0 < (2 * π ^ 2 : ℝ) by positivity)) ?_
    exact div_pos hζ (normSq_pos.mpr (ne_zero_of_re_pos hζ))
  have hζ₀ := ne_zero_of_re_pos hζ
  have hterm (j : ℤ) : thetaGaussian w ζ j =
      exp (w ^ 2 / (2 * ζ)) * exp (a * j + b * (j : ℂ) ^ 2) := by
    rw [thetaGaussian, ← exp_add]
    congr 1
    dsimp [a, b]
    push_cast
    field_simp
    ring_nf
    simp [I_sq, sub_eq_add_neg]
  simp_rw [hterm, norm_mul]
  exact (summable_norm_exp_quadratic hb a).mul_left _

/-- The second equality in (12), with `exp w` as the theta variable. -/
theorem theta_gaussian_transform {ζ : ℂ} (hζ : 0 < ζ.re) (w : ℂ) :
    thetaSeries (exp w) ζ = sqrt (2 * (π : ℂ) / ζ) * (∑' j : ℤ, thetaGaussian w ζ j) := by
  let a := ζ / ((2 * π : ℝ) : ℂ)
  let b := w / ((2 * π : ℝ) : ℂ)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hζ₀ := ne_zero_of_re_pos hζ
  have ha : 0 < a.re := by
    dsimp [a]
    rw [re_div_real]
    exact div_pos hζ (by positivity)
  have hroot : sqrt (2 * (π : ℂ) / ζ) = 1 / a ^ (1 / 2 : ℂ) := by
    rw [show 2 * (π : ℂ) / ζ = a⁻¹ by simp [a, inv_div], sqrt_inv_rightHalfPlane ha,
      sqrt, one_div]
    rw [one_div]
  rw [thetaSeries, hroot, ← (Equiv.neg ℤ).tsum_eq (thetaGaussian w ζ)]
  convert Complex.tsum_exp_neg_quadratic ha b using 1
  · apply tsum_congr
    intro j
    rw [← exp_int_mul, ← exp_add]
    congr 1
    dsimp [a, b]
    push_cast
    field_simp
    ring
  · congr 1
    apply tsum_congr
    intro j
    rw [Equiv.neg_apply, thetaGaussian]
    congr 1
    dsimp [a, b]
    push_cast
    field_simp
    ring_nf
    simp [I_sq, sub_eq_add_neg]

end DurfeeCCS.Step06
