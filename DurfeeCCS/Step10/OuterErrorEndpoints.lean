module

public import DurfeeCCS.Step07.OuterTableMonotone
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-! Endpoint estimates for the outer Bessel transform, as used on page 41. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real

/-- The principal exponential term in the transform at a given square root. -/
def outerEndpointMain (y : ℝ) (ρ : ℂ) : ℂ :=
  ρ * Complex.exp ((y : ℂ) * ρ) / (8 * (π : ℂ) * (y : ℂ) ^ 2)

/-- The upper endpoint in the transform formula (70). -/
def outerEndpointUpper (y : ℝ) (ρ : ℂ) : ℂ :=
  ρ * Complex.sinh ((y : ℂ) * ρ) / (4 * (π : ℂ) * (y : ℂ) ^ 2) -
    Complex.cosh ((y : ℂ) * ρ) / (4 * (π : ℂ) * (y : ℂ) ^ 3)

/-- The lower endpoint in (70), including the constant removed from the kernel. -/
def outerEndpointLower (y : ℝ) (ζ : ℂ) : ℂ :=
  (π : ℂ) * Complex.cosh ((y : ℂ) * ζ) / (6 * (y : ℂ)) +
  ζ * Complex.sinh ((y : ℂ) * ζ) / (4 * (π : ℂ) * (y : ℂ) ^ 2) -
    Complex.cosh ((y : ℂ) * ζ) / (4 * (π : ℂ) * (y : ℂ) ^ 3) +
    (π : ℂ) ^ 3 * Complex.sinh ((y : ℂ) * ζ) / (18 * ζ)

private theorem norm_exp_real_mul (y : ℝ) (z : ℂ) :
    ‖Complex.exp ((y : ℂ) * z)‖ = exp (y * z.re) := by
  rw [Complex.norm_exp, Complex.mul_re]
  simp

private theorem norm_exp_neg_real_mul (y : ℝ) (z : ℂ) :
    ‖Complex.exp (-((y : ℂ) * z))‖ = exp (-(y * z.re)) := by
  rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re]
  simp

theorem norm_sinh_real_mul_le {y : ℝ} {z : ℂ} (hz : 0 ≤ y * z.re) :
    ‖Complex.sinh ((y : ℂ) * z)‖ ≤ exp (y * z.re) := by
  rw [Complex.sinh, norm_div]
  norm_num [Complex.norm_ofNat]
  have h₁ := norm_sub_le (Complex.exp ((y : ℂ) * z)) (Complex.exp (-((y : ℂ) * z)))
  rw [norm_exp_real_mul, norm_exp_neg_real_mul] at h₁
  have h₂ : exp (-(y * z.re)) ≤ exp (y * z.re) := exp_le_exp.mpr (by linarith)
  linarith

theorem norm_cosh_real_mul_le {y : ℝ} {z : ℂ} (hz : 0 ≤ y * z.re) :
    ‖Complex.cosh ((y : ℂ) * z)‖ ≤ exp (y * z.re) := by
  rw [Complex.cosh, norm_div]
  norm_num [Complex.norm_ofNat]
  have h₁ := norm_add_le (Complex.exp ((y : ℂ) * z)) (Complex.exp (-((y : ℂ) * z)))
  rw [norm_exp_real_mul, norm_exp_neg_real_mul] at h₁
  have h₂ : exp (-(y * z.re)) ≤ exp (y * z.re) := exp_le_exp.mpr (by linarith)
  linarith

theorem norm_outerEndpointMain {y : ℝ} (hy : 0 < y) (ρ : ℂ) :
    ‖outerEndpointMain y ρ‖ = ‖ρ‖ * exp (y * ρ.re) / (8 * π * y ^ 2) := by
  rw [outerEndpointMain, norm_div, norm_mul, norm_exp_real_mul]
  simp [norm_pow, abs_of_pos hy, abs_of_pos pi_pos]

/-- The normalized error at the upper endpoint in (70). -/
theorem outerUpperEndpoint_error {y h : ℝ} {ρ : ℂ} (hy : 0 < y) (hh : 0 < h)
    (hρ : h ≤ ρ.re) (hyh : 1 ≤ y * h) :
    ‖outerEndpointUpper y ρ - outerEndpointMain y ρ‖ ≤
      ‖outerEndpointMain y ρ‖ * (1 / (y * h) + 2 * exp (-2 * (y * h))) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hπc : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_pos.ne'
  have hρn : h ≤ ‖ρ‖ := hρ.trans (Complex.re_le_norm _)
  have hprod : y * h ≤ y * ρ.re := mul_le_mul_of_nonneg_left hρ hy.le
  have hE : exp (-(y * ρ.re)) ≤ exp (y * ρ.re) * exp (-2 * (y * h)) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    linarith
  have hrewrite :
      outerEndpointUpper y ρ - outerEndpointMain y ρ =
        -(ρ * Complex.exp (-((y : ℂ) * ρ))) / (8 * (π : ℂ) * (y : ℂ) ^ 2) -
          (Complex.exp ((y : ℂ) * ρ) + Complex.exp (-((y : ℂ) * ρ))) /
            (8 * (π : ℂ) * (y : ℂ) ^ 3) := by
    unfold outerEndpointUpper outerEndpointMain Complex.sinh Complex.cosh
    field_simp
    ring
  rw [hrewrite, norm_outerEndpointMain hy]
  apply (norm_sub_le _ _).trans
  simp only [norm_div, norm_neg, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hy, abs_of_pos pi_pos, norm_exp_neg_real_mul]
  have hcos := norm_add_le (Complex.exp ((y : ℂ) * ρ)) (Complex.exp (-((y : ℂ) * ρ)))
  rw [norm_exp_real_mul, norm_exp_neg_real_mul] at hcos
  apply (add_le_add le_rfl (div_le_div_of_nonneg_right hcos (by positivity))).trans
  let E := exp (y * ρ.re)
  let ε := exp (-2 * (y * h))
  have hE₀ : 0 ≤ E := exp_nonneg _
  have hε₀ : 0 ≤ ε := exp_nonneg _
  have hratio : 1 / (y * ‖ρ‖) ≤ 1 / (y * h) :=
    div_le_div_of_nonneg_left zero_le_one (by positivity) (mul_le_mul_of_nonneg_left hρn hy.le)
  have hεratio : ε / (y * h) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).2
    exact le_mul_of_one_le_right hε₀ hyh
  have hmag : 0 < ‖ρ‖ := hh.trans_le hρn
  calc
    _ ≤ ‖ρ‖ * (E * ε) / (8 * π * y ^ 2) + (E + E * ε) / (8 * π * y ^ 3) := by
      gcongr
    _ = (‖ρ‖ * E / (8 * π * y ^ 2)) * (ε + (1 + ε) / (y * ‖ρ‖)) := by
      field_simp
    _ ≤ (‖ρ‖ * E / (8 * π * y ^ 2)) * (ε + (1 + ε) / (y * h)) := by
      gcongr
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [add_div]
      linarith

/-- Bound the lower endpoint and the subtracted constant term together. -/
theorem outerLowerEndpoint_error {y h : ℝ} {ζ : ℂ} (hy : 72 < y) (hh : 0 < h)
    (hscale : h / y ≤ 0.240) (hζ : ζ.re = h)
    (hζlo : h ≤ ‖ζ‖) (hζhi : ‖ζ‖ ≤ Real.sqrt 2 * h) :
    ‖outerEndpointLower y ζ‖ ≤ 2 / h * exp (y * h) := by
  have hy₀ : 0 < y := by linarith
  have hterm : 0 ≤ y * ζ.re := by rw [hζ]; positivity
  have hc := norm_cosh_real_mul_le hterm
  have hs := norm_sinh_real_mul_le hterm
  rw [hζ] at hc hs
  let C := Complex.cosh ((y : ℂ) * ζ)
  let S := Complex.sinh ((y : ℂ) * ζ)
  let E := exp (y * h)
  have hnorm :
      ‖outerEndpointLower y ζ‖ ≤
        ‖(π : ℂ) * C / (6 * (y : ℂ))‖ +
          ‖ζ * S / (4 * (π : ℂ) * (y : ℂ) ^ 2)‖ +
          ‖C / (4 * (π : ℂ) * (y : ℂ) ^ 3)‖ +
          ‖(π : ℂ) ^ 3 * S / (18 * ζ)‖ := by
    unfold outerEndpointLower
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  apply hnorm.trans
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hy₀, abs_of_pos pi_pos]
  calc
    _ ≤ π * E / (6 * y) + (sqrt 2 * h) * E / (4 * π * y ^ 2) +
          E / (4 * π * y ^ 3) + π ^ 3 * E / (18 * h) := by
      dsimp [C, S, E]
      gcongr
    _ = (π * (h / y) / 6 + sqrt 2 * (h / y) ^ 2 / (4 * π) +
          (h / y) / (4 * π * y ^ 2) + π ^ 3 / 18) * E / h := by
      field_simp
    _ ≤ _ := by
      have hr₀ : 0 ≤ h / y := by positivity
      have hp₀ : 3.14 ≤ π := Real.pi_gt_d2.le
      have hp₁ : π ≤ 3.142 := Real.pi_lt_d6.le.trans (by norm_num)
      have hrt : sqrt (2 : ℝ) ≤ 1.415 := (Real.sqrt_le_iff).2 (by norm_num)
      have hy₂ : (72 : ℝ) ^ 2 ≤ y ^ 2 := by gcongr
      have hb :
          π * (h / y) / 6 + sqrt 2 * (h / y) ^ 2 / (4 * π) +
              (h / y) / (4 * π * y ^ 2) + π ^ 3 / 18 ≤ 2 := by
        calc
          _ ≤ (3.142 : ℝ) * 0.240 / 6 + 1.415 * 0.240 ^ 2 / (4 * 3.14) +
              0.240 / (4 * 3.14 * 72 ^ 2) + 3.142 ^ 3 / 18 := by gcongr
          _ ≤ 2 := by norm_num
      calc
        _ ≤ 2 * E / h := by gcongr
        _ = _ := by ring

/-- Combine the two endpoint bounds when (70) holds. -/
theorem outerEndpoint_error {y h : ℝ} {ζ ρ T : ℂ} (hy : 72 < y) (hh : 0 < h)
    (hscale : h / y ≤ 0.240) (hζ : ζ.re = h) (hρ : h ≤ ρ.re) (hyh : 1 ≤ y * h)
    (hζlo : h ≤ ‖ζ‖) (hζhi : ‖ζ‖ ≤ Real.sqrt 2 * h)
    (hT : T = outerEndpointUpper y ρ - outerEndpointLower y ζ) :
    ‖T - outerEndpointMain y ρ‖ ≤
      ‖outerEndpointMain y ρ‖ * (1 / (y * h) + 2 * exp (-2 * (y * h))) +
        2 / h * exp (y * h) := by
  rw [hT, sub_right_comm]
  exact (norm_sub_le _ _).trans (add_le_add
    (outerUpperEndpoint_error (by linarith) hh hρ hyh)
    (outerLowerEndpoint_error hy hh hscale hζ hζlo hζhi))

end DurfeeCCS.Step10
