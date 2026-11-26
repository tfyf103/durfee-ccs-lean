module

public import DurfeeCCS.Step10.OuterErrorNormalize
public import DurfeeCCS.Step10.OuterBesselEndpoints
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! High-frequency bounds for the explicit Bessel transform on pages 41–42. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Complex Set MeasureTheory

abbrev outerBesselScale : ℝ := 4 * π ^ 2 / 3

def outerZeta (h v : ℝ) : ℂ := (h : ℂ) + I * (v : ℂ)

@[simp] theorem outerZeta_re (h v : ℝ) : (outerZeta h v).re = h := by simp [outerZeta, Complex.mul_re]

@[simp] theorem outerZeta_im (h v : ℝ) : (outerZeta h v).im = v := by simp [outerZeta, Complex.mul_im]

theorem normSq_outerZeta (h v : ℝ) : ‖outerZeta h v‖ ^ 2 = h ^ 2 + v ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, outerZeta_re, outerZeta_im]
  ring

private theorem outerZeta_sq_sqrt {h v : ℝ} (hh : 0 < h) : (outerZeta h v ^ 2).sqrt = outerZeta h v := by
  have hs := DurfeeCCS.Step06.principalSqrt_sq (outerZeta h v ^ 2)
  have hr : 0 ≤ (outerZeta h v ^ 2).sqrt.re := by
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp <;> positivity
  rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hs with he | he
  · exact he
  · rw [he, Complex.neg_re, outerZeta_re] at hr
    linarith

def outerHighGap (h : ℝ) : ℝ := outerBesselScale / h * max 0.152 (1 / 4 - 8.4 / h ^ 2)

private theorem norm_sinhKernelDerivative_high {y h v u : ℝ}
    (hy : 72 ≤ y) (hh : 8.76 < h) (hv : h < |v|) (hu : 0 ≤ u) (hu' : u ≤ outerBesselScale) :
    let ζ := outerZeta h v
    let z := (ζ ^ 2 + (u : ℂ)).sqrt
    ‖((y : ℂ) * Complex.cosh ((y : ℂ) * z)) / (2 * (ζ ^ 2 + (u : ℂ))) -
        Complex.sinh ((y : ℂ) * z) / (2 * z ^ 3)‖ ≤
      0.55 * y / (h ^ 2 + v ^ 2) * Real.exp (y * ((outerRho h π).re - outerHighGap h)) := by
  dsimp only
  let ζ := outerZeta h v
  let z := outerRhoAt h v u
  let D := h ^ 2 + v ^ 2
  let E₀ := Real.exp (y * ((outerRho h π).re - outerHighGap h))
  let E := Real.exp (y * z.re)
  have hy₀ : 0 < y := by linarith
  have hh₀ : 0 < h := by linarith
  have hv₂ : h ^ 2 < v ^ 2 := by
    simpa only [sq_abs] using (pow_lt_pow_left₀ hv hh₀.le two_ne_zero)
  have hD : 2 * (8.76 : ℝ) ^ 2 < D := by
    dsimp [D]
    nlinarith
  have hD₀ : 0 < D := by linarith
  have hπ : outerBesselScale < 13.16 := by
    calc
      4 * π ^ 2 / 3 ≤ 4 * (3.141593 : ℝ) ^ 2 / 3 := by gcongr; exact pi_lt_d6.le
      _ < _ := by norm_num
  have hnorm : 0.914 * D ≤ ‖ζ ^ 2 + (u : ℂ)‖ := by
    have hr := norm_sub_le (ζ ^ 2 + (u : ℂ)) (u : ℂ)
    rw [add_sub_cancel_right, norm_pow] at hr
    have hzeta : ‖ζ‖ ^ 2 = D := normSq_outerZeta h v
    rw [hzeta, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] at hr
    linarith
  have hzn : ‖z‖ ^ 2 = ‖ζ ^ 2 + (u : ℂ)‖ := by
    rw [← norm_pow]
    exact congrArg norm (outerRhoAt_sq h v u)
  have hzn₀ : 11 ≤ ‖z‖ := by
    apply (sq_le_sq₀ (by norm_num) (norm_nonneg _)).1
    rw [hzn]
    linarith
  have hN : 0 ≤ y * z.re := by
    apply mul_nonneg hy₀.le
    change 0 ≤ (ζ ^ 2 + (u : ℂ)).sqrt.re
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp <;> positivity
  have hs := norm_sinh_real_mul_le hN
  have hc := norm_cosh_real_mul_le hN
  have hgap := outerRho_high_gap hh hv hu hu'
  have hE : E ≤ E₀ := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hy₀.le
    change z.re ≤ (outerRho h π).re - _
    have h₁ : 3 * h / (4 * π ^ 2) = h / outerBesselScale := by ring
    rw [h₁] at hgap
    have hA : 0 < outerBesselScale := by positivity
    have h₂ := mul_le_mul_of_nonneg_left hgap.le
      (div_nonneg hA.le hh₀.le)
    have h₃ : outerBesselScale / h * (h / outerBesselScale * ((outerRho h π).re - z.re)) =
        (outerRho h π).re - z.re := by field_simp
    change outerHighGap h ≤ _ at h₂
    rw [h₃] at h₂
    linarith
  change ‖((y : ℂ) * Complex.cosh ((y : ℂ) * z)) / (2 * (ζ ^ 2 + (u : ℂ))) -
        Complex.sinh ((y : ℂ) * z) / (2 * z ^ 3)‖ ≤ 0.55 * y / D * E₀
  apply (norm_sub_le _ _).trans
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hy₀]
  have hden : 0 < (0.914 : ℝ) * D := by positivity
  have hNle : ‖z‖ ^ 3 = ‖ζ ^ 2 + (u : ℂ)‖ * ‖z‖ := by
    rw [← hzn]
    ring
  rw [hNle]
  calc
    _ ≤ y * E₀ / (2 * (0.914 * D)) + E₀ / (2 * (0.914 * D * 11)) := by
      gcongr <;> first | exact hc.trans hE | exact hs.trans hE
    _ = (y / (2 * 0.914) + 1 / (2 * 0.914 * 11)) * (E₀ / D) := by
      field_simp
    _ ≤ _ := by
      rw [show 0.55 * y / D * E₀ = 0.55 * y * (E₀ / D) by ring]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      norm_num
      linarith

/-- The mean-value bound for the difference under the integral in (69). -/
theorem outerHigh_sinh_difference {y h v u : ℝ}
    (hy : 72 ≤ y) (hh : 8.76 < h) (hv : h < |v|) (hu : 0 ≤ u) (hu' : u ≤ outerBesselScale) :
    let ζ := outerZeta h v
    let z := (ζ ^ 2 + (u : ℂ)).sqrt
    ‖Complex.sinh ((y : ℂ) * z) / z - Complex.sinh ((y : ℂ) * ζ) / ζ‖ ≤
      (0.55 * y / (h ^ 2 + v ^ 2) * Real.exp (y * ((outerRho h π).re - outerHighGap h))) * u := by
  dsimp only
  let ζ := outerZeta h v
  let F (s : ℝ) := Complex.sinh ((y : ℂ) * (ζ ^ 2 + (s : ℂ)).sqrt) / (ζ ^ 2 + (s : ℂ)).sqrt
  have hζ : 0 < ζ.re := by rw [outerZeta_re]; linarith
  have hh₀ : 0 < h := by linarith
  have H := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := F)
    (fun s (hs : s ∈ Icc (0 : ℝ) u) => (sinhKernelDerivative hζ hs.1 y).hasDerivWithinAt)
    (fun s (hs : s ∈ Icc (0 : ℝ) u) => norm_sinhKernelDerivative_high hy hh hv hs.1 (hs.2.trans hu'))
    (show 0 ∈ Icc (0 : ℝ) u from ⟨le_rfl, hu⟩)
    (show u ∈ Icc (0 : ℝ) u from ⟨hu, le_rfl⟩)
  simp only [F, Complex.ofReal_zero, add_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hu] at H
  simpa only [ζ, outerZeta_sq_sqrt hh₀] using H

/-- The transform at |v| > h, in the explicit integral form (69). -/
theorem outerHigh_transform_point {y h v : ℝ} (hy : 72 ≤ y) (hh : 8.76 < h)
    (hv : h < |v|) :
    ‖kernelTransformIntegralFormula y (outerZeta h v)‖ ≤
      (0.55 * π * outerBesselScale ^ 2 / 72) * y / (h ^ 2 + v ^ 2) *
        Real.exp (y * ((outerRho h π).re - outerHighGap h)) := by
  let ζ := outerZeta h v
  let L := 0.55 * y / (h ^ 2 + v ^ 2) * Real.exp (y * ((outerRho h π).re - outerHighGap h))
  let g (t : ℝ) := outerBesselScale * L * (t ^ 3 - t ^ 5)
  have hA : 0 ≤ outerBesselScale := by positivity
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hL₀ : 0 ≤ L := by dsimp [L]; positivity
  have hy₀ : 0 < y := by linarith
  unfold kernelTransformIntegralFormula
  rw [norm_mul]
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos pi_pos]
  let F (t : ℝ) : ℂ :=
      let z := (ζ ^ 2 + ((outerBesselScale * t ^ 2 : ℝ) : ℂ)).sqrt
      ((t * (1 - t ^ 2) : ℝ) : ℂ) *
        (Complex.sinh ((y : ℂ) * z) / z - Complex.sinh ((y : ℂ) * ζ) / ζ)
  have hi : ‖∫ t in (0 : ℝ)..1, F t‖ ≤ ∫ t in (0 : ℝ)..1, g t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) _ (hg.intervalIntegrable 0 1)
    apply Filter.Eventually.of_forall
    intro t ht'
    dsimp only [F]
    have hpow : t ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ ht'.1.le ht'.2 2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht'.1.le (sub_nonneg.mpr hpow))]
    calc
      _ ≤ (t * (1 - t ^ 2)) * (L * (outerBesselScale * t ^ 2)) :=
        mul_le_mul_of_nonneg_left (outerHigh_sinh_difference hy hh hv (by positivity)
          (mul_le_of_le_one_right hA hpow)) (mul_nonneg ht'.1.le (sub_nonneg.mpr hpow))
      _ = g t := by dsimp [g]; ring
  have hgi : (∫ t in (0 : ℝ)..1, g t) = outerBesselScale * L / 12 := by
    unfold g
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun t : ℝ => t ^ 3) (g := fun t : ℝ => t ^ 5)
        ((continuous_id.pow 3).intervalIntegrable _ _) ((continuous_id.pow 5).intervalIntegrable _ _),
      integral_pow, integral_pow]
    ring
  rw [hgi] at hi
  calc
    _ ≤ (2 * π ^ 3 / 9) * (outerBesselScale * L / 12) := by gcongr
    _ = _ := by dsimp [L, outerBesselScale]; ring

end DurfeeCCS.Step10
