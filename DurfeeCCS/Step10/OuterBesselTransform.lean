module

public import DurfeeCCS.Step10.OuterBesselSphere
public import DurfeeCCS.Step10.OuterBesselWeight

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Identification of the exact Laplace transform with equations (69) and (70). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Complex Set MeasureTheory intervalIntegral DurfeeCCS.Step06

private theorem sphereBessel_zeroFactor (y x : ℝ) : sphereBesselFactor y 0 x = 1 := by
  simp only [sphereBesselFactor, zero_mul, Complex.ofReal_zero, besselI]
  rw [tsum_eq_single 0]
  · norm_num [besselITerm]
  · intro k hk
    simp [besselITerm, zero_pow (show 2 * k ≠ 0 by omega)]

/-- Equation (69) for the exact compactly supported kernel. -/
theorem kernelTransformIntegral {y : ℝ} {ζ : ℂ} (hy : 0 ≤ y) (hζ : 0 < ζ.re) :
    kernelTransform y ζ = kernelTransformIntegralFormula y ζ := by
  let b : ℝ := 2 * Real.pi / Real.sqrt 3
  let A (t : ℝ) : ℂ := ((t * (1 - t ^ 2) : ℝ) : ℂ)
  let E (x : ℝ) : ℂ := Complex.exp (ζ * (x : ℂ))
  let F (x t : ℝ) : ℂ := A t * (sphereBesselFactor y (b * t) x - 1) * E x
  let W (t : ℝ) := (ζ ^ 2 + ((4 * Real.pi ^ 2 / 3 * t ^ 2 : ℝ) : ℂ)).sqrt
  let S (z : ℂ) : ℂ := Complex.sinh ((y : ℂ) * z) / z
  have hcontB : Continuous (besselI 0) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_besselI 0 z).continuousAt
  have hcontF : Continuous F.uncurry := by
    change Continuous (fun p : ℝ × ℝ => A p.2 * (sphereBesselFactor y (b * p.2) p.1 - 1) * E p.1)
    apply Continuous.mul
    · apply Continuous.mul (by dsimp [A]; fun_prop)
      apply Continuous.sub _ continuous_const
      unfold sphereBesselFactor
      exact hcontB.comp (by fun_prop)
    · dsimp [E]
      fun_prop
  have hon : -y ≤ y := by linarith
  have hFint : IntegrableOn F.uncurry (uIoc (-y) y ×ˢ uIoc 0 1) := by
    rw [uIoc_of_le hon, uIoc_of_le zero_le_one]
    exact (hcontF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hfirst : kernelTransform y ζ =
      ((Real.pi : ℂ) ^ 3 / 9) * ∫ x in -y..y, ∫ t in (0 : ℝ)..1, F x t := by
    rw [kernelTransform_eq_core hy, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hon] at hx
    have hu : 0 ≤ y ^ 2 - x ^ 2 := sub_nonneg.2 (sq_le_sq.2 (by rw [abs_of_nonneg hy]; exact abs_le.2 hx))
    simp only
    rw [outerBesselCore_eq_weighted hu, mul_assoc, ← intervalIntegral.integral_mul_const]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [F, E, A, sphereBesselFactor, b]
    rw [mul_right_comm (2 * Real.pi / Real.sqrt 3) t]
  have hζ₀ : ζ ≠ 0 := by intro h; rw [h, Complex.zero_re] at hζ; exact (lt_irrefl _) hζ
  have hzeroint : (∫ x in -y..y, E x) = 2 * S ζ := by
    have hz := sphereBesselIdentity hy 0 ζ (by simpa using pow_ne_zero 2 hζ₀)
    simpa [sphereBessel_zeroFactor, mul_one, principalSqrt_zeta_sq hζ, E, S, mul_div_assoc]
      using hz
  have hinner (t : ℝ) : (∫ x in -y..y, F x t) = 2 * A t * (S (W t) - S ζ) := by
    have hB : Continuous (sphereBesselFactor y (b * t)) := hcontB.comp (by fun_prop)
    have hE : Continuous E := by dsimp [E]; fun_prop
    have hscale : ((b * t : ℝ) : ℂ) ^ 2 = ((4 * Real.pi ^ 2 / 3 * t ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow]
      congr 1
      rw [mul_pow, show b ^ 2 = 4 * Real.pi ^ 2 / 3 by
        dsimp [b]
        rw [div_pow, Real.sq_sqrt (by norm_num), mul_pow]
        ring]
    have hnon : ζ ^ 2 + ((b * t : ℝ) : ℂ) ^ 2 ≠ 0 := by
      rw [hscale]
      exact Complex.slitPlane_ne_zero (outerRoot_slit hζ (by positivity))
    have h := sphereBesselIdentity hy (b * t) ζ hnon
    dsimp only at h
    rw [hscale] at h
    have hh : (∫ x in -y..y, E x * sphereBesselFactor y (b * t) x) = 2 * S (W t) := by
      simpa only [W, S, E, mul_div_assoc] using h
    have hi : IntervalIntegrable (fun x => E x * sphereBesselFactor y (b * t) x) volume (-y) y :=
      (hE.mul hB).intervalIntegrable _ _
    calc
      _ = A t * ((∫ x in -y..y, E x * sphereBesselFactor y (b * t) x) -
          ∫ x in -y..y, E x) := by
        rw [← intervalIntegral.integral_sub hi
          (hE.intervalIntegrable _ _), ← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        simp only [F]
        ring
      _ = _ := by rw [hh, hzeroint]; ring
  rw [hfirst, intervalIntegral_intervalIntegral_swap hFint, kernelTransformIntegralFormula]
  simp_rw [hinner, mul_assoc (2 : ℂ), intervalIntegral.integral_const_mul]
  dsimp only [S, W, A]
  ring

/-- Equation (70) for the exact compactly supported kernel. -/
theorem kernelTransformEndpoints {y : ℝ} {ζ : ℂ} (hy : 0 < y) (hζ : 0 < ζ.re) :
    kernelTransform y ζ + (Real.pi : ℂ) ^ 3 * Complex.sinh ((y : ℂ) * ζ) / (18 * ζ) =
      (1 / (8 * (Real.pi : ℂ))) *
        (kernelEndpoint y (ζ ^ 2 + ((4 * Real.pi ^ 2 / 3 : ℝ) : ℂ))
          (ζ ^ 2 + ((4 * Real.pi ^ 2 / 3 : ℝ) : ℂ)).sqrt -
        kernelEndpoint y (ζ ^ 2 + ((4 * Real.pi ^ 2 / 3 : ℝ) : ℂ)) ζ) := by
  rw [kernelTransformIntegral hy.le hζ, kernelTransformIntegral_endpoints hy.ne' hζ]

end DurfeeCCS.Step10
