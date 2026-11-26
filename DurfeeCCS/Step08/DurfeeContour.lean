module

public import DurfeeCCS.Step06.DurfeeAngle
public import DurfeeCCS.Step06.DurfeePairedAngle
public import DurfeeCCS.Step08.ContourSplit
public import DurfeeCCS.Step08.LogArcMean
public import DurfeeCCS.Step08.SaddleAssembly
public import DurfeeCCS.Step08.SaddleOuterArc

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The Durfee contour and its split against the Bessel model in (40). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06

def durfeeExponentialMean (r u v : ℝ) : ℂ :=
  angularAverage (fun θ => exp (pairedLog r θ (verticalPoint u v)) - 1)

theorem continuous_durfeeExponentialMean {r u : ℝ} (hr : |r| ≤ 1) (hu : 0 < u) :
    Continuous (durfeeExponentialMean r u) := by
  have hf : Continuous (fun p : ℝ × ℝ => exp (pairedLog r p.2 (verticalPoint u p.1)) - 1) :=
    (Complex.continuous_exp.comp (continuous_pairedLog_vertical r hr hu)).sub continuous_const
  unfold durfeeExponentialMean angularAverage
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun v θ => exp (pairedLog r θ (verticalPoint u v)) - 1) hf _ _)

theorem ofReal_durfeeNegativeValue (n : ℕ) (r : ℝ) :
    (durfeeNegativeValue n r : ℂ) = (DurfeeCCS.durfeePolynomialComplex n).eval (-(r : ℂ) ^ 2) := by
  simp only [durfeeNegativeValue, DurfeeCCS.durfeePolynomialComplex, Polynomial.eval_map]
  have h := Polynomial.hom_eval₂ (DurfeeCCS.durfeePolynomial n) (Int.castRingHom ℝ)
    Complex.ofRealHom (-(r ^ 2))
  have hg : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext z
    simp
  change ((Polynomial.eval₂ (Int.castRingHom ℝ) (-(r ^ 2)) (DurfeeCCS.durfeePolynomial n) : ℝ) : ℂ) =
    Polynomial.eval₂ (Int.castRingHom ℂ) (-(r : ℂ)^2) (DurfeeCCS.durfeePolynomial n)
  rw [hg] at h
  convert h using 2
  rw [map_neg, map_pow]
  rfl

theorem integral_exp_verticalPoint_nat {n : ℕ} (hn : 0 < n) (u : ℝ) :
    (∫ v : ℝ in -Real.pi..Real.pi, exp ((n : ℂ) * verticalPoint u v)) = 0 := by
  have heq (v : ℝ) : exp ((n : ℂ) * verticalPoint u v) =
      exp ((n : ℂ) * (u : ℂ)) * exp (((n : ℤ) : ℂ) * I * (v : ℂ)) := by
    rw [← exp_add, verticalPoint]
    push_cast
    congr 1
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, integral_integer_mode, ite_eq_right, mul_zero]
  exact_mod_cast (Nat.ne_of_gt hn)

set_option maxHeartbeats 600000 in
theorem durfeeNegativeValue_eq_contour {n : ℕ} (hn : 0 < n) {r u : ℝ}
    (hr : |r| ≤ 1) (hu : 0 < u) :
    (durfeeNegativeValue n r : ℂ) =
      angularAverage (fun v => exp ((n : ℂ) * verticalPoint u v) * durfeeExponentialMean r u v) := by
  rw [ofReal_durfeeNegativeValue, durfeePolynomials_angular_coefficient n r u hu]
  have heq (v : ℝ) :
      durfeeAnalyticF (-(r : ℂ) ^ 2) (exp (- verticalPoint u v)) =
        durfeeExponentialMean r u v + 1 := by
    have hp : Continuous (fun θ : ℝ => (v, θ)) := continuous_const.prodMk continuous_id
    have hl : Continuous (fun θ => pairedLog r θ (verticalPoint u v)) := by
      change Continuous ((fun p : ℝ × ℝ => pairedLog r p.2 (verticalPoint u p.1)) ∘ fun θ => (v, θ))
      exact (continuous_pairedLog_vertical r hr hu).comp hp
    have hcont : Continuous (fun θ => exp (pairedLog r θ (verticalPoint u v))) :=
      Complex.continuous_exp.comp hl
    unfold durfeeExponentialMean
    rw [angularAverage_sub (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      angularAverage_const, sub_add_cancel]
    unfold angularAverage
    have hζ : 0 < (verticalPoint u v).re := by simpa using hu
    rw [durfeeAnalyticF_eq_pairedAngle r hζ]
    simp_rw [exp_pairedLog r _ hr hζ]
  change (2 * Real.pi : ℂ)⁻¹ * (∫ v : ℝ in -Real.pi..Real.pi,
    exp ((n : ℂ) * verticalPoint u v) *
      durfeeAnalyticF (-(r : ℂ) ^ 2) (exp (- verticalPoint u v))) = _
  have hident (v : ℝ) :
      exp ((n : ℂ) * verticalPoint u v) *
        durfeeAnalyticF (-(r : ℂ) ^ 2) (exp (- verticalPoint u v)) =
      exp ((n : ℂ) * verticalPoint u v) * durfeeExponentialMean r u v +
        exp ((n : ℂ) * verticalPoint u v) := by rw [heq, mul_add, mul_one]
  simp_rw [hident]
  have hcont : Continuous (fun v => exp ((n : ℂ) * verticalPoint u v)) := by
    unfold verticalPoint
    fun_prop
  have hf : IntervalIntegrable (fun v => exp ((n : ℂ) * verticalPoint u v) *
      durfeeExponentialMean r u v) volume (-Real.pi) Real.pi :=
    (hcont.mul (continuous_durfeeExponentialMean hr hu)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hf (hcont.intervalIntegrable _ _),
    integral_exp_verticalPoint_nat hn, add_zero]
  rfl

/-- The three contour errors in (40), with the full real-line Bessel model. -/
theorem saddle_contour_difference_le {n : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) :
    let u := saddleU n r
    let ω := saddleOmega n r
    let s := Icc (-(16 * u)) (16 * u)
    let t := Icc (-Real.pi) Real.pi
    |durfeeNegativeValue n r - saddleBesselAverage n r| ≤
      Real.exp ω / (2 * Real.pi) *
        ((∫ v in s, ‖durfeeExponentialMean r u v - saddleExponentialMean r u v‖) +
         (∫ v in t \ s, ‖durfeeExponentialMean r u v‖) +
         (∫ v in sᶜ, ‖saddleExponentialMean r u v‖)) := by
  dsimp only
  let u := saddleU n r
  let ω := saddleOmega n r
  let s := Icc (-(16 * u)) (16 * u)
  let t := Icc (-Real.pi) Real.pi
  let E (v : ℝ) := exp ((n : ℂ) * verticalPoint u v)
  let L := durfeeExponentialMean r u
  let G := saddleExponentialMean r u
  have hn' : 0 < n := by omega
  have hu : 0 < u := saddleU_pos hn' hr
  have hr' : |r| ≤ 1 := by rwa [abs_of_pos hr]
  have hub := saddleU_lt_bound hn hr hr₁
  have hπ := Real.pi_gt_three
  have hsub : s ⊆ t := Icc_subset_Icc (by linarith only [hπ,hub]) (by linarith only [hπ,hub])
  have hE : Continuous E := by dsimp [E, verticalPoint]; fun_prop
  have hL : Continuous L := continuous_durfeeExponentialMean hr' hu
  have hsplit := norm_contour_difference_le (A := fun v => E v * L v)
    (B := fun v => E v * G v) measurableSet_Icc measurableSet_Icc hsub
    ((hE.mul hL).integrableOn_Icc)
    (by simpa only [Complex.ofReal_natCast] using integrable_saddleExponentialMean hr' hu (n : ℝ))
  have hcoef : (durfeeNegativeValue n r : ℂ) =
      (2 * Real.pi : ℂ)⁻¹ * ∫ v in t, E v * L v := by
    rw [durfeeNegativeValue_eq_contour hn' hr' hu, angularAverage]
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_Icc_eq_integral_Ioc]
  have hQ : (saddleBesselAverage n r : ℂ) =
      (2 * Real.pi : ℂ)⁻¹ * ∫ v, E v * G v := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (integral_saddleExponentialMean_eq_saddleBesselAverage hr' hu hn').symm
  have hW (v : ℝ) : ‖E v‖ = Real.exp ω := by
    change ‖exp ((n : ℂ) * verticalPoint u v)‖ = _
    rw [norm_exp_nat_verticalPoint, saddleU_mul_n hn']
  have hfactor : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_of_nonneg (by positivity)]
  simp_rw [← mul_sub, norm_mul, hW, integral_const_mul] at hsplit
  change |durfeeNegativeValue n r - saddleBesselAverage n r| ≤
    Real.exp ω / (2 * Real.pi) *
      ((∫ v in s, ‖L v - G v‖) + (∫ v in t \ s, ‖L v‖) + ∫ v in sᶜ, ‖G v‖)
  rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub,
    hcoef, hQ, ← mul_sub, norm_mul, hfactor]
  refine (mul_le_mul_of_nonneg_left hsplit (by positivity)).trans_eq ?_
  ring

end DurfeeCCS.Step08
