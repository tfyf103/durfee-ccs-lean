module

public import DurfeeCCS.Step09.MidMajorEtaBudget
public import DurfeeCCS.Step09.MidMajorGaussian
public import DurfeeCCS.Step09.MidPhase

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Gaussian normalization for the main angular contribution. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

/-- Absolute Gaussian mass normalized by the saddle amplitude after the χ integration. -/
def midMajorWeight (t r ρ η : ℝ) : ℝ :=
  Real.sqrt (t / Real.pi) * thetaFourthRoot (1 + r⁻¹ ^ 2) *
    Real.sqrt (1 + η ^ 2) * Real.exp (-t * midMajorGap ρ η) / Real.sqrt (1 + ρ ^ 2)

theorem thetaFourthRoot_nonneg (x : ℝ) : 0 ≤ thetaFourthRoot x := Real.sqrt_nonneg _

theorem thetaFourthRoot_pos {x : ℝ} (hx : 0 < x) : 0 < thetaFourthRoot x :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx)

theorem thetaFourthRoot_mul {x y : ℝ} (hx : 0 ≤ x) :
    thetaFourthRoot (x * y) = thetaFourthRoot x * thetaFourthRoot y := by
  unfold thetaFourthRoot
  rw [Real.sqrt_mul hx, Real.sqrt_mul (Real.sqrt_nonneg x)]

theorem thetaFourthRoot_four {x : ℝ} (hx : 0 ≤ x) : thetaFourthRoot x ^ 4 = x := by
  unfold thetaFourthRoot
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt hx]

theorem thetaFourthRoot_mono : Monotone thetaFourthRoot :=
  fun _ _ h => Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

theorem midMajor_saddleAmplitude_eq {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    saddleAmplitude n r =
      (saddleS r).re * Real.sqrt (1 + midSlope r ^ 2) * thetaFourthRoot (1 + r⁻¹ ^ 2) *
        Real.exp (2 * midOmega n r) / (2 * Real.pi * n) := by
  let s := saddleS r
  let a := s.re
  let b := s.im
  have ha := (saddleS_components hr).1.trans (saddleS_components hr).2
  change 0 < a at ha
  have hs : ‖s‖ = a * Real.sqrt (1 + midSlope r ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    change √(a ^ 2 + b ^ 2) = a * √(1 + (b / a) ^ 2)
    rw [show a ^ 2 + b ^ 2 = a ^ 2 * (1 + (b / a) ^ 2) by field_simp]
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have hrad : (1 + r ^ 2) ^ (1 / 4 : ℝ) =
      Real.sqrt r * thetaFourthRoot (1 + r⁻¹ ^ 2) := by
    have hpow : thetaFourthRoot (1 + r ^ 2) = (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
      simpa only [pow_one, Nat.cast_one] using thetaFourthRoot_pow (1 + r ^ 2) (by positivity) 1
    rw [← hpow]
    rw [show 1 + r ^ 2 = r ^ 2 * (1 + r⁻¹ ^ 2) by field_simp; ring,
      thetaFourthRoot_mul (sq_nonneg r)]
    unfold thetaFourthRoot
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]
  unfold saddleAmplitude
  change ‖s‖ * _ * _ / _ = a * _ * _ * _ / _
  rw [hs, hrad]
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [show midOmega n r = a * Real.sqrt n from rfl]
  rw [show 2 * a * Real.sqrt n = 2 * (a * Real.sqrt n) by ring]
  field_simp

theorem midMajor_weight_eq {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    let u := midU n r
    let t := midOmega n r
    let ρ := midSlope r
    let A := (1 / u) * r ^ 2 / ((1 + r ^ 2) * (1 + η ^ 2))
    u / (4 * Real.pi ^ 2) * (Real.exp (2 * t - t * midMajorGap ρ η) *
        Real.sqrt (Real.pi / A)) =
      saddleAmplitude n r / 2 * midMajorWeight t r ρ η := by
  dsimp only
  let a := (saddleS r).re
  let x := Real.sqrt (n : ℝ)
  let u := midU n r
  let t := midOmega n r
  let ρ := midSlope r
  have hu : 0 < u := saddleU_pos hn hr
  have ht : 0 < t := saddleOmega_pos hn hr
  have hx : 0 < x := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have ha := (saddleS_components hr).1.trans (saddleS_components hr).2
  change 0 < a at ha
  have hx₂ : x ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hu' : u = a / x := rfl
  have ht' : t = a * x := rfl
  have hmass : Real.pi / ((1 / u) * r ^ 2 / ((1 + r ^ 2) * (1 + η ^ 2))) =
      (Real.pi * u) * (1 + r⁻¹ ^ 2) * (1 + η ^ 2) := by field_simp; ring
  have hscale : u / (4 * Real.pi ^ 2) * Real.sqrt (Real.pi * u) =
      a / (4 * Real.pi * (n : ℝ)) * Real.sqrt (t / Real.pi) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      hu', ht', ← hx₂]
    field_simp
  have hheight : Real.sqrt (1 + r⁻¹ ^ 2) = thetaFourthRoot (1 + r⁻¹ ^ 2) ^ 2 :=
    (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
  rw [hmass, Real.sqrt_mul (by positivity : 0 ≤ Real.pi * u * (1 + r⁻¹ ^ 2)),
    Real.sqrt_mul (by positivity : 0 ≤ Real.pi * u), ← mul_assoc _ _ (Real.sqrt (1 + η ^ 2)),
    hheight]
  rw [midMajor_saddleAmplitude_eq hn hr]
  unfold midMajorWeight
  change u / (_ : ℝ) * _ = _
  rw [sub_eq_add_neg, Real.exp_add]
  have hh : Real.sqrt (1 + ρ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  calc
    _ = (u / (4 * Real.pi ^ 2) * Real.sqrt (Real.pi * u)) *
        (Real.exp (2 * t) * Real.exp (-(t * midMajorGap ρ η)) *
          thetaFourthRoot (1 + r⁻¹ ^ 2) ^ 2 * Real.sqrt (1 + η ^ 2)) := by ring
    _ = _ := by
      rw [hscale]
      change _ = (a * Real.sqrt (1 + ρ ^ 2) * thetaFourthRoot (1 + r⁻¹ ^ 2) *
        Real.exp (2 * t) / (2 * Real.pi * n)) / 2 *
        (Real.sqrt (t / Real.pi) * thetaFourthRoot (1 + r⁻¹ ^ 2) *
          Real.sqrt (1 + η ^ 2) * Real.exp (-t * midMajorGap ρ η) / Real.sqrt (1 + ρ ^ 2))
      rw [show -(t * midMajorGap ρ η) = -t * midMajorGap ρ η by ring]
      field_simp
      ring

/-- The Gaussian weight on the central interval before inserting the radius cap. -/
theorem midMajor_weight_integral_le {t r ρ : ℝ} (ht : 0 < t) :
    (∫ η in (0 : ℝ)..(3 / 2), midMajorWeight t r ρ η) ≤
      (13 / 4) * thetaFourthRoot (1 + r⁻¹ ^ 2) := by
  let C := Real.sqrt (t / Real.pi) * thetaFourthRoot (1 + r⁻¹ ^ 2) * Real.sqrt (13 / 4)
  let d := t / (13 / 4)
  let G (η : ℝ) := Real.exp (-d * (η - ρ) ^ 2)
  have hC : 0 ≤ C := by
    unfold C
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (thetaFourthRoot_nonneg _))
      (Real.sqrt_nonneg _)
  have hd : 0 < d := by unfold d; positivity
  have hpoint (η : ℝ) (hη : η ∈ Icc (0 : ℝ) (3 / 2)) :
      midMajorWeight t r ρ η ≤ C * G η := by
    have hη₂ : η ^ 2 ≤ 9 / 4 := by
      have h := pow_le_pow_left₀ hη.1 hη.2 2
      norm_num at h
      exact h
    have hs : Real.sqrt (1 + η ^ 2) ≤ Real.sqrt (13 / 4) := Real.sqrt_le_sqrt (by linarith)
    have hρ : 1 ≤ Real.sqrt (1 + ρ ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ρ])
    have hgap : (η - ρ) ^ 2 / (13 / 4) ≤ midMajorGap ρ η := by
      unfold midMajorGap
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    unfold midMajorWeight
    apply (div_le_self (by
      have := thetaFourthRoot_nonneg (1 + r⁻¹ ^ 2)
      positivity) hρ).trans
    unfold C G
    have hpre := mul_nonneg (Real.sqrt_nonneg (t / Real.pi)) (thetaFourthRoot_nonneg (1 + r⁻¹ ^ 2))
    refine mul_le_mul (mul_le_mul_of_nonneg_left hs hpre) (Real.exp_le_exp.mpr ?_)
      (Real.exp_pos _).le (mul_nonneg hpre (Real.sqrt_nonneg _))
    have hh := neg_le_neg (mul_le_mul_of_nonneg_left hgap ht.le)
    dsimp only [d]
    simpa only [neg_mul, show -(t / (13 / 4)) * (η - ρ) ^ 2 =
      -t * ((η - ρ) ^ 2 / (13 / 4)) by ring] using hh
  have hG := integrable_exp_neg_mul_sq hd |>.comp_sub_right ρ
  have hcont : Continuous (midMajorWeight t r ρ) := by
    unfold midMajorWeight midMajorGap
    fun_prop (disch := intro _; positivity)
  have hGc : Continuous (fun η => C * G η) := by unfold G; fun_prop
  refine (intervalIntegral.integral_mono_on (by norm_num)
    (hcont.intervalIntegrable _ _) (hGc.intervalIntegrable _ _) hpoint).trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hwhole : (∫ η in (0 : ℝ)..(3 / 2), G η) ≤ ∫ η : ℝ, G η := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    exact setIntegral_le_integral hG (ae_of_all _ fun η => Real.exp_nonneg _)
  apply (mul_le_mul_of_nonneg_left hwhole hC).trans_eq
  unfold G
  rw [integral_sub_right_eq_self (fun z : ℝ => Real.exp (-d * z ^ 2)) ρ, integral_gaussian d]
  unfold C d
  have hpi := Real.pi_pos
  calc
    _ = thetaFourthRoot (1 + r⁻¹ ^ 2) * Real.sqrt
        ((t / Real.pi) * (13 / 4) * (Real.pi / (t / (13 / 4)))) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ t / Real.pi * (13 / 4)),
        Real.sqrt_mul (by positivity : 0 ≤ t / Real.pi)]
      ring
    _ = _ := by rw [show (t / Real.pi) * (13 / 4) * (Real.pi / (t / (13 / 4))) =
        (13 / 4 : ℝ)^2 by field_simp, Real.sqrt_sq_eq_abs]; norm_num; ring

theorem midMajor_central_constant_le :
    (13 / 4 : ℝ) ≤ (243 / 100) * thetaFourthRoot (13 / 4) := by
  apply (pow_le_pow_iff_left₀ (by norm_num) (by
    exact mul_nonneg (by norm_num) (thetaFourthRoot_nonneg _)) (n := 4) (by decide)).mp
  rw [mul_pow, thetaFourthRoot_four (by norm_num)]
  norm_num

end DurfeeCCS.Step09
