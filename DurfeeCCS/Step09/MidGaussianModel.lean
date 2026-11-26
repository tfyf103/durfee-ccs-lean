module

public import DurfeeCCS.Step09.MidPhaseShape
public import DurfeeCCS.Step09.MidModelBase
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact evaluation of the central model Gaussian in (55). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory DurfeeCCS.Step06 DurfeeCCS.Step08

def midGaussianModel (n : ℕ) (r : ℝ) : ℂ :=
  (midU n r / (4*Real.pi^2) : ℝ) *
    ∫ η in (0:ℝ)..(3/2), ∫ χ : ℝ, exp (midGaussianExponent n r η χ)

theorem midCurvature_re_pos {r : ℝ} (hr : 0 < r) : 0 < (midCurvature r).re := by
  rw [(saddleBesselSlope_components r).1]
  positivity

theorem re_midGaussianRate_pos {n : ℕ} (hn : 0 < n) {r η : ℝ} (hr : 0 < r) (hη : 0 ≤ η) :
    0 < (midCurvature r / midEtaPoint n r η).re := by
  rw [re_div_midEtaPoint hn hr, (saddleBesselSlope_components r).1, (saddleBesselSlope_components r).2]
  have hu := saddleU_pos hn hr
  exact div_pos (add_pos_of_pos_of_nonneg (by positivity) (by positivity)) (by positivity)

theorem integral_midGaussian_inner {n : ℕ} (hn : 0 < n) {r η : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) :
    (∫ χ : ℝ, exp (midGaussianExponent n r η χ)) =
      exp ((n : ℂ)*midEtaPoint n r η + saddleS r^2/midEtaPoint n r η) *
        ((Real.sqrt (Real.pi * midU n r) : ℂ) / (midCurvature r).sqrt) *
        (midModelZ η).sqrt := by
  let ζ := midEtaPoint n r η
  let c := midCurvature r
  let E := exp ((n : ℂ)*ζ + saddleS r^2/ζ)
  have hζ := midEtaPoint_ne_zero hn hr η
  have hu := saddleU_pos hn hr
  have hc := midCurvature_re_pos hr
  have hcn := Complex.ne_zero_of_re_pos hc
  have hsum (χ : ℝ) : exp (midGaussianExponent n r η χ) =
      E * exp (-(c/ζ)*(χ : ℂ)^2) := by
    rw [← exp_add]
    unfold midGaussianExponent
    congr 1
    ring
  have hzh : 0 < ζ.re := by simpa [ζ] using hu
  have hgauss := integral_gaussian_complex (re_midGaussianRate_pos hn hr hη)
  rw [one_div, ← Complex.sqrt] at hgauss
  simp_rw [hsum]
  rw [integral_const_mul, hgauss]
  change E * ((Real.pi : ℂ)/(c/ζ)).sqrt =
    E * ((Real.sqrt (Real.pi * midU n r) : ℂ) / c.sqrt) * (midModelZ η).sqrt
  have harg : (Real.pi : ℂ)/(c/ζ) = ζ * ((Real.pi : ℂ)/c) := by
    field_simp [hcn,hζ]
  have hpc : 0 < ((Real.pi : ℂ)/c).re := by
    rw [div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re]
    exact mul_pos Real.pi_pos (div_pos hc (Complex.normSq_pos.mpr hcn))
  have hZ : ζ = (midU n r : ℂ) * midModelZ η := by
    unfold ζ midEtaPoint midModelZ verticalPoint
    norm_num
  rw [harg, sqrt_mul_right_half_planes hzh hpc, hZ, sqrt_ofReal_mul _ hu.le,
    sqrt_div_right_half_plane _ Real.pi_pos.le hc, Real.sqrt_mul Real.pi_pos.le, Complex.ofReal_mul]
  ring

theorem integral_midGaussian_inner_eq_model {n : ℕ} (hn : 0 < n) {r η : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) :
    (∫ χ : ℝ, exp (midGaussianExponent n r η χ)) =
      (exp (2*(Real.sqrt n : ℂ)*saddleS r) *
        ((Real.sqrt (Real.pi*midU n r) : ℂ)/(midCurvature r).sqrt)) *
        midModelIntegrand (midOmega n r) (midSlope r) η := by
  rw [integral_midGaussian_inner hn hr hη, mid_saddle_exponent_identity hn hr, Complex.exp_sub,
    midModelIntegrand]
  have hZ : midModelZ η = 1+(η : ℂ)*I := by simp [midModelZ, verticalPoint]
  rw [hZ]
  push_cast
  rw [show -(midOmega n r : ℂ) * (↑η-↑(midSlope r))^2/(1+(η : ℂ)*I) =
    -((midOmega n r : ℂ)*(↑η-↑(midSlope r))^2/(1+(η : ℂ)*I)) by ring,Complex.exp_neg]
  ring

theorem midGaussianModel_eq_factor {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    midGaussianModel n r =
      (midU n r / (4*Real.pi^2) : ℝ) * exp (2*(Real.sqrt n : ℂ)*saddleS r) *
        ((Real.sqrt (Real.pi*midU n r) : ℂ)/(midCurvature r).sqrt) *
        midModelJ (midOmega n r) (midSlope r) := by
  let C := exp (2*(Real.sqrt n : ℂ)*saddleS r) *
        ((Real.sqrt (Real.pi*midU n r) : ℂ)/(midCurvature r).sqrt)
  unfold midGaussianModel midModelJ
  have h :
      (∫ η in (0:ℝ)..(3/2), ∫ χ : ℝ, exp (midGaussianExponent n r η χ)) =
      ∫ η in (0:ℝ)..(3/2), C * midModelIntegrand (midOmega n r) (midSlope r) η := by
    apply intervalIntegral.integral_congr
    intro η hη
    rw [Set.uIcc_of_le (by norm_num)] at hη
    exact integral_midGaussian_inner_eq_model hn hr hη.1
  rw [h, intervalIntegral.integral_const_mul]
  unfold C
  ring

theorem saddleS_eq_re_mul_midModelZ {r : ℝ} (hr : 0 < r) :
    saddleS r = ((saddleS r).re : ℂ) * midModelZ (midSlope r) := by
  have ha : 0 < (saddleS r).re := (saddleS_components hr).1.trans (saddleS_components hr).2
  conv_lhs => rw [← saddleS_real_imag r]
  unfold midModelZ verticalPoint midSlope
  push_cast
  field_simp [(Complex.ofReal_ne_zero.mpr ha.ne')]

theorem midGaussianModel_eq_prediction {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    midGaussianModel n r =
      (saddleAmplitude n r / 2 : ℝ) * exp ((saddlePhase n r : ℂ)*I) *
        (Real.sqrt (midOmega n r / Real.pi) : ℂ) *
        midModelJ (midOmega n r) (midSlope r) / midModelZ (midSlope r) := by
  let u := midU n r
  let a := (saddleS r).re
  let x := Real.sqrt n
  let c := (midCurvature r).sqrt
  let Z := midModelZ (midSlope r)
  have hu : 0 < u := saddleU_pos hn hr
  have hx : 0 < x := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hZ : Z ≠ 0 := midModelZ_ne_zero _
  have hc : c ≠ 0 := by
    intro h
    have hp := principalSqrt_sq (midCurvature r)
    change c^2 = midCurvature r at hp
    rw [h,zero_pow (by decide : 2 ≠ 0)] at hp
    exact (Complex.ne_zero_of_re_pos (midCurvature_re_pos hr)) hp.symm
  have hrad : Real.sqrt (midOmega n r / Real.pi) = x * Real.sqrt u / Real.sqrt Real.pi := by
    change Real.sqrt (saddleOmega n r / Real.pi) = _
    rw [← saddleU_mul_n hn, Real.sqrt_div (by positivity), Real.sqrt_mul (Nat.cast_nonneg n)]
  have hnx : (n : ℂ) = (x : ℂ)^2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have hmul : ↑u * (x : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    change (a/x)*x = a
    exact div_mul_cancel₀ _ hx.ne'
  have hπs : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hπs₀ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [midGaussianModel_eq_factor hn hr, hrad, Real.sqrt_mul Real.pi_pos.le]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_pow]
  have hp := saddleBesselLead_eq_polar hn hr
  rw [show (saddleAmplitude n r : ℂ)/2 * exp ((saddlePhase n r : ℂ)*I) =
    ((saddleAmplitude n r : ℂ) * exp ((saddlePhase n r : ℂ)*I))/2 by ring,
    ← hp, saddleS_eq_re_mul_midModelZ hr]
  change ((u : ℂ)/(4*(Real.pi : ℂ)^2)) *
      exp (2*(x : ℂ)*((a : ℂ)*Z)) * (((Real.sqrt Real.pi : ℂ)*(Real.sqrt u : ℂ))/c) * _ =
    ((((a : ℂ)*Z) * exp (2*(x : ℂ)*((a : ℂ)*Z)) /
      (2*(Real.pi : ℂ)*(n : ℂ)*c))/2) * (((x : ℂ)*(Real.sqrt u : ℂ))/(Real.sqrt Real.pi : ℂ)) * _ / Z
  rw [← hmul, hnx]
  field_simp [hπ,hc,hZ,hπs₀,(Complex.ofReal_ne_zero.mpr hx.ne')]
  ring_nf
  rw [hπs]
  ring

end DurfeeCCS.Step09
