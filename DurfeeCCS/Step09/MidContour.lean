module

public import DurfeeCCS.Step09.MidContourDefs
public import DurfeeCCS.Step09.MidPoissonVertical
public import DurfeeCCS.Step09.MidPoissonEuler

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Modular normalization of (47) and splitting the coefficient contour. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step08

def midPoissonWeight (n : ℕ) (u v : ℝ) : ℂ :=
  let ζ := verticalPoint u v
  exp ((n : ℂ)*ζ) * ((2*Real.pi : ℂ)/(ζ*eulerProduct ζ^2))

theorem continuous_midPoissonWeight (n : ℕ) {u : ℝ} (hu : 0 < u) :
    Continuous (midPoissonWeight n u) := by
  have hζ : Continuous (verticalPoint u) := by unfold verticalPoint; fun_prop
  have hne (v : ℝ) : eulerProduct (verticalPoint u v) ≠ 0 :=
    eulerProduct_ne_zero_right (by simpa using hu)
  unfold midPoissonWeight
  apply Continuous.mul (Complex.continuous_exp.comp (continuous_const.mul hζ))
  exact continuous_const.div (hζ.mul ((continuous_eulerProduct_vertical hu).pow 2))
    (fun v => mul_ne_zero (verticalPoint_ne_zero hu v) (pow_ne_zero 2 (hne v)))

theorem midEta_modular_factor {ζ : ℂ} (hζ : 0 < ζ.re) :
    (2*Real.pi : ℂ)/(ζ*eulerProduct ζ ^ 2) =
      exp (-ζ/12 + (Real.pi : ℂ)^2/(3*ζ)) / eulerProduct (midEtaTransform ζ)^2 := by
  let ζ' := midEtaTransform ζ
  let c := (2*Real.pi : ℂ)
  let T := ζ/12 - (Real.pi : ℂ)^2/(3*ζ)
  have hπ : c ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hz : ζ ≠ 0 := Complex.ne_zero_of_re_pos hζ
  have hE : ζ * eulerProduct ζ^2 = c * exp T * eulerProduct ζ'^2 := by
    have hmain := eulerProduct_modular hζ
    change eulerProduct ζ = (c/ζ).sqrt *
      exp (ζ/24 - (Real.pi : ℂ)^2/(6*ζ)) * eulerProduct ζ' at hmain
    rw [hmain,mul_pow,mul_pow,principalSqrt_sq,← exp_nat_mul]
    change ζ * (c/ζ * exp ((2 : ℂ)*(ζ/24-(Real.pi : ℂ)^2/(6*ζ))) *
      eulerProduct ζ'^2) = _
    have ht : (2 : ℂ)*(ζ/24-(Real.pi : ℂ)^2/(6*ζ)) = T := by
      unfold T
      field_simp [hz]
      ring
    rw [ht, ← mul_assoc, ← mul_assoc, mul_div_cancel₀ _ hz]
  change c / (ζ * eulerProduct ζ ^ 2) = _ / eulerProduct ζ'^2
  rw [hE,div_eq_mul_inv,mul_inv_rev,mul_inv_rev]
  have hT : -ζ/12 + (Real.pi : ℂ)^2/(3*ζ) = -T := by dsimp [T]; ring
  rw [hT,Complex.exp_neg, div_eq_mul_inv]
  calc
    _ = (c * c⁻¹) * ((exp T)⁻¹ * (eulerProduct ζ'^2)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hπ,one_mul]

theorem midIntegrand_eq_midPoisson {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 ≤ r)
    (p : ℤ) (η χ : ℝ) :
    midIntegrand n r p η χ =
      midPoissonWeight n (midU n r) (η*midU n r) *
        midPoissonMode r (verticalPoint (midU n r) (η*midU n r)) p χ := by
  let u := midU n r
  let ζ := midEtaPoint n r η
  have he : verticalPoint (midU n r) (η*midU n r) = ζ := by
    rw [mul_comm η (midU n r)]
    exact (midEtaPoint_eq_vertical n r η).symm
  have hζ : 0 < ζ.re := by simpa [ζ] using saddleU_pos hn (show 0 < r by linarith)
  have hmod := midEta_modular_factor hζ
  simp only [midPoissonWeight, he, hmod]
  rw [midPoissonMode, ← exp_pairedLog _ _ (midModeRadius_abs_le_one hr p) hζ]
  unfold midIntegrand midMultiplier
  change exp ((n : ℂ)*ζ + _/ζ) * (exp (-ζ/12) / _ * exp (_/ζ - _)) = _
  have ha :
      exp ((n : ℂ)*ζ + midPhase r p χ / ζ) * exp (-ζ/12) *
        exp (saddleG (midModeRadius r p) χ / ζ - pairedLog (midModeRadius r p) χ ζ) =
      exp ((n : ℂ)*ζ) * exp (-ζ/12+(Real.pi : ℂ)^2/(3*ζ)) *
        exp (((Real.log r : ℂ)+(midFrequency p : ℂ)*I)^2/ζ) *
        exp (-(χ : ℂ)^2/ζ) * (exp (pairedLog (midModeRadius r p) χ ζ))⁻¹ := by
    rw [← exp_neg,← exp_add,← exp_add,← exp_add,← exp_add,← exp_add,← exp_add]
    congr 1
    unfold midPhase
    ring
  calc
    _ = (exp ((n : ℂ)*ζ + midPhase r p χ / ζ) * exp (-ζ/12) *
        exp (saddleG (midModeRadius r p) χ / ζ - pairedLog (midModeRadius r p) χ ζ)) *
          (eulerProduct (midEtaTransform ζ)^2)⁻¹ := by ring
    _ = _ := by rw [ha]; ring

theorem midContribution_eq_v_integral {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 ≤ r)
    (p : ℤ) (l h : ℝ) :
    let u := midU n r
    midContribution n r p l h = ((2*Real.pi : ℂ)^2)⁻¹ *
      ∫ v in l*u..h*u, midPoissonWeight n u v * ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ := by
  dsimp only
  let u := midU n r
  have hu := saddleU_pos hn (show 0 < r by linarith)
  let f (v : ℝ) := midPoissonWeight n u v * ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ
  have hpoint (η : ℝ) : (∫ χ : ℝ, midIntegrand n r p η χ) = f (η*u) := by
    simp_rw [midIntegrand_eq_midPoisson hn hr]
    rw [integral_const_mul]
  unfold midContribution
  simp_rw [hpoint]
  rw [intervalIntegral.integral_comp_mul_right f hu.ne', Complex.real_smul]
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_inv]
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  change (u : ℂ) / (4*(Real.pi : ℂ)^2) * ((u : ℂ)⁻¹ * _) = _
  rw [← mul_assoc, div_mul_eq_mul_div, mul_inv_cancel₀ hu']
  congr 1
  ring

theorem hasSum_midContribution {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 ≤ r) (l h : ℝ) :
    let u := midU n r
    HasSum (fun p : ℤ => midContribution n r p l h)
      ((2*Real.pi : ℂ)⁻¹ * ∫ v in l*u..h*u, midDurfeeLine n r v) := by
  dsimp only
  let u := midU n r
  have hu := saddleU_pos hn (show 0 < r by linarith)
  have hh := (hasSum_intervalIntegral_midPoissonMode hr hu
    (continuous_midPoissonWeight n hu) (l*u) (h*u)).mul_left (((2*Real.pi : ℂ)^2)⁻¹)
  have hsum (v : ℝ) : midPoissonWeight n u v *
      (∑' p : ℤ, ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ) =
      (2*Real.pi : ℂ) * midDurfeeLine n r v := by
    dsimp only [midPoissonWeight,midDurfeeLine]
    rw [durfeeAnalyticF_midPoisson hr (by simpa using hu : 0 < (verticalPoint u v).re)]
    ring
  have heq :
      (∫ v in l*u..h*u, midPoissonWeight n u v *
        ∑' p : ℤ, ∫ χ : ℝ, midPoissonMode r (verticalPoint u v) p χ) =
      (2*Real.pi : ℂ) * ∫ v in l*u..h*u, midDurfeeLine n r v := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun v _ => hsum v)
  rw [heq] at hh
  simp_rw [midContribution_eq_v_integral hn hr]
  have hπ : (2*Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hfactor : ((2*Real.pi : ℂ)^2)⁻¹ * (2*Real.pi : ℂ) = (2*Real.pi : ℂ)⁻¹ := by
    field_simp [hπ]
  rwa [← mul_assoc,hfactor] at hh

theorem hasSum_midContribution_central {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 ≤ r) :
    HasSum (fun p : ℤ => midContribution n r p (-8) 8) (midCentralContribution n r) := by
  simpa only [neg_mul,midCentralContribution] using hasSum_midContribution hn hr (-8) 8

theorem continuous_midDurfeeLine (n : ℕ) {r : ℝ} (hu : 0 < midU n r) :
    Continuous (midDurfeeLine n r) := by
  let u := midU n r
  have hζ : Continuous (verticalPoint u) := by unfold verticalPoint; fun_prop
  have hv (v : ℝ) : ‖exp (-verticalPoint u v)‖ = ‖exp (-(u : ℂ))‖ := by
    simp [Complex.norm_exp]
  have hnorm : ‖exp (-(u : ℂ))‖ < 1 := by
    simpa [Complex.norm_exp,Real.exp_lt_one_iff] using neg_lt_zero.mpr hu
  unfold midDurfeeLine
  refine (Complex.continuous_exp.comp (continuous_const.mul hζ)).mul ?_
  unfold durfeeAnalyticF
  apply continuous_tsum (u := fun j : ℕ =>
    ‖(DurfeeCCS.durfeePolynomialComplex j).eval (-(r : ℂ)^2) * exp (-(u : ℂ)) ^ j‖)
  · exact fun j => continuous_const.mul ((Complex.continuous_exp.comp hζ.neg).pow j)
  · exact summable_norm_durfeeAnalyticF _ hnorm
  · intro j v
    rw [norm_mul, norm_mul, norm_pow, norm_pow, show ‖exp (-verticalPoint (midU n r) v)‖ = _ from hv v]

theorem durfeeNegativeValue_eq_midContour {n : ℕ} {r : ℝ}
    (hu : 0 < midU n r) (hmain : 8*midU n r ≤ Real.pi) :
    (durfeeNegativeValue n r : ℂ) = midCentralContribution n r + midOuterContribution n r := by
  let u := midU n r
  let s := Ioo (-(8*u)) (8*u)
  let t := Icc (-Real.pi) Real.pi
  let f := midDurfeeLine n r
  have hst : s ⊆ t := (Ioo_subset_Icc_self).trans (Icc_subset_Icc (by linarith) hmain)
  have hF : IntegrableOn f t := (continuous_midDurfeeLine n hu).integrableOn_Icc
  have hd : Disjoint s (t \ s) := disjoint_sdiff_right
  have he : s ∪ (t \ s) = t := by
    ext x
    constructor
    · rintro (h|h)
      · exact hst h
      · exact h.1
    · intro h
      by_cases hs : x∈s
      · exact Or.inl hs
      · exact Or.inr ⟨h,hs⟩
  have hsplit : (∫ x in t, f x) = (∫ x in s, f x) + ∫ x in t \ s, f x := by
    calc
      _ = ∫ x in s ∪ (t \ s), f x := congrArg (fun k => ∫ x in k, f x) he.symm
      _ = _ := setIntegral_union hd (measurableSet_Icc.diff measurableSet_Ioo)
        (hF.mono_set hst) (hF.mono_set sdiff_subset)
  rw [ofReal_durfeeNegativeValue_eq_line hu, midCentralContribution,midOuterContribution,
    ← mul_add]
  congr 1
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_Icc_eq_integral_Ioc,
    hsplit]
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  rw [integral_Icc_eq_integral_Ioo]

end DurfeeCCS.Step09
