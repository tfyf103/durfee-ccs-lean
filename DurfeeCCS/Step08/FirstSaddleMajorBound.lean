module

public import DurfeeCCS.Step07.FirstSaddleErrorTable
public import DurfeeCCS.Step08.FirstSaddleSubregions
public import DurfeeCCS.Step08.MidpointMainArc
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import DurfeeCCS.Step08.MidpointRectangle
import DurfeeCCS.Step08.MidpointUniform

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The major-arc bound on the rectangle and its complement in Case 2 of (41). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open MeasureTheory Set intervalIntegral

/-- The positive scalar integrand in (41) with logarithmic error δ. -/
def saddleMajorDensity (r ω : ℝ) (δ : ℝ → ℝ → ℂ) (η θ : ℝ) : ℝ :=
  Real.exp (-ω * saddleGap r θ η) * (Real.exp ‖δ η θ‖ - 1)

private theorem saddleMajorDensity_le {r ω η θ b c : ℝ} {δ : ℝ → ℝ → ℂ}
    (hω : 0 ≤ ω) (hb : b ≤ saddleGap r θ η) (hc : Real.exp ‖δ η θ‖ - 1 ≤ c) :
    saddleMajorDensity r ω δ η θ ≤ Real.exp (-ω * b) * c := by
  apply mul_le_mul _ hc
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (norm_nonneg _))) (Real.exp_nonneg _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hb (neg_nonpos.mpr hω))

private def saddleRectIntegral (f : ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  ∫ η in a..b, ∫ θ in c..d, f η θ

private theorem continuous_saddleInner {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) (c d : ℝ) :
    Continuous (fun η => ∫ θ in c..d, f η θ) :=
  continuous_parametric_intervalIntegral_of_continuous' hf c d

private theorem continuous_saddleSection {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) (η : ℝ) : Continuous (f η) :=
  hf.comp (continuous_const.prodMk continuous_id)

private theorem saddleRectIntegral_mono {f g : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g))
    (hab : a ≤ b) (hcd : c ≤ d)
    (hle : ∀ η ∈ Icc a b, ∀ θ ∈ Icc c d, f η θ ≤ g η θ) :
    saddleRectIntegral f a b c d ≤ saddleRectIntegral g a b c d := by
  apply intervalIntegral.integral_mono_on hab
    ((continuous_saddleInner hf c d).intervalIntegrable _ _)
    ((continuous_saddleInner hg c d).intervalIntegrable _ _)
  intro η hη
  exact intervalIntegral.integral_mono_on hcd ((continuous_saddleSection hf η).intervalIntegrable _ _)
    ((continuous_saddleSection hg η).intervalIntegrable _ _) (hle η hη)

private theorem saddleRectIntegral_le_const {f : ℝ → ℝ → ℝ} {a b c d C : ℝ}
    (hf : Continuous (Function.uncurry f)) (hab : a ≤ b) (hcd : c ≤ d)
    (hle : ∀ η ∈ Icc a b, ∀ θ ∈ Icc c d, f η θ ≤ C) :
    saddleRectIntegral f a b c d ≤ (b - a) * (d - c) * C := by
  calc
    _ ≤ saddleRectIntegral (fun _ _ => C) a b c d :=
      saddleRectIntegral_mono hf continuous_const hab hcd hle
    _ = _ := by simp only [saddleRectIntegral, intervalIntegral.integral_const, smul_eq_mul]; ring

private theorem saddleRectIntegral_split_eta {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) (a b c d e : ℝ) :
    saddleRectIntegral f a b d e + saddleRectIntegral f b c d e = saddleRectIntegral f a c d e :=
  intervalIntegral.integral_add_adjacent_intervals
    ((continuous_saddleInner hf _ _).intervalIntegrable _ _)
    ((continuous_saddleInner hf _ _).intervalIntegrable _ _)

private theorem saddleRectIntegral_split_theta {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) (a b c d e : ℝ) :
    saddleRectIntegral f a b c d + saddleRectIntegral f a b d e = saddleRectIntegral f a b c e := by
  unfold saddleRectIntegral
  rw [← intervalIntegral.integral_add ((continuous_saddleInner hf c d).intervalIntegrable _ _)
    ((continuous_saddleInner hf d e).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro η _
  exact intervalIntegral.integral_add_adjacent_intervals
    ((continuous_saddleSection hf η).intervalIntegrable _ _)
    ((continuous_saddleSection hf η).intervalIntegrable _ _)

private theorem saddleRectIntegral_separable (f g : ℝ → ℝ) (a b c d C : ℝ) :
    saddleRectIntegral (fun η θ => (C * f η) * g θ) a b c d =
      C * (∫ η in a..b, f η) * (∫ θ in c..d, g θ) := by
  unfold saddleRectIntegral
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]

private theorem saddleGaussian_interval {a b c d : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    (∫ x in a..b, Real.exp (-c * (x - d) ^ 2)) ≤ Real.sqrt (Real.pi / c) := by
  rw [intervalIntegral.integral_comp_sub_right (f := fun x => Real.exp (-c * x ^ 2)) d,
    intervalIntegral.integral_of_le (sub_le_sub_right hab d), ← integral_gaussian]
  exact setIntegral_le_integral (integrable_exp_neg_mul_sq hc) (ae_of_all _ fun _ => Real.exp_nonneg _)

private theorem saddleRectangle_gaussian_constant {ω : ℝ} (hω : 0 < ω) :
    Real.sqrt (Real.pi / (0.2 * ω)) * Real.sqrt (Real.pi / (0.082 * ω)) ≤ 24.54 / ω := by
  have h₁ : Real.sqrt (Real.pi / 0.2) ≤ 3.964 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.2)).mpr
    linarith only [Real.pi_lt_d6]
  have h₂ : Real.sqrt (Real.pi / 0.082) ≤ 6.19 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.082)).mpr
    linarith only [Real.pi_lt_d6]
  have hnum := (mul_le_mul h₁ h₂ (Real.sqrt_nonneg _) (by norm_num)).trans
    (by norm_num : (3.964 : ℝ) * 6.19 ≤ 24.54)
  have hScale (a : ℝ) (ha : 0 ≤ a) :
      Real.sqrt (Real.pi / (a * ω)) = Real.sqrt (Real.pi / a) / Real.sqrt ω := by
    rw [← div_div, Real.sqrt_div (by positivity)]
  rw [hScale 0.2 (by norm_num), hScale 0.082 (by norm_num),
    div_mul_div_comm, ← pow_two, Real.sq_sqrt hω.le]
  exact div_le_div_of_nonneg_right hnum hω.le

private theorem saddleMajorRectangle {f : ℝ → ℝ → ℝ} {r ω C : ℝ}
    (hf : Continuous (Function.uncurry f)) (hω : 0 < ω) (hC : 0 ≤ C)
    (hle : ∀ η ∈ Icc (1 / 4) 2, ∀ θ ∈ Icc (-Real.pi / 3) (Real.pi / 3),
      f η θ ≤ (C * Real.exp (-(0.2 * ω) * (η - saddleSlope r) ^ 2)) *
        Real.exp (-(0.082 * ω) * θ ^ 2)) :
    saddleRectIntegral f (1 / 4) 2 (-Real.pi / 3) (Real.pi / 3) ≤ C * (24.54 / ω) := by
  let g (η θ : ℝ) := (C * Real.exp (-(0.2 * ω) * (η - saddleSlope r) ^ 2)) *
    Real.exp (-(0.082 * ω) * θ ^ 2)
  have hg : Continuous (Function.uncurry g) := by unfold Function.uncurry g; fun_prop
  have hθ : -Real.pi / 3 ≤ Real.pi / 3 := by linarith only [Real.pi_pos]
  have hη : (1 / 4 : ℝ) ≤ 2 := by norm_num
  have hga := saddleGaussian_interval (d := saddleSlope r) hη (show 0 < 0.2 * ω by positivity)
  have hgb := saddleGaussian_interval (d := 0) hθ (show 0 < 0.082 * ω by positivity)
  simp only [sub_zero] at hgb
  have ha : 0 ≤ ∫ x in (1 / 4 : ℝ)..2, Real.exp (-(0.2 * ω) * (x - saddleSlope r) ^ 2) :=
    intervalIntegral.integral_nonneg hη fun _ _ => Real.exp_nonneg _
  have hb : 0 ≤ ∫ x in (-Real.pi / 3)..(Real.pi / 3), Real.exp (-(0.082 * ω) * x ^ 2) :=
    intervalIntegral.integral_nonneg hθ fun _ _ => Real.exp_nonneg _
  calc
    _ ≤ saddleRectIntegral g (1 / 4) 2 (-Real.pi / 3) (Real.pi / 3) :=
      saddleRectIntegral_mono hf hg hη hθ hle
    _ ≤ C * (Real.sqrt (Real.pi / (0.2 * ω)) * Real.sqrt (Real.pi / (0.082 * ω))) := by
      rw [show g = _ from rfl, saddleRectIntegral_separable, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hga hgb hb (Real.sqrt_nonneg _)) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (saddleRectangle_gaussian_constant hω) hC

private theorem saddleExponential_integral {ω : ℝ} (hω : 40 ≤ ω) :
    (∫ η in (2 : ℝ)..4, Real.exp (1.38 - (0.1 * ω - 0.69) * η)) ≤
      Real.exp (2.76 - 0.2 * ω) / (0.1 * ω - 0.69) := by
  let b := 0.1 * ω - 0.69
  have hb : 0 < b := by dsimp [b]; linarith only [hω]
  change (∫ η in (2 : ℝ)..4, Real.exp (1.38 - b * η)) ≤ _
  have hE : (fun η : ℝ => Real.exp (1.38 - b * η)) =
      fun η => Real.exp 1.38 * Real.exp (-b * η) := by
    funext η
    rw [← Real.exp_add]
    congr 1
    ring
  have hInt : IntegrableOn (fun η : ℝ => Real.exp (-b * η)) (Ioi 2) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) _
  rw [hE, intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 4)]
  calc
    _ ≤ ∫ η in Ioi (2 : ℝ), Real.exp 1.38 * Real.exp (-b * η) :=
      setIntegral_mono_set (hInt.const_mul _) (ae_of_all _ fun _ => by positivity)
        (ae_of_all _ fun x (h : x ∈ Ioc (2 : ℝ) 4) => h.1)
    _ = _ := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hb), neg_div_neg_eq,
        ← mul_div_assoc, ← Real.exp_add]
      congr 2
      dsimp [b]
      ring

/-- Case 2 of (41), combining the rectangle with the five complementary regions. -/
theorem saddleMajorDensity_integral_le_case_two {r r₀ ω : ℝ} {δ : ℝ → ℝ → ℂ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hω : 40 ≤ ω)
    (hr₀ : 0 ≤ r₀) (hf : Continuous (Function.uncurry (saddleMajorDensity r ω δ)))
    (h45 : ∀ η ∈ Icc (0 : ℝ) 16, ∀ θ ∈ Icc (-Real.pi) Real.pi,
      ‖δ η θ‖ ≤ 0.51 + 0.69 * (1 + Real.sqrt (1 + η ^ 2)))
    (hrect : ∀ η ∈ Icc (1 / 4 : ℝ) 2, ∀ θ ∈ Icc (-Real.pi / 3) (Real.pi / 3),
      ‖δ η θ‖ ≤ 5.33 * r₀ * Step07.firstSaddleU0 r₀) :
    3 * ω / (4 * Real.pi) *
      (∫ η in (0 : ℝ)..16, ∫ θ in -Real.pi..Real.pi, saddleMajorDensity r ω δ η θ) ≤
      Step07.firstSaddleRectError r₀ + Step07.firstSaddleRectComplement ω := by
  let f := saddleMajorDensity r ω δ
  let C := Real.exp (5.33 * r₀ * Step07.firstSaddleU0 r₀) - 1
  have hω' : 0 < ω := by linarith only [hω]
  have hU0 : 0 ≤ Step07.firstSaddleU0 r₀ := Real.sqrt_nonneg _
  have hC : 0 ≤ C := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  have hp := Real.pi_pos
  have hθπ : -Real.pi ≤ Real.pi := by linarith only [hp]
  have hsplit :
      saddleRectIntegral f 0 16 (-Real.pi) Real.pi =
        saddleRectIntegral f 0 (1 / 4) (-Real.pi) Real.pi +
        saddleRectIntegral f (1 / 4) 2 (-Real.pi) (-Real.pi / 3) +
        saddleRectIntegral f (1 / 4) 2 (-Real.pi / 3) (Real.pi / 3) +
        saddleRectIntegral f (1 / 4) 2 (Real.pi / 3) Real.pi +
        saddleRectIntegral f 2 4 (-Real.pi) Real.pi +
        saddleRectIntegral f 4 8 (-Real.pi) Real.pi +
        saddleRectIntegral f 8 16 (-Real.pi) Real.pi := by
    rw [← saddleRectIntegral_split_eta hf 0 8 16, ← saddleRectIntegral_split_eta hf 0 4 8,
      ← saddleRectIntegral_split_eta hf 0 2 4, ← saddleRectIntegral_split_eta hf 0 (1 / 4) 2,
      ← saddleRectIntegral_split_theta hf (1 / 4) 2 (-Real.pi) (-Real.pi / 3),
      ← saddleRectIntegral_split_theta hf (1 / 4) 2 (-Real.pi / 3) (Real.pi / 3)]
    ring
  have hsmall := saddleRectIntegral_le_const (C := Real.exp (-0.206 * ω) * 6)
    hf (show (0 : ℝ) ≤ 1 / 4 by norm_num) hθπ (by
      intro η hη θ hθ
      have h := h45 η ⟨hη.1, hη.2.trans (by norm_num)⟩ θ hθ
      simpa only [mul_comm (-ω) 0.206, mul_neg, neg_mul] using
        (saddleMajorDensity_le hω'.le (saddleGap_small_eta hr hr₁ hη.1 hη.2)
          (saddle_log_error_small_eta h hη.1 hη.2).le : f η θ ≤ _))
  have houter (η θ : ℝ) (hη : η ∈ Icc (1 / 4 : ℝ) 2)
      (hθ : θ ∈ Icc (-Real.pi) Real.pi) (hθ' : Real.pi / 3 ≤ |θ|) :
      f η θ ≤ Real.exp (-0.275 * ω) * 15 := by
    have hη' : 0 ≤ η := by linarith only [hη.1]
    have h := h45 η ⟨hη', hη.2.trans (by norm_num)⟩ θ hθ
    simpa only [mul_comm (-ω) 0.275, mul_neg, neg_mul] using
      (saddleMajorDensity_le hω'.le (saddleGap_outer_angles hr hr₁ hη' hθ' (abs_le.mpr hθ))
        (saddle_log_error_eta_le_two h hη' hη.2).le : f η θ ≤ _)
  have hleft := saddleRectIntegral_le_const hf (show (1 / 4 : ℝ) ≤ 2 by norm_num)
    (show -Real.pi ≤ -Real.pi / 3 by linarith only [hp]) (by
      intro η hη θ hθ
      apply houter η θ hη ⟨hθ.1, by linarith only [hθ.2, hp]⟩
      rw [abs_of_nonpos (by linarith only [hθ.2, hp])]
      linarith only [hθ.2])
  have hright := saddleRectIntegral_le_const hf (show (1 / 4 : ℝ) ≤ 2 by norm_num)
    (show Real.pi / 3 ≤ Real.pi by linarith only [hp]) (by
      intro η hη θ hθ
      apply houter η θ hη ⟨by linarith only [hθ.1, hp], hθ.2⟩
      rw [abs_of_nonneg (by linarith only [hθ.1, hp])]
      exact hθ.1)
  have hmid := saddleMajorRectangle (r := r) hf hω' hC (by
    intro η hη θ hθ
    have hθ' : |θ| ≤ Real.pi / 3 := abs_le.mpr ⟨by linarith only [hθ.1], hθ.2⟩
    have h := saddleMajorDensity_le hω'.le (saddleGap_rectangle hr hr₁ hη.1 hη.2 hθ')
      (sub_le_sub_right (Real.exp_le_exp.mpr (hrect η hη θ hθ)) 1)
    have heq :
        -ω * (0.2 * (η - saddleSlope r) ^ 2 + 0.082 * θ ^ 2) =
        -(0.2 * ω) * (η - saddleSlope r) ^ 2 + -(0.082 * ω) * θ ^ 2 := by ring
    rw [heq, Real.exp_add] at h
    convert h using 1
    dsimp [C]
    ring)
  have h24 : saddleRectIntegral f 2 4 (-Real.pi) Real.pi ≤
      2 * Real.pi * (Real.exp (2.76 - 0.2 * ω) / (0.1 * ω - 0.69)) := by
    let g (η : ℝ) := Real.exp (1.38 - (0.1 * ω - 0.69) * η)
    have hg : Continuous (Function.uncurry (fun η (_ : ℝ) => g η)) := by
      unfold Function.uncurry g
      fun_prop
    have hle : saddleRectIntegral f 2 4 (-Real.pi) Real.pi ≤
        saddleRectIntegral (fun η _ => g η) 2 4 (-Real.pi) Real.pi := by
      apply saddleRectIntegral_mono hf hg (by norm_num) hθπ
      intro η hη θ hθ
      have h := h45 η ⟨hη.1.trans' (by norm_num), hη.2.trans (by norm_num)⟩ θ hθ
      refine (saddleMajorDensity_le hω'.le (saddleGap_eta_two_to_four hr hr₁ hη.1 hη.2)
        (saddle_log_error_eta_ge_two h hη.1).le).trans_eq ?_
      rw [← Real.exp_add]
      unfold g
      congr 1
      ring
    refine hle.trans ?_
    unfold saddleRectIntegral
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add, ← two_mul]
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (saddleExponential_integral hω) (by positivity)
  have h48 := saddleRectIntegral_le_const (C := Real.exp (-9 * ω / 17) * 900)
    hf (show (4 : ℝ) ≤ 8 by norm_num) hθπ (by
      intro η hη θ hθ
      have hη' : 0 ≤ η := le_trans (by norm_num) hη.1
      have h := h45 η ⟨hη', hη.2.trans (by norm_num)⟩ θ hθ
      have heq : -ω * (9 / 17) = -9 * ω / 17 := by ring
      rw [← heq]
      exact saddleMajorDensity_le hω'.le (saddleGap_eta_ge_four hr hr₁ hη.1)
        (saddle_log_error_eta_le_eight h hη' hη.2).le)
  have h816 := saddleRectIntegral_le_const (C := Real.exp (-49 * ω / 65) * 220000)
    hf (show (8 : ℝ) ≤ 16 by norm_num) hθπ (by
      intro η hη θ hθ
      have hη' : 0 ≤ η := le_trans (by norm_num) hη.1
      have h := h45 η ⟨hη', hη.2⟩ θ hθ
      have heq : -ω * (49 / 65) = -49 * ω / 65 := by ring
      rw [← heq]
      exact saddleMajorDensity_le hω'.le (saddleGap_eta_ge_eight hr hr₁ hη.1)
        (saddle_log_error_eta_le_sixteen h hη' hη.2).le)
  let E := 1.5 * Real.exp (-0.206 * ω) +
    Real.exp (2.76 - 0.2 * ω) / (0.1 * ω - 0.69) +
    3600 * Real.exp (-9 * ω / 17) + 1760000 * Real.exp (-49 * ω / 65) +
    (105 / 4) * Real.exp (-0.275 * ω)
  have htotal : saddleRectIntegral f 0 16 (-Real.pi) Real.pi ≤
      C * (24.54 / ω) + 2 * Real.pi * E := by
    rw [hsplit]
    dsimp only [E]
    linarith only [hsmall, hleft, hmid, hright, h24, h48, h816,
      mul_nonneg hp.le (Real.exp_nonneg (-0.275 * ω))]
  change 3 * ω / (4 * Real.pi) * saddleRectIntegral f 0 16 (-Real.pi) Real.pi ≤ _
  calc
    _ ≤ 3 * ω / (4 * Real.pi) * (C * (24.54 / ω) + 2 * Real.pi * E) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = _ := by
      rw [mul_add, Step07.firstSaddleRectError, Step07.firstSaddleRectComplement]
      change _ = (3 * 24.54) / (4 * Real.pi) * C + (3 * ω / 2) * E
      congr 1
      · field_simp [hω'.ne', Real.pi_ne_zero]
      · field_simp [Real.pi_ne_zero]
        ring

/-- Equation (41) for the actual logarithmic error in the large-radius case. -/
theorem firstSaddleMainArcBudget_le_case_two {n : ℕ} (hn : 6400 ≤ n) {r r₀ : ℝ}
    (hr : 1 / 4 ≤ r) (hrr : r ≤ r₀) (hr₀ : r₀ ≤ 1) :
    firstSaddleMainArcBudget n r ≤
      Step07.firstSaddleRectError r₀ + Step07.firstSaddleRectComplement (saddleOmega n r) := by
  let u := saddleU n r
  let δ (η θ : ℝ) :=
    pairedLog r θ (verticalPoint u (u * η)) -
      Step06.saddleG r θ / verticalPoint u (u * η)
  have hrp : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hr₁ : r ≤ 1 := hrr.trans hr₀
  have hn' : 0 < n := by omega
  have hu : 0 < u := saddleU_pos hn' hrp
  have hU := Step07.firstSaddleRadius_leU0 hn hrp hrr hr₀
  have hAsq := (Step07.firstSaddle_coordinates_bounds hrp hr₁).1
  have hω := Step07.firstSaddleOmega_lower hn hrp hr (β := 1) (by norm_num)
    (by simpa only [one_mul] using hAsq)
  have h40 : 40 ≤ saddleOmega n r := by
    refine le_trans ?_ hω
    rw [show (6400 : ℝ) * 1 * (1 / 4) = (40 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : 0 ≤ (40 : ℝ))]
  have hf : Continuous (Function.uncurry (saddleMajorDensity r (saddleOmega n r) δ)) :=
    continuous_firstSaddleMainArcKernel hn' hrp hr₁
  change 3 * saddleOmega n r / (4 * Real.pi) *
    (∫ η in (0 : ℝ)..16, ∫ θ in -Real.pi..Real.pi,
      saddleMajorDensity r (saddleOmega n r) δ η θ) ≤ _
  apply saddleMajorDensity_integral_le_case_two hrp hr₁ h40 (hrp.le.trans hrr) hf
  · intro η hη θ _
    unfold δ
    rw [verticalPoint_mul]
    have hη' : |η| ≤ 16 := by
      rw [abs_of_nonneg hη.1]
      exact hη.2
    exact norm_pairedLog_sub_saddleG_div_le_45 r θ u η
      (by rwa [abs_of_pos hrp]) hu (norm_saddleU_mul_one_add_im_le hn hrp hr₁ hη')
  · intro η hη θ hθ
    have hη' : 0 ≤ η := le_trans (by norm_num) hη.1
    have hθ' : |θ| ≤ Real.pi / 3 := abs_le.mpr ⟨by linarith only [hθ.1], hθ.2⟩
    have h := norm_pairedLog_sub_saddleG_div_le_rectangle r θ u η
      hrp.le hr₁ hu hθ' hη' hη.2
    unfold δ
    rw [verticalPoint_mul]
    refine h.trans ?_
    have hU' : u ≤ Step07.firstSaddleU0 r₀ := hU
    have hU₀ : 0 ≤ Step07.firstSaddleU0 r₀ := hu.le.trans hU'
    have hprod := mul_le_mul hU' hrr hrp.le hU₀
    have hnonneg := mul_nonneg hU₀ (hrp.le.trans hrr)
    nlinarith only [hprod, hnonneg]

end DurfeeCCS.Step08
