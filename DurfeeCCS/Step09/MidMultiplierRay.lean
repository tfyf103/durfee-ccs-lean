module

public import DurfeeCCS.Step08.MidpointRectangle
public import DurfeeCCS.Step07.ThetaBounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The midpoint remainder on the main saddle rectangle. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step09

open Complex MeasureTheory Set Filter DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08
open scoped Topology

private theorem sin_le_norm_one_sub_exp (R φ : ℝ) (hs : 0 ≤ Real.sin φ) :
    Real.sin φ ≤ ‖1 - (R : ℂ) * Complex.exp ((φ : ℂ) * I)‖ := by
  apply (sq_le_sq₀ hs (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.re_mul_ofReal, Complex.im_mul_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, add_zero, sub_zero, zero_sub]
  have h := Real.sin_sq_add_cos_sq φ
  have hsq := sq_nonneg (R - Real.cos φ)
  have h₁ := congrArg (fun y : ℝ => R ^ 2 * y) h
  nlinarith only [h, hsq, h₁]

private theorem sin_lower_on_center {d φ : ℝ} (hd : 0 ≤ d)
    (hl : d ≤ φ) (hh : φ ≤ Real.pi - d) : Real.sin d ≤ Real.sin φ := by
  by_cases h : φ ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h hl
  · rw [← Real.sin_pi_sub φ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith) (by linarith)

private theorem norm_rayDenominator_inner {t θ η x h : ℝ}
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hpi : h < Real.pi / 2) (hθ : |θ| ≤ h)
    (hη : 0 ≤ η) (hη' : η ≤ 3 / 2)
    (hx : 0 ≤ x) (hx' : x ≤ 2 * ((Real.pi / 2 - h) / 2) / 3) :
    Real.sin ((Real.pi / 2 - h) / 2) ≤
      ‖1 - rayArgument ((t : ℂ) * I * Complex.exp ((θ : ℂ) * I))
        (1 + (η : ℂ) * I) x‖ := by
  let d := (Real.pi / 2 - h) / 2
  let φ := Real.pi / 2 + θ - η * x
  have hd : 0 < d := by dsimp [d]; linarith
  have hηx : η * x ≤ d := by
    exact (mul_le_mul hη' hx' hx (by norm_num)).trans_eq (by ring)
  have hθ₀ := (abs_le.mp hθ).1
  have hθ₁ := (abs_le.mp hθ).2
  have hφmin : d ≤ φ := by dsimp only [d, φ] at *; linarith
  have hφmax : φ ≤ Real.pi - d := by dsimp only [d, φ] at *; linarith [mul_nonneg hη hx]
  have hφpos : 0 < φ := hd.trans_le hφmin
  have hφpi : φ < Real.pi := hφmax.trans_lt (by linarith)
  have he :
      rayArgument ((t : ℂ) * I * Complex.exp ((θ : ℂ) * I)) (1 + (η : ℂ) * I) x =
        ((t * Real.exp (-x) : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * I) := by
    rw [rayArgument, Complex.ofReal_mul, Complex.ofReal_exp]
    have hsum : (-((1 + (η : ℂ) * I)) * (x : ℂ)) = -(x : ℂ) + (-(η * x : ℝ) : ℂ) * I := by
      push_cast
      ring
    have hAngle : (φ : ℂ) * I = (Real.pi : ℂ) / 2 * I + (θ : ℂ) * I + (-(η*x : ℝ) : ℂ) * I := by
      dsimp [φ]
      push_cast
      ring
    rw [hsum, hAngle, Complex.exp_add, Complex.exp_add, Complex.exp_add,
      Complex.exp_pi_div_two_mul_I, Complex.ofReal_neg]
    ring
  rw [he]
  exact (sin_lower_on_center hd.le hφmin hφmax).trans
    (sin_le_norm_one_sub_exp _ _ (Real.sin_pos_of_pos_of_lt_pi hφpos hφpi).le)

private theorem raySecond_tail {b : ℝ} (hb : 0 < b) :
    IntegrableOn (raySecondMajorant 1) (Ioi b) ∧
      (∫ x in Ioi b, raySecondMajorant 1 x) = (Real.exp b - 1)⁻¹ := by
  let F (x : ℝ) := -(1 - Real.exp (-x))⁻¹
  have hD (x : ℝ) (hx : x ∈ Ici b) : HasDerivAt F (raySecondMajorant 1 x) x := by
    have hx' : 0 < x := hb.trans_le hx
    have hp : 0 < 1 - Real.exp (-x) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    have hd := (((hasDerivAt_id x).neg.exp).const_sub 1).inv hp.ne'
    convert hd.neg using 1
    · rfl
    · simp [raySecondMajorant]
      ring
  have hnn (x : ℝ) (_hx : x ∈ Ioi b) : 0 ≤ raySecondMajorant 1 x := by
    unfold raySecondMajorant
    positivity
  have hlim : Tendsto F atTop (𝓝 (-1)) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      Real.tendsto_exp_neg_atTop_nhds_zero).inv₀ (by simp)
    simpa [F] using h.neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hD hnn hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hD hnn hlim]
  dsimp [F]
  have hE : Real.exp b ≠ 0 := (Real.exp_pos _).ne'
  have hE' : Real.exp b - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hb)).ne'
  rw [Real.exp_neg]
  field_simp [hE, hE']
  ring

private theorem integral_rayLogSecond_inner {t θ η h : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hh : 0 ≤ h) (hpi : h < Real.pi / 2) (hθ : |θ| ≤ h) (hη : 0 ≤ η) (hη' : η ≤ 3 / 2) :
    (∫ x in Ioi (0 : ℝ), ‖rayLogSecond ((t : ℂ) * I * Complex.exp ((θ : ℂ) * I))
      (1 + (η : ℂ) * I) x‖) ≤ (1 + η ^ 2) * t * theta38K h := by
  let w := (t : ℂ) * I * Complex.exp ((θ : ℂ) * I)
  let α := 1 + (η : ℂ) * I
  let d := (Real.pi / 2 - h) / 2
  let b := 2 * d / 3
  let A := (1 + η ^ 2) * t
  let f (x : ℝ) := ‖rayLogSecond w α x‖
  have hα : α.re = 1 := by simp [α, Complex.mul_re]
  have hα₂ : ‖α‖ ^ 2 = 1 + η ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [α, Complex.mul_re, Complex.mul_im, pow_two]
  have hw : ‖w‖ = t := by
    simpa only [Complex.ofReal_neg, neg_neg, abs_neg, abs_of_nonneg ht] using
      norm_ray_phase (-t) θ
  have hw' : ‖w‖ < 1 := hw.trans_lt ht'
  have hInt : IntegrableOn f (Ioi 0) := (integrableOn_rayLogSecond hw' hα).norm
  have hd : 0 < d := by dsimp [d]; linarith
  have hdp : d < Real.pi := by dsimp [d]; linarith [Real.pi_pos]
  have hb : 0 < b := by dsimp [b]; positivity
  have hs : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd hdp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have heq (x : ℝ) : f x = A * Real.exp (-x) / ‖1 - rayArgument w α x‖ ^ 2 := by
    unfold f
    rw [norm_rayLogSecond hα, hα₂, hw]
  have hshort :
      (∫ x in Ioc 0 b, f x) ≤ A / Real.sin d ^ 2 := by
    have hi : IntegrableOn (fun x => Real.exp (-x)) (Ioc 0 b) :=
      (integrableOn_exp_neg_Ioi 0).mono_set Ioc_subset_Ioi_self
    calc
      _ ≤ ∫ x in Ioc 0 b, (A / Real.sin d ^ 2) * Real.exp (-x) := by
        apply integral_mono_ae (hInt.mono_set Ioc_subset_Ioi_self) (hi.const_mul _)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
        rw [heq]
        have hk := norm_rayDenominator_inner ht hh hpi hθ hη hη' hx.1.le hx.2
        calc
          _ ≤ A * Real.exp (-x) / Real.sin d ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hs)
              (pow_le_pow_left₀ hs.le hk 2)
          _ = _ := by ring
      _ = (A / Real.sin d ^ 2) * ∫ x in Ioc 0 b, Real.exp (-x) := integral_const_mul _ _
      _ ≤ _ := by
        conv_rhs => rw [← mul_one (A / Real.sin d ^ 2), ← integral_exp_neg_Ioi_zero]
        exact mul_le_mul_of_nonneg_left
          (setIntegral_mono_set (integrableOn_exp_neg_Ioi 0)
            (Eventually.of_forall fun _ => Real.exp_nonneg _)
            (Eventually.of_forall Ioc_subset_Ioi_self)) (by positivity)
  have hfar : (∫ x in Ioi b, f x) ≤ A * (Real.exp b - 1)⁻¹ := by
    have hS : Ioi b ⊆ Ioi (0 : ℝ) := fun _ hx => hb.trans hx
    have htInt := raySecond_tail hb
    calc
      _ ≤ ∫ x in Ioi b, A * raySecondMajorant 1 x := by
        apply integral_mono_ae (hInt.mono_set hS) (htInt.1.const_mul _)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
        have hx' : 0 < x := hb.trans hx
        have hpos : 0 < 1 - Real.exp (-x) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
        have hN := norm_sub_norm_le (1 : ℂ) (rayArgument w α x)
        rw [norm_one, norm_rayArgument w hα, hw] at hN
        have hden : 1 - Real.exp (-x) ≤ ‖1 - rayArgument w α x‖ :=
          (sub_le_sub_left (mul_le_of_le_one_left (Real.exp_nonneg _) ht'.le) 1).trans hN
        rw [heq]
        unfold raySecondMajorant
        rw [one_mul, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Real.exp_nonneg _)
          (sq_pos_of_pos hpos) (pow_le_pow_left₀ hpos.le hden 2)) hA
      _ = _ := by rw [integral_const_mul, htInt.2]
  have hS : Ioi b ⊆ Ioi (0 : ℝ) := fun _ hx => hb.trans hx
  change (∫ x in Ioi 0, f x) ≤ _
  rw [← Ioc_union_Ioi_eq_Ioi hb.le, setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set hS)]
  refine (add_le_add hshort hfar).trans_eq ?_
  change A / Real.sin d ^ 2 + A * (Real.exp b - 1)⁻¹ =
    A * ((Real.sin d ^ 2)⁻¹ + (Real.exp b - 1)⁻¹)
  rw [div_eq_mul_inv, mul_add]

theorem norm_pairedLog_neg_sub_saddleG_div_le_inner {t θ u η h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hu : 0 < u) (hh : 0 ≤ h) (hpi : h < Real.pi / 2) (hθ : |θ| ≤ h)
    (hη : 0 ≤ η) (hη' : η ≤ 3 / 2) :
    let ζ : ℂ := (u : ℂ) * (1 + (η : ℂ) * I)
    ‖pairedLog (-t) θ ζ - saddleG (-t) θ / ζ‖ ≤ u * (1 + η ^ 2) * t * theta38K h / 4 := by
  let ζ : ℂ := (u : ℂ) * (1 + (η : ℂ) * I)
  let f (t : ℝ) := ‖pairedLog (-t) θ ζ - saddleG (-t) θ / ζ‖
  let g (t : ℝ) := u * (1 + η ^ 2) * t * theta38K h / 4
  have hζ : 0 < ζ.re := by simpa [ζ, Complex.mul_re] using hu
  have hmap : MapsTo (fun t : ℝ => -t) (Icc 0 1) (Icc (-1) 1) := by
    intro x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hf : ContinuousOn f (Icc 0 1) :=
    (((continuousOn_pairedLog_signed_radius θ hζ).sub
      ((continuousOn_saddleG_signed_radius θ).div_const ζ)).comp
        continuous_neg.continuousOn hmap).norm
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hle (v : ℝ) (hv : v ∈ Ico (0 : ℝ) 1) : f v ≤ g v := by
    have hB (x : ℝ) (hx : |x| ≤ |θ|) :=
      integral_rayLogSecond_inner hv.1 hv.2 hh hpi (hx.trans hθ) hη hη'
    have hb := norm_pairedLog_sub_saddleG_div_le_signed_integrals (-v) θ u η
      ((1 + η ^ 2) * v * theta38K h) (by simpa [abs_of_nonneg hv.1] using hv.2) hu
      (fun x hx => by simpa only [Complex.ofReal_neg, neg_neg] using hB x hx)
    refine hb.trans_eq ?_
    dsimp [g]
    ring
  have htM : t ∈ Icc (0 : ℝ) 1 := ⟨ht,ht'⟩
  have hcl : t ∈ closure (Ico (0 : ℝ) 1) := by rwa [closure_Ico zero_ne_one]
  exact ContinuousWithinAt.closure_le hcl ((hf t htM).mono Ico_subset_Icc_self)
    hg.continuousAt.continuousWithinAt hle

end DurfeeCCS.Step09
