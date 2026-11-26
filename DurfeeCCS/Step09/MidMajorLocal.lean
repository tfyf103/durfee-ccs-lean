module

public import DurfeeCCS.Step09.MidMajorGaussian
public import DurfeeCCS.Step08.ExpRemainder

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The three local error contributions in (58). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open MeasureTheory Set Complex DurfeeCCS.Step08

/-- Relative Gaussian mass outside the common truncation interval. -/
theorem midGaussian_relative_tail_le {A h z : ℝ} (hA : 0 < A) (hh : 0 < h)
    (hz : 0 < z) (hzA : z ≤ A * h ^ 2) :
    (∫ x in (Icc (-h) h)ᶜ, Real.exp (-A * x ^ 2)) ≤
      (∫ x : ℝ, Real.exp (-A * x ^ 2)) * (Real.exp (-z) / Real.sqrt (Real.pi * z)) := by
  apply (midGaussian_tail_le hA hh).trans
  rw [integral_gaussian A, Real.sqrt_div Real.pi_nonneg]
  have heq : (Real.exp (-A * h ^ 2) / (A * h)) =
      Real.sqrt Real.pi / Real.sqrt A * (Real.exp (-(A * h ^ 2)) /
        Real.sqrt (Real.pi * (A * h ^ 2))) := by
    rw [Real.sqrt_mul Real.pi_nonneg, Real.sqrt_mul hA.le, Real.sqrt_sq_eq_abs,
      abs_of_pos hh]
    field_simp
    nlinarith only [Real.sq_sqrt hA.le]
  rw [heq]
  gcongr

/--
A common real-part estimate for two phases controls their integrated difference
after truncation, removal of the multiplier and a quartic phase estimate.
-/
theorem midMajor_inner_error {P Q B : ℝ → ℂ} {A F h z L K : ℝ}
    (hA : 0 < A) (hh : 0 < h) (hz : 0 < z) (hzA : z ≤ A * h ^ 2)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hP : Continuous P) (hQ : Continuous Q) (hB : Continuous B)
    (hp : ∀ x, (P x).re ≤ F - A * x ^ 2)
    (hq : ∀ x, (Q x).re ≤ F - A * x ^ 2)
    (hb : ∀ x, ‖B x‖ ≤ 10.9)
    (hnear : ∀ x ∈ Icc (-h) h, ‖B x - 1‖ ≤ Real.exp L - 1)
    (hquartic : ∀ x ∈ Icc (-h) h, ‖P x - Q x‖ ≤ K * x ^ 4) :
    ‖(∫ x : ℝ, exp (P x) * B x) - ∫ x : ℝ, exp (Q x)‖ ≤
      Real.exp F * Real.sqrt (Real.pi / A) *
        ((119 / 10) * (Real.exp (-z) / Real.sqrt (Real.pi * z)) +
          (Real.exp L - 1) + 3 * K / (4 * A ^ 2)) := by
  let S := Icc (-h) h
  let g (x : ℝ) := Real.exp (-A * x ^ 2)
  let g₄ (x : ℝ) := x ^ 4 * g x
  have hg : Integrable g := integrable_exp_neg_mul_sq hA
  have hg₄ : Integrable g₄ := midGaussian_integrable_quartic hA
  have hpe (x : ℝ) : ‖exp (P x)‖ ≤ Real.exp F * g x := by
    rw [Complex.norm_exp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by simpa [sub_eq_add_neg] using hp x)
  have hqe (x : ℝ) : ‖exp (Q x)‖ ≤ Real.exp F * g x := by
    rw [Complex.norm_exp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by simpa [sub_eq_add_neg] using hq x)
  have hiP : Integrable (fun x => exp (P x) * B x) := by
    refine ((hg.const_mul (Real.exp F)).mul_const 10.9).mono'
      (((Complex.continuous_exp.comp hP).mul hB).aestronglyMeasurable) ?_
    exact ae_of_all _ fun x => by
      rw [norm_mul]
      exact mul_le_mul (hpe x) (hb x) (norm_nonneg _) (by positivity)
  have hiQ : Integrable (fun x => exp (Q x)) := by
    exact (hg.const_mul (Real.exp F)).mono'
      ((Complex.continuous_exp.comp hQ).aestronglyMeasurable) (ae_of_all _ hqe)
  let d (x : ℝ) := exp (P x) * B x - exp (Q x)
  have hd : Integrable d := hiP.sub hiQ
  have hd' : Integrable (fun x => ‖d x‖) := hd.norm
  have hl₀ : 0 ≤ Real.exp L - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hL)
  have hout (x : ℝ) :
      ‖d x‖ ≤ (Real.exp F * (119 / 10)) * g x := by
    unfold d
    have h := norm_sub_le (exp (P x) * B x) (exp (Q x))
    rw [norm_mul] at h
    calc
      _ ≤ ‖exp (P x)‖ * ‖B x‖ + ‖exp (Q x)‖ := h
      _ ≤ (Real.exp F * g x) * 10.9 + Real.exp F * g x :=
        add_le_add (mul_le_mul (hpe x) (hb x) (norm_nonneg _) (by positivity)) (hqe x)
      _ = _ := by ring
  have hin (x : ℝ) (hx : x ∈ S) :
      ‖d x‖ ≤ (Real.exp F * (Real.exp L - 1)) * g x +
        (Real.exp F * K) * g₄ x := by
    have heq : d x = exp (P x) * (B x - 1) + (exp (P x) - exp (Q x)) := by
      unfold d
      ring
    have hmax : Real.exp (max (P x).re (Q x).re) ≤ Real.exp F * g x := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      exact max_le (by simpa [sub_eq_add_neg] using hp x) (by simpa [sub_eq_add_neg] using hq x)
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    refine add_le_add (?_ : ‖exp (P x)‖ * ‖B x - 1‖ ≤ _) ?_
    · calc
        _ ≤ (Real.exp F * g x) * (Real.exp L - 1) :=
          mul_le_mul (hpe x) (hnear x hx) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · calc
        _ ≤ ‖P x - Q x‖ * Real.exp (max (P x).re (Q x).re) := norm_exp_sub_exp_le _ _
        _ ≤ (K * x ^ 4) * (Real.exp F * g x) :=
          mul_le_mul (hquartic x hx) hmax (Real.exp_pos _).le (by positivity)
        _ = _ := by unfold g₄; ring
  have hO : (∫ x in Sᶜ, ‖d x‖) ≤ (Real.exp F * (119 / 10)) *
      (∫ x in Sᶜ, g x) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hd'.integrableOn (hg.const_mul _).integrableOn
      measurableSet_Icc.compl (fun x _ => hout x)
  have hiDom : Integrable (fun x => (Real.exp F * (Real.exp L - 1)) * g x +
      (Real.exp F * K) * g₄ x) := (hg.const_mul _).add (hg₄.const_mul _)
  have hI : (∫ x in S, ‖d x‖) ≤
      (Real.exp F * (Real.exp L - 1)) * (∫ x, g x) +
        (Real.exp F * K) * (∫ x, g₄ x) := by
    apply (setIntegral_mono_on hd'.integrableOn hiDom.integrableOn measurableSet_Icc hin).trans
    apply (setIntegral_le_integral hiDom
      (ae_of_all _ (fun x => add_nonneg (by positivity) (by unfold g₄ g; positivity)))).trans_eq
    rw [integral_add (hg.const_mul _) (hg₄.const_mul _), integral_const_mul, integral_const_mul]
  have hT := hO.trans (mul_le_mul_of_nonneg_left (midGaussian_relative_tail_le hA hh hz hzA)
    (by positivity : 0 ≤ Real.exp F * (119 / 10)))
  rw [← integral_sub hiP hiQ]
  apply (norm_integral_le_integral_norm d).trans
  rw [← integral_add_compl measurableSet_Icc hd']
  apply (add_le_add hI hT).trans_eq
  change _ * (∫ x, g x) + _ * (∫ x, g₄ x) + _ * ((∫ x, g x) * _) = _
  have hg₄eq : (∫ x, g₄ x) = (∫ x, g x) * (3 / (4 * A ^ 2)) := midGaussian_fourth_moment hA
  have hgeq : (∫ x, g x) = Real.sqrt (Real.pi / A) := integral_gaussian A
  rw [hg₄eq, hgeq]
  ring

end DurfeeCCS.Step09
