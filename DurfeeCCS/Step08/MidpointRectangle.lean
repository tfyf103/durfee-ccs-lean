module

public import DurfeeCCS.Step08.MidpointRay
public import DurfeeCCS.Step08.SaddleFourier
public import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The sharper midpoint estimate on the first-saddle rectangle. -/

@[expose] public section
namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06 MeasureTheory Set

private theorem norm_one_add_phase_sq (s φ : ℝ) :
    ‖1 + (s : ℂ) * Complex.exp (φ * I)‖ ^ 2 = 1 + 2 * s * Real.cos φ + s ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    zero_mul, mul_zero, mul_one, sub_zero, zero_add, add_zero]
  linear_combination s ^ 2 * Real.sin_sq_add_cos_sq φ

private theorem half_le_norm_one_add_phase {s φ : ℝ} (hs : 0 ≤ s)
    (hφ : |φ| ≤ 5 * Real.pi / 6) :
    (1 / 2 : ℝ) ≤ ‖1 + (s : ℂ) * Complex.exp (φ * I)‖ := by
  have hp := Real.pi_pos
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ) (by linarith : 5 * Real.pi / 6 ≤ Real.pi) hφ
  rw [Real.cos_abs, show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub] at hc
  have h₂ := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * s)
  have hsq := Real.sq_cos_pi_div_six
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [norm_one_add_phase_sq]
  nlinarith only [h₂, hsq, sq_nonneg (s - Real.cos (Real.pi / 6))]

private theorem half_le_norm_rayLogDenominator {r θ η x : ℝ}
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hθ : |θ| ≤ Real.pi / 3)
    (hη : 0 ≤ η) (hη₁ : η ≤ 2) (hx : 0 ≤ x) :
    (1 / 2 : ℝ) ≤ ‖1 - rayArgument (-(r : ℂ) * I * Complex.exp (θ * I))
      (1 + (η : ℂ) * I) x‖ := by
  let w := -(r : ℂ) * I * Complex.exp (θ * I)
  let α := 1 + (η : ℂ) * I
  let φ := Real.pi / 2 + θ - η * x
  let s := r * Real.exp (-x)
  by_cases hxp : x ≤ Real.pi / 2
  · have hφ : |φ| ≤ 5 * Real.pi / 6 := by
      have hθ' := abs_le.mp hθ
      have hx' : η * x ≤ Real.pi := by
        calc
          _ ≤ 2 * x := mul_le_mul_of_nonneg_right hη₁ hx
          _ ≤ _ := by linarith
      have hx₀ : 0 ≤ η * x := mul_nonneg hη hx
      exact abs_le.mpr ⟨by dsimp only [φ]; linarith, by dsimp only [φ]; linarith⟩
    have ha : 1 - rayArgument w α x = 1 + (s : ℂ) * Complex.exp (φ * I) := by
      unfold rayArgument
      have hExp : -(α * (x : ℂ)) = -(x : ℂ) + (-((η : ℂ) * x)) * I := by dsimp [α]; ring
      dsimp only [w, s, φ]
      rw [show -α * (x : ℂ) = -(α * (x : ℂ)) by ring, hExp, Complex.exp_add]
      push_cast
      have hPhase : ((Real.pi : ℂ) / 2 + θ - (η : ℂ) * x) * I =
          (Real.pi : ℂ) / 2 * I + (θ : ℂ) * I + (-(↑η * ↑x : ℂ)) * I := by ring
      rw [hPhase, Complex.exp_add, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
      ring
    change (1 / 2 : ℝ) ≤ ‖1 - rayArgument w α x‖
    rw [ha]
    exact half_le_norm_one_add_phase (mul_nonneg hr (Real.exp_nonneg _)) hφ
  · have hα : α.re = 1 := by simp [α, Complex.mul_re]
    have hw : ‖w‖ = r := by dsimp only [w]; rw [norm_ray_phase, abs_of_nonneg hr]
    have hE : Real.exp (-x) ≤ 1 / 2 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp x, Real.two_le_pi])
    have hb : ‖rayArgument w α x‖ ≤ 1 / 2 := by
      rw [norm_rayArgument w hα, hw]
      exact (mul_le_of_le_one_left (Real.exp_nonneg _) hr₁).trans hE
    have h := norm_sub_norm_le (1 : ℂ) (rayArgument w α x)
    rw [norm_one] at h
    change (1 / 2 : ℝ) ≤ ‖1 - rayArgument w α x‖
    linarith

private theorem integral_rayLogSecond_rectangle {r θ η : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1)
    (hθ : |θ| ≤ Real.pi / 3) (hη : 0 ≤ η) (hη₁ : η ≤ 2) :
    (∫ x in Ioi (0 : ℝ), ‖rayLogSecond (-(r : ℂ) * I * Complex.exp (θ * I)) (1 + (η : ℂ) * I) x‖) ≤
      4 * (1 + η ^ 2) * r := by
  let w := -(r : ℂ) * I * Complex.exp (θ * I)
  let α := 1 + (η : ℂ) * I
  have hα : α.re = 1 := by simp [α, Complex.mul_re]
  have hs : ‖α‖ ^ 2 = 1 + η ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [α, Complex.mul_re, Complex.mul_im, pow_two]
  have hw : ‖w‖ = r := by dsimp only [w]; rw [norm_ray_phase, abs_of_nonneg hr]
  have hw₁ : ‖w‖ < 1 := by rwa [hw]
  change (∫ x in Ioi (0 : ℝ), ‖rayLogSecond w α x‖) ≤ _
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), (4 * (1 + η ^ 2) * r) * Real.exp (-x) := by
      apply integral_mono_ae (integrableOn_rayLogSecond hw₁ hα).norm
        ((integrableOn_exp_neg_Ioi 0).const_mul _)
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      have hx₀ := (mem_Ioi.mp hx).le
      have hden := half_le_norm_rayLogDenominator hr hr₁.le hθ hη hη₁ hx₀
      have hden₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hden 2
      rw [norm_rayLogSecond hα, hw, hs]
      refine (div_le_div_of_nonneg_left (by positivity) (by positivity) hden₂).trans_eq ?_
      ring
    _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

theorem continuousOn_pairedLog_signed_radius (θ : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) :
    ContinuousOn (fun r : ℝ => pairedLog r θ ζ) (Icc (-1) 1) := by
  refine (continuousOn_tsum (f := fun n r => pairedLogMode r θ ζ n) ?_
    (summable_pairedLog_majorant ζ) ?_).congr ?_
  · intro n
    exact Continuous.continuousOn (by unfold pairedLogMode pairedLogCoeff; fun_prop)
  · intro n r hr
    apply norm_pairedLogMode_le r θ _ hζ n
    exact abs_le.mpr hr
  · intro r hr
    apply pairedLog_eq_tsum_mode r θ _ hζ
    exact abs_le.mpr hr

theorem continuousOn_pairedLog_radius (θ : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) :
    ContinuousOn (fun r : ℝ => pairedLog r θ ζ) (Icc 0 1) :=
  (continuousOn_pairedLog_signed_radius θ hζ).mono (Icc_subset_Icc_left (by norm_num))

theorem continuousOn_saddleG_signed_radius (θ : ℝ) :
    ContinuousOn (fun r : ℝ => saddleG r θ) (Icc (-1) 1) := by
  have hs : Summable (fun n : ℕ => 2 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Complex.one_re, one_mul] using summable_pairedLog_majorant (1 : ℂ)
  refine (continuousOn_tsum (f := fun n r =>
    saddleGCoeff r n * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ)) ?_ hs ?_).congr ?_
  · intro n
    exact Continuous.continuousOn (by unfold saddleGCoeff; fun_prop)
  · intro n r hr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_saddleGCoeff]
    refine (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_of_le_one_right (by norm_num)
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr hr)
  · intro r hr
    apply saddleG_eq_cosineSeries r θ
    exact abs_le.mpr hr

theorem continuousOn_saddleG_radius (θ : ℝ) :
    ContinuousOn (fun r : ℝ => saddleG r θ) (Icc 0 1) :=
  (continuousOn_saddleG_signed_radius θ).mono (Icc_subset_Icc_left (by norm_num))

/-- A sharpened midpoint bound on the rectangle, including the endpoint r = 1. -/
theorem norm_pairedLog_sub_saddleG_div_le_rectangle (r θ u η : ℝ)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hu : 0 < u)
    (hθ : |θ| ≤ Real.pi / 3) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 2) :
    let ζ : ℂ := (u : ℂ) * (1 + (η : ℂ) * I)
    ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤ 5 * u * r := by
  let ζ : ℂ := (u : ℂ) * (1 + (η : ℂ) * I)
  let f (r : ℝ) := ‖pairedLog r θ ζ - saddleG r θ / ζ‖
  let g (r : ℝ) := 5 * u * r
  have hζ : 0 < ζ.re := by simpa [ζ, Complex.mul_re] using hu
  have hfc : ContinuousOn f (Icc 0 1) :=
    ((continuousOn_pairedLog_radius θ hζ).sub ((continuousOn_saddleG_radius θ).div_const ζ)).norm
  have hgc : Continuous g := by unfold g; fun_prop
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : f t ≤ g t := by
    have h := norm_pairedLog_sub_saddleG_div_le_integrals t θ u η (4 * (1 + η ^ 2) * t)
      ht.1 ht.2 hu (fun s hs => integral_rayLogSecond_rectangle ht.1 ht.2 (hs.trans hθ) hη₀ hη₁)
    change f t ≤ _
    refine h.trans ?_
    have hη : 1 + η ^ 2 ≤ 5 := by
      nlinarith only [mul_nonneg hη₀ (sub_nonneg.mpr hη₁)]
    calc
      _ = (1 + η ^ 2) * (u * t) := by ring
      _ ≤ _ := by
        dsimp only [g]
        simpa only [← mul_assoc] using mul_le_mul_of_nonneg_right hη (mul_nonneg hu.le ht.1)
  have hmem : r ∈ Icc (0 : ℝ) 1 := ⟨hr₀, hr₁⟩
  have hcl : r ∈ closure (Ico (0 : ℝ) 1) := by rwa [closure_Ico zero_ne_one]
  exact ContinuousWithinAt.closure_le hcl ((hfc r hmem).mono Ico_subset_Icc_self)
    hgc.continuousAt.continuousWithinAt hb

end DurfeeCCS.Step08
