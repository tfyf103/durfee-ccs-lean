module

public import DurfeeCCS.Step08.SaddleBesselAverage
public import DurfeeCCS.Step08.SaddleBesselJacobian
public import DurfeeCCS.Step08.SaddleBesselLaplace
public import DurfeeCCS.Step08.SaddleNormalization
public import DurfeeCCS.Step08.PhaseGapParameters
import DurfeeCCS.Step08.PhaseGap
import DurfeeCCS.Step08.SaddleBesselRadicals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The outer angular term in (37) of the first-saddle approximation. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06 MeasureTheory Set

private theorem saddleBesselCutoff_exponent {n : ℕ} {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hθ : |θ| ≤ Real.pi / 2) :
    (2 * (Real.sqrt n : ℂ) * (saddleG r θ).sqrt).re ≤
      2 * saddleOmega n r - saddleGamma r * saddleOmega n r * (1 - Real.cos θ) := by
  let ψ := 1 - Real.cos θ
  let γ := saddleGamma r
  let a := (saddleS r).re
  have hψ : 0 ≤ ψ := sub_nonneg.mpr (Real.cos_le_one _)
  have hψ₁ : ψ ≤ 1 := by
    have hc := Real.cos_nonneg_of_mem_Icc (abs_le.mp hθ)
    dsimp [ψ]
    linarith only [hc]
  have hγ := (saddleGamma_bounds r).2
  have hp : γ * ψ ≤ 1 :=
    (mul_le_mul_of_nonneg_right hγ hψ).trans (by simpa only [one_mul] using hψ₁)
  have hs : Real.sqrt (1 - γ * ψ) ≤ 1 - γ * ψ / 2 := by
    apply (Real.sqrt_le_left (by linarith only [hp])).mpr
    nlinarith only [sq_nonneg (γ * ψ)]
  have ha : 0 ≤ a := ((saddleS_components hr).1.trans (saddleS_components hr).2).le
  have h := (saddleG_sqrt_re_le hr hr₁ hθ).trans (mul_le_mul_of_nonneg_left hs ha)
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * Real.sqrt (n : ℝ) by positivity)
  simp [Complex.mul_re, Complex.mul_im]
  change 2 * Real.sqrt (n : ℝ) * (saddleG r θ).sqrt.re ≤
    2 * (a * Real.sqrt n) - γ * (a * Real.sqrt n) * ψ
  linarith only [h']

private theorem saddleBesselCutoff_large_constant :
    Real.pi ^ 2 / Real.sqrt (2 * Real.pi) ≤ 3.938 := by
  have hden : (2.5066 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_sq (show 0 ≤ (2.5066 : ℝ) by norm_num)]
    apply Real.sqrt_le_sqrt
    linarith only [Real.pi_gt_d6]
  have hnum := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (2 * Real.pi))).mpr
  have h := mul_le_mul_of_nonneg_left hden (show 0 ≤ (3.938 : ℝ) by norm_num)
  nlinarith only [h, hnum]

private theorem saddleBesselCutoff_pointwise {n : ℕ} (hn : 0 < n) {r θ : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hθ : |θ| ≤ Real.pi / 2) :
    let ω := saddleOmega n r
    let γ := saddleGamma r
    ‖(Real.pi : ℂ)⁻¹ * saddleBesselKernel n (saddleG r θ)‖ ≤
      saddleAmplitude n r *
        (3.938 * Real.sqrt ω * Real.exp (-γ * ω * (1 - Real.cos θ)) +
          Real.pi ^ 2 / 2 * ω ^ 2 * Real.exp (-ω)) := by
  let ω := saddleOmega n r
  let γ := saddleGamma r
  let M := saddleAmplitude n r
  let g := saddleG r θ
  let p := g.sqrt
  let z : ℂ := 2 * (Real.sqrt n : ℂ) * p
  let B := Real.pi⁻¹ * (‖p‖ / Real.sqrt n)
  let T := Real.exp (-γ * ω * (1 - Real.cos θ))
  change ‖(Real.pi : ℂ)⁻¹ * saddleBesselKernel n g‖ ≤
    M * (3.938 * Real.sqrt ω * T + Real.pi ^ 2 / 2 * ω ^ 2 * Real.exp (-ω))
  have hω : 0 < ω := saddleOmega_pos hn hr
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnRoot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn₀
  have hM₀ : 0 ≤ M := (by positivity : 0 ≤ 2 * Real.exp (2 * ω) / (3 * Real.pi * n)).trans
    (saddleAmplitude_lower hn hr hr₁)
  have hM : Real.exp (2 * ω) ≤ M * (3 * Real.pi * n / 2) := by
    have h := (div_le_iff₀ (by positivity : 0 < 3 * Real.pi * n)).mp
      (saddleAmplitude_lower hn hr hr₁)
    change 2 * Real.exp (2 * ω) ≤ M * (3 * Real.pi * n) at h
    linarith only [h]
  have hωsq : (n : ℝ) * r ≤ ω ^ 2 := by
    rw [saddleOmega_sq]
    exact mul_le_mul_of_nonneg_left (Step07.firstSaddle_coordinates_bounds hr hr₁).1 hn₀.le
  have hg := norm_saddleG_le (show |r| ≤ 1 by rwa [abs_of_pos hr]) θ
  rw [abs_of_pos hr] at hg
  change ‖g‖ ≤ Real.pi ^ 2 / 3 * r at hg
  have hzRe : z.re = 2 * Real.sqrt n * p.re := by
    simp [z, Complex.mul_re, Complex.mul_im]
  have hzpos : 0 ≤ z.re := by rw [hzRe, principalSqrt_re_eq]; positivity
  have hzNorm : ‖z‖ = 2 * Real.sqrt n * ‖p‖ := by
    simp [z]
  have hscale : B * ‖z‖ = 2 * ‖g‖ / Real.pi := by
    dsimp only [B]
    rw [hzNorm, show ‖p‖ = Real.sqrt ‖g‖ from norm_principalSqrt _]
    field_simp [hnRoot.ne', Real.pi_ne_zero]
    nlinarith only [Real.sq_sqrt (norm_nonneg g)]
  have hK : ‖(Real.pi : ℂ)⁻¹ * saddleBesselKernel n g‖ = B * ‖besselI 1 z‖ := by
    rw [saddleBesselKernel_eq_besselI hn]
    simp [B, z, p, norm_inv, abs_of_nonneg hnRoot.le, mul_assoc]
  rw [hK]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 0 ≤ T := Real.exp_nonneg _
  by_cases hz : ω ≤ z.re
  · have hden : ω * Real.sqrt ω ≤ z.re ^ (3 / 2 : ℝ) := by
      rw [show ω * Real.sqrt ω = ω ^ (3 / 2 : ℝ) by
        rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add hω, Real.rpow_one]]
      exact Real.rpow_le_rpow hω.le hz (by norm_num)
    have hExp : Real.exp z.re ≤ (M * (3 * Real.pi * n / 2)) * T := by
      calc
        _ ≤ Real.exp (2 * ω + -γ * ω * (1 - Real.cos θ)) := by
          apply Real.exp_le_exp.mpr
          have h := saddleBesselCutoff_exponent (n := n) hr hr₁ hθ
          change z.re ≤ 2 * ω - γ * ω * (1 - Real.cos θ) at h
          linarith only [h]
        _ = Real.exp (2 * ω) * T := Real.exp_add _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hM hT
    have hmain : B * ‖besselI 1 z‖ ≤ M * (3.938 * Real.sqrt ω * T) := by
      calc
        _ ≤ B * (‖z‖ * Real.exp z.re / (Real.sqrt (2 * Real.pi) * z.re ^ (3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (norm_besselI_one_le_laplace (hω.trans_le hz)) hB
        _ = (2 * ‖g‖ / Real.pi) * Real.exp z.re /
            (Real.sqrt (2 * Real.pi) * z.re ^ (3 / 2 : ℝ)) := by rw [← hscale]; ring
        _ ≤ (2 * (Real.pi ^ 2 / 3 * r) / Real.pi) * ((M * (3 * Real.pi * n / 2)) * T) /
            (Real.sqrt (2 * Real.pi) * (ω * Real.sqrt ω)) := by gcongr
        _ = M * ((Real.pi ^ 2 / Real.sqrt (2 * Real.pi)) * ((n : ℝ) * r) /
            (ω * Real.sqrt ω) * T) := by
          field_simp [Real.pi_ne_zero, hω.ne', (Real.sqrt_pos.mpr hω).ne',
            (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne']
        _ ≤ M * ((Real.pi ^ 2 / Real.sqrt (2 * Real.pi)) * ω ^ 2 / (ω * Real.sqrt ω) * T) := by
          gcongr
        _ = M * ((Real.pi ^ 2 / Real.sqrt (2 * Real.pi)) * Real.sqrt ω * T) := by
          have hsq : ω ^ 2 / (ω * Real.sqrt ω) = Real.sqrt ω := by
            apply (div_eq_iff (by positivity : 0 < ω * Real.sqrt ω).ne').mpr
            calc
              _ = ω * (Real.sqrt ω) ^ 2 := by rw [Real.sq_sqrt hω.le]; ring
              _ = _ := by ring
          rw [mul_div_assoc, hsq]
        _ ≤ _ := by gcongr; exact saddleBesselCutoff_large_constant
    exact hmain.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (by positivity)) hM₀)
  · have hExp : Real.exp z.re ≤ (M * (3 * Real.pi * n / 2)) * Real.exp (-ω) := by
      calc
        _ ≤ Real.exp ω := Real.exp_le_exp.mpr (le_of_not_ge hz)
        _ = Real.exp (2 * ω) * Real.exp (-ω) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hM (Real.exp_nonneg _)
    have hmain : B * ‖besselI 1 z‖ ≤ M * (Real.pi ^ 2 / 2 * ω ^ 2 * Real.exp (-ω)) := by
      calc
        _ ≤ B * (‖z‖ * Real.exp z.re / 2) :=
          mul_le_mul_of_nonneg_left (norm_besselI_one_le_half_mul_exp hzpos) hB
        _ = (B * ‖z‖) * Real.exp z.re / 2 := by ring
        _ = ‖g‖ / Real.pi * Real.exp z.re := by rw [hscale]; ring
        _ ≤ (Real.pi ^ 2 / 3 * r) / Real.pi *
            ((M * (3 * Real.pi * n / 2)) * Real.exp (-ω)) := by gcongr
        _ = M * (Real.pi ^ 2 / 2 * ((n : ℝ) * r) * Real.exp (-ω)) := by
          field_simp [Real.pi_ne_zero]
        _ ≤ _ := by gcongr
    exact hmain.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (by positivity)) hM₀)

private theorem saddleBesselCutoff_cosine_gap {θ : ℝ}
    (hθ : θ ∈ Icc saddleBesselCutoff (Real.pi / 2)) :
    0.3 + 0.714 * (θ - saddleBesselCutoff) ≤ 1 - Real.cos θ := by
  let c := saddleBesselCutoff
  have hc := saddleBesselCutoff_nonneg
  have hcπ := saddleBesselCutoff_le
  have hcCos : Real.cos c = 0.7 := Real.cos_arccos (by norm_num) (by norm_num)
  have hcSin₀ : 0 ≤ Real.sin c :=
    Real.sin_nonneg_of_nonneg_of_le_pi hc (by linarith only [hcπ, Real.pi_pos])
  have hcSin : 0.714 ≤ Real.sin c := by
    apply (sq_le_sq₀ (by norm_num) hcSin₀).mp
    have h := Real.sin_sq_add_cos_sq c
    rw [hcCos] at h
    linarith only [h]
  let f (x : ℝ) := 1 - Real.cos x
  have hd (x : ℝ) : HasDerivAt f (Real.sin x) x := by
    simpa [f] using (Real.hasDerivAt_cos x).const_sub 1
  have hF : Continuous f := by unfold f; fun_prop
  have h' := (convex_Icc c (Real.pi / 2)).mul_sub_le_image_sub_of_le_deriv
    (f := f) (C := 0.714) hF.continuousOn
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      have hx' : x ∈ Icc c (Real.pi / 2) := interior_subset hx
      rw [(hd x).deriv]
      exact hcSin.trans (Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith only [hc, Real.pi_pos]) hx'.2 hx'.1))
    c (show c ∈ Icc c (Real.pi / 2) from ⟨le_rfl, hcπ⟩) θ hθ hθ.1
  dsimp [f] at h'
  change 0.3 + 0.714 * (θ - c) ≤ 1 - Real.cos θ
  linarith only [h', hcCos]

private theorem saddleBesselCutoff_exponential_integral {b c d : ℝ} (hb : 0 < b) (hcd : c ≤ d) :
    (∫ t in c..d, Real.exp (-b * (t - c))) ≤ 1 / b := by
  rw [intervalIntegral.integral_comp_sub_right (f := fun x => Real.exp (-b * x)) c, sub_self]
  rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hcd)]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) :=
      setIntegral_mono_set (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) _)
        (ae_of_all _ fun _ => Real.exp_nonneg _)
        (ae_of_all _ fun x (hx : x ∈ Ioc (0 : ℝ) (d - c)) => hx.1)
    _ = _ := by rw [integral_exp_mul_Ioi (neg_neg_of_pos hb), mul_zero,
      Real.exp_zero, neg_div_neg_eq]

/-- The second term in (37), from the two outer angular intervals. -/
theorem saddleBessel_outer_cutoff_error {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) :
    let ω := saddleOmega n r
    let γ := saddleGamma r
    let c := saddleBesselCutoff
    let K (θ : ℝ) := (Real.pi : ℂ)⁻¹ * saddleBesselKernel n (saddleG r θ)
    ((∫ θ in (-Real.pi / 2)..-c, ‖K θ‖) + (∫ θ in c..(Real.pi / 2), ‖K θ‖)) ≤
      saddleAmplitude n r * ((11.1 / γ) / Real.sqrt ω * Real.exp (-0.3 * γ * ω) +
        19 * ω ^ 2 * Real.exp (-ω)) := by
  let ω := saddleOmega n r
  let γ := saddleGamma r
  let c := saddleBesselCutoff
  let M := saddleAmplitude n r
  let K (θ : ℝ) := (Real.pi : ℂ)⁻¹ * saddleBesselKernel n (saddleG r θ)
  change ((∫ θ in (-Real.pi / 2)..-c, ‖K θ‖) + (∫ θ in c..(Real.pi / 2), ‖K θ‖)) ≤
    M * ((11.1 / γ) / Real.sqrt ω * Real.exp (-0.3 * γ * ω) + 19 * ω ^ 2 * Real.exp (-ω))
  have hω : 0 < ω := saddleOmega_pos hn hr
  have hγ : 0 < γ := (by norm_num : (0 : ℝ) < 0.55).trans_le (saddleGamma_bounds r).1
  have hc : 0 ≤ c := saddleBesselCutoff_nonneg
  have hcπ : c ≤ Real.pi / 2 := saddleBesselCutoff_le
  have hM : 0 ≤ M := (by positivity : 0 ≤ 2 * Real.exp (2 * ω) / (3 * Real.pi * (n : ℝ))).trans
    (saddleAmplitude_lower hn hr hr₁)
  have hK : Continuous K := by
    exact continuous_const.mul (continuous_saddleBesselAngular n (by rwa [abs_of_pos hr]))
  have hEven : Function.Even K := fun θ => by dsimp [K]; rw [saddleG_even r θ]
  have hSym : (∫ θ in (-Real.pi / 2)..-c, ‖K θ‖) = (∫ θ in c..(Real.pi / 2), ‖K θ‖) := by
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring]
    exact (intervalIntegral.integral_comp_neg (a := c) (b := Real.pi / 2)
      (f := fun x => ‖K x‖)).symm.trans
      (intervalIntegral.integral_congr fun θ _ => congrArg norm (hEven θ))
  let b := 0.714 * γ * ω
  let A := 3.938 * Real.sqrt ω * Real.exp (-0.3 * γ * ω)
  let D := Real.pi ^ 2 / 2 * ω ^ 2 * Real.exp (-ω)
  let h (θ : ℝ) := Real.exp (-b * (θ - c))
  have hb : 0 < b := by dsimp [b]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hH : Continuous h := by unfold h; fun_prop
  have hBound (θ : ℝ) (hθ : θ ∈ Icc c (Real.pi / 2)) : ‖K θ‖ ≤ M * (A * h θ + D) := by
    have hθ' : |θ| ≤ Real.pi / 2 := by
      rw [abs_of_nonneg (hc.trans hθ.1)]
      exact hθ.2
    refine (saddleBesselCutoff_pointwise hn hr hr₁ hθ').trans ?_
    apply mul_le_mul_of_nonneg_left _ hM
    refine add_le_add ?_ (le_refl D)
    have hgap := saddleBesselCutoff_cosine_gap hθ
    have hE := mul_le_mul_of_nonpos_left hgap (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hγ.le) hω.le)
    have heq : -γ * ω * (0.3 + 0.714 * (θ - c)) =
        -0.3 * γ * ω + -b * (θ - c) := by dsimp [b]; ring
    rw [heq] at hE
    have hProd : Real.exp (-γ * ω * (1 - Real.cos θ)) ≤ Real.exp (-0.3 * γ * ω) * h θ := by
      unfold h
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hE
    simpa only [A, mul_assoc] using
      mul_le_mul_of_nonneg_left hProd (show 0 ≤ 3.938 * Real.sqrt ω by positivity)
  have hInt : (∫ θ in c..(Real.pi / 2), ‖K θ‖) ≤
      M * (A * (1 / b) + (Real.pi / 2 - c) * D) := by
    calc
      _ ≤ ∫ θ in c..(Real.pi / 2), M * (A * h θ + D) :=
        intervalIntegral.integral_mono_on hcπ (hK.norm.intervalIntegrable _ _)
          ((continuous_const.mul ((continuous_const.mul hH).add continuous_const)).intervalIntegrable
            _ _) hBound
      _ = M * (A * (∫ θ in c..(Real.pi / 2), h θ) + (Real.pi / 2 - c) * D) := by
        have hI : IntervalIntegrable (fun θ => A * h θ) volume c (Real.pi / 2) :=
          (continuous_const.mul hH).intervalIntegrable _ _
        have hD' : IntervalIntegrable (fun _ : ℝ => D) volume c (Real.pi / 2) :=
          continuous_const.intervalIntegrable _ _
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hI hD',
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ _ := by
        have hsmall : (∫ θ in c..(Real.pi / 2), h θ) ≤ 1 / b :=
          saddleBesselCutoff_exponential_integral hb hcπ
        gcongr
  have hhi : 2 * A * (1 / b) ≤ (11.1 / γ) / Real.sqrt ω * Real.exp (-0.3 * γ * ω) := by
    have heq : 2 * A * (1 / b) =
        ((2 * 3.938 / 0.714) / γ) / Real.sqrt ω * Real.exp (-0.3 * γ * ω) := by
      dsimp [A, b]
      field_simp [hγ.ne', hω.ne', (Real.sqrt_pos.mpr hω).ne']
      exact Real.sq_sqrt hω.le
    rw [heq]
    gcongr
    norm_num
  have hlo : 2 * (Real.pi / 2 - c) * D ≤ 19 * ω ^ 2 * Real.exp (-ω) := by
    calc
      _ ≤ Real.pi * D := mul_le_mul_of_nonneg_right (by linarith only [hc]) hD
      _ = (Real.pi ^ 3 / 2) * ω ^ 2 * Real.exp (-ω) := by dsimp [D]; ring
      _ ≤ _ := by
        have hπ : Real.pi ^ 3 / 2 ≤ 19 := by
          linarith only [pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 3]
        gcongr
  rw [hSym]
  calc
    _ ≤ 2 * (M * (A * (1 / b) + (Real.pi / 2 - c) * D)) := by linarith only [hInt]
    _ = M * (2 * A * (1 / b) + 2 * (Real.pi / 2 - c) * D) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hhi hlo) hM

end DurfeeCCS.Step08
