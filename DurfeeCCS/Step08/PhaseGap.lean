module

public import DurfeeCCS.Step08.PhaseGapComponents
public import DurfeeCCS.Step08.PhaseGapParameters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The saddle inequalities in (25)–(30). -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex Set DurfeeCCS.Step06
open scoped Real

/-- The normalized gap in the real part of the saddle exponent. -/
noncomputable def saddleGap (r θ η : ℝ) : ℝ :=
  1 - ((saddleG r θ).re + η*(saddleG r θ).im) / ((saddleS r).re^2*(1+η^2))

/-- Equation (28) in complex square coordinates. -/
theorem square_eta_gap (z : ℂ) (η : ℝ) :
    z.re^2 - ((z^2).re + η*(z^2).im)/(1+η^2) = (z.re*η-z.im)^2/(1+η^2) := by
  rw [pow_two z, Complex.mul_re, Complex.mul_im]
  field_simp
  ring

/-- The variational expression in (29) attains its maximum at `z.im / z.re`. -/
theorem square_eta_isGreatest {z : ℂ} (hre : 0 < z.re) (him : 0 ≤ z.im) :
    IsGreatest ((fun η : ℝ => ((z^2).re + η*(z^2).im)/(1+η^2)) '' Ici 0) (z.re^2) := by
  constructor
  · refine ⟨z.im/z.re, div_nonneg him hre.le, ?_⟩
    have h := square_eta_gap z (z.im/z.re)
    rw [show z.re*(z.im/z.re)-z.im = 0 by field_simp; ring,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_div] at h
    exact (sub_eq_zero.mp h).symm
  · rintro _ ⟨η, hη, rfl⟩
    have h := square_eta_gap z η
    exact sub_nonneg.mp (by rw [h]; positivity)

/-- Equation (29) in supremum form. -/
theorem square_eta_sSup {z : ℂ} (hre : 0 < z.re) (him : 0 ≤ z.im) :
    sSup ((fun η : ℝ => ((z^2).re + η*(z^2).im)/(1+η^2)) '' Ici 0) = z.re^2 :=
  (square_eta_isGreatest hre him).csSup_eq

/-- Equation (30) at the actual saddle. -/
theorem saddle_axis_eta_gap {r : ℝ} (hr : 0 < r) (η : ℝ) :
    1 - ((saddleS r^2).re + η*(saddleS r^2).im) / ((saddleS r).re^2*(1+η^2)) =
      (η-saddleSlope r)^2/(1+η^2) := by
  let a := (saddleS r).re
  let b := (saddleS r).im
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  unfold saddleSlope
  rw [pow_two (saddleS r), Complex.mul_re, Complex.mul_im]
  change 1 - ((a*a-b*b)+η*(a*b+b*a))/(a^2*(1+η^2)) = (η-b/a)^2/(1+η^2)
  field_simp
  ring

private theorem saddle_components_to_gap {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hη : 0 ≤ η) :
    ((η-saddleSlope r)^2 + r*saddleCurvature r*Real.sin θ^2 +
      2*saddleCurvature r*η*(1-Real.cos θ))/(1+η^2) ≤ saddleGap r θ η := by
  let a := (saddleS r).re
  let c := saddleCurvature r
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  have ha' : (saddleS r).re ≠ 0 := ha.ne'
  have hg := saddleG_component_gaps hr hr₁ θ
  have hmul := mul_le_mul_of_nonneg_left hg.2 hη
  have hReq : r*c*Real.sin θ^2*a^2 = r^2/(1+r^2)*Real.sin θ^2 := by
    dsimp [c, saddleCurvature, a]
    field_simp [ha']
  have hIeq : 2*c*η*(1-Real.cos θ)*a^2 = η*(2*r/(1+r^2)*(1-Real.cos θ)) := by
    dsimp [c, saddleCurvature, a]
    field_simp [ha']
  have hBound :
      (r*c*Real.sin θ^2+2*c*η*(1-Real.cos θ))*a^2 ≤
        ((saddleS r^2).re + η*(saddleS r^2).im) - ((saddleG r θ).re+η*(saddleG r θ).im) := by
    rw [add_mul, hReq, hIeq]
    linarith only [hg.1, hmul]
  have hBase := saddle_axis_eta_gap hr η
  change ((η-saddleSlope r)^2+r*c*Real.sin θ^2+2*c*η*(1-Real.cos θ))/(1+η^2) ≤
    1 - ((saddleG r θ).re+η*(saddleG r θ).im)/(a^2*(1+η^2))
  change 1 - ((saddleS r^2).re+η*(saddleS r^2).im)/(a^2*(1+η^2)) = _ at hBase
  rw [add_assoc, add_div, ← hBase]
  have hPos : 0 < a^2*(1+η^2) := by positivity
  have hScaled : (r*c*Real.sin θ^2+2*c*η*(1-Real.cos θ))/(1+η^2) ≤
      (((saddleS r^2).re+η*(saddleS r^2).im)-((saddleG r θ).re+η*(saddleG r θ).im))/
        (a^2*(1+η^2)) := by
    apply (le_div_iff₀ hPos).mpr
    convert hBound using 1
    field_simp
  rw [sub_div] at hScaled
  linarith only [hScaled]

/-- The global angular gap in (27). -/
theorem saddleG_gap_all {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hη : 0 ≤ η) :
    (η-saddleSlope r)^2/(1+η^2) ≤ saddleGap r θ η := by
  have hC : 0 ≤ saddleCurvature r := (lt_trans (by norm_num) (saddleCurvature_bounds hr hr₁).2.2).le
  refine le_trans ?_ (saddle_components_to_gap hr hr₁ hη)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h₁ : 0 ≤ r*saddleCurvature r*Real.sin θ^2 := by positivity
  have h₂ : 0 ≤ 2*saddleCurvature r*η*(1-Real.cos θ) := by
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
  linarith only [h₁, h₂]

/-- The two bounds in (25) for the central angular interval. -/
theorem saddleG_gap_main {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hθ : |θ| ≤ Real.pi/2) (hη : 0 ≤ η) :
    let ψ := 1-Real.cos θ
    let ρ := saddleSlope r
    let κ := saddleCurvature r
    saddleGamma r*ψ ≤ ((η-ρ)^2+r*κ*ψ*(2-ψ)+2*κ*η*ψ)/(1+η^2) ∧
      ((η-ρ)^2+r*κ*ψ*(2-ψ)+2*κ*η*ψ)/(1+η^2) ≤ saddleGap r θ η := by
  let ψ := 1-Real.cos θ
  let ρ := saddleSlope r
  let κ := saddleCurvature r
  let γ := saddleGamma r
  have hψ₀ : 0 ≤ ψ := sub_nonneg.mpr (Real.cos_le_one θ)
  obtain ⟨h₁, h₂⟩ := abs_le.mp hθ
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨h₁, h₂⟩
  have hψ₁ : ψ ≤ 1 := by dsimp [ψ]; linarith only [hcos]
  have hκ : 0 ≤ κ := (lt_trans (by norm_num) (saddleCurvature_bounds hr hr₁).2.2).le
  obtain ⟨hρ, hρκ, hγ⟩ := saddleSlope_curvature_bounds hr hr₁
  change 1 ≤ ρ^2+r*κ at hρ
  change 0 ≤ ρ-κ at hρκ
  change γ ≤ 1-ρ+κ at hγ
  constructor
  · apply (le_div_iff₀ (show 0 < 1+η^2 by positivity)).mpr
    have hA := mul_le_mul_of_nonneg_left (show 2*η ≤ 1+η^2 by nlinarith [sq_nonneg (η-1)]) hρκ
    have hB := mul_le_mul_of_nonneg_right hγ (show 0 ≤ 1+η^2 by positivity)
    have hC : γ*(1+η^2) ≤ (η-ρ)^2+r*κ+2*κ*η := by nlinarith only [hA, hB, hρ]
    have hC' := mul_le_mul_of_nonneg_right hC hψ₀
    have hD := mul_le_of_le_one_left (sq_nonneg (η-ρ)) hψ₁
    have hE := mul_le_mul_of_nonneg_left (show 1 ≤ 2-ψ by linarith only [hψ₁])
      (show 0 ≤ r*κ*ψ by positivity)
    nlinarith only [hC', hD, hE]
  · have hsin : Real.sin θ^2 = ψ*(2-ψ) := by
      dsimp [ψ]
      nlinarith only [Real.sin_sq_add_cos_sq θ]
    have h := saddle_components_to_gap (θ := θ) hr hr₁ hη
    rw [hsin] at h
    simpa only [mul_assoc] using h

/-- The real part of the principal square root obeys (26) at both angular endpoints. -/
theorem saddleG_sqrt_re_le {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hθ : |θ| ≤ Real.pi/2) :
    ((saddleG r θ).sqrt).re ≤ (saddleS r).re * Real.sqrt (1-saddleGamma r*(1-Real.cos θ)) := by
  let z := (saddleG r θ).sqrt
  let a := (saddleS r).re
  let p := 1-saddleGamma r*(1-Real.cos θ)
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  have hz : z^2 = saddleG r θ := principalSqrt_sq _
  have hIm := saddleG_im_nonneg_of_cos_nonneg hr hr₁ (Real.cos_nonneg_of_mem_Icc (abs_le.mp hθ))
  have hzr : 0 ≤ z.re := by
    dsimp [z]
    rw [Complex.sqrt_eq_real_add_ite, ite_eq_left hIm]
    simpa [Complex.mul_re] using
      (Real.sqrt_nonneg ((‖saddleG r θ‖+(saddleG r θ).re)/2))
  have hzi : 0 ≤ z.im := by
    dsimp [z]
    rw [Complex.sqrt_eq_real_add_ite, ite_eq_left hIm]
    simpa [Complex.mul_im] using
      (Real.sqrt_nonneg ((‖saddleG r θ‖-(saddleG r θ).re)/2))
  change z.re ≤ a*Real.sqrt p
  rcases eq_or_lt_of_le hzr with heq | hpos
  · rw [← heq]
    positivity
  have hGreat := square_eta_isGreatest hpos hzi
  obtain ⟨η, hη, heq⟩ := hGreat.1
  change ((z^2).re+η*(z^2).im)/(1+η^2) = z.re^2 at heq
  rw [hz] at heq
  have hg := ((saddleG_gap_main hr hr₁ hθ hη).1).trans (saddleG_gap_main hr hr₁ hθ hη).2
  unfold saddleGap at hg
  change saddleGamma r*(1-Real.cos θ) ≤
    1 - ((saddleG r θ).re+η*(saddleG r θ).im)/(a^2*(1+η^2)) at hg
  have hdiv : ((saddleG r θ).re+η*(saddleG r θ).im)/(a^2*(1+η^2)) = z.re^2/a^2 := by
    rw [mul_comm (a^2), ← div_div, heq]
  rw [hdiv] at hg
  have hp : z.re^2 ≤ a^2*p := by
    rw [mul_comm (a^2)]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mp
    dsimp [p]
    linarith only [hg]
  calc
    _ = Real.sqrt (z.re^2) := (Real.sqrt_sq hzr).symm
    _ ≤ Real.sqrt (a^2*p) := Real.sqrt_le_sqrt hp
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

/-- The outer angular bound following (27). -/
theorem saddleG_gap_opposite {r θ η : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hθ₁ : Real.pi/2 < |θ|) (hθ₂ : |θ| ≤ Real.pi) (hη : 0 ≤ η) :
    1-r/2 ≤ saddleGap r θ η := by
  let a := (saddleS r).re
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  have hcos : Real.cos θ ≤ 0 := by
    rw [← Real.cos_abs]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le hθ₁.le (by linarith only [hθ₂, Real.pi_pos])
  have hIm := saddleG_im_nonpos_of_cos_nonpos hr hr₁ hcos
  have hRe : (saddleG r θ).re ≤ r^2/2 := by
    have h := (saddleG_component_gaps hr hr₁ θ).1
    have h' : 0 ≤ r^2 / (1+r^2) * Real.sin θ^2 := by positivity
    rw [saddleS_sq] at h
    linarith only [h, h', saddlePhaseSquare_re_le_sq_half hr]
  have har : r ≤ a^2 := (DurfeeCCS.Step07.firstSaddle_coordinates_bounds hr hr₁).1
  have h : r^2/2 ≤ (r/2)*(a^2*(1+η^2)) := by
    have hmul := mul_le_mul_of_nonneg_left har (show 0 ≤ r/2 by positivity)
    have hh := mul_nonneg (show 0 ≤ r/2*a^2 by positivity) (sq_nonneg η)
    nlinarith only [hmul, hh]
  have hDiv : ((saddleG r θ).re+η*(saddleG r θ).im)/(a^2*(1+η^2)) ≤ r/2 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith only [hRe, h, mul_nonpos_of_nonneg_of_nonpos hη hIm])
  unfold saddleGap
  linarith only [hDiv]

end DurfeeCCS.Step08
