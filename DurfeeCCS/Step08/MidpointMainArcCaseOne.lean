module

public import DurfeeCCS.Step08.MidpointMainArc
public import DurfeeCCS.Step08.MidpointRay
public import DurfeeCCS.Step08.FirstSaddleSubregions
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integration of the three Case 1 subregions in (41). -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06 DurfeeCCS.Step07 MeasureTheory Set intervalIntegral

private theorem midpoint_caseOne_error_le {n : ℕ} (hn : 6400 ≤ n) {r r₀ θ η T : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ r₀) (hr₁ : r₀ ≤ 1 / 4) (hη : 0 ≤ η) (hηT : η ≤ T) :
    ‖pairedLog r θ (verticalPoint (saddleU n r) (saddleU n r * η)) -
      saddleG r θ / verticalPoint (saddleU n r) (saddleU n r * η)‖ ≤
      (1 + T ^ 2) * (r₀ * firstSaddleU0 r₀ / (4 * (1 - r₀))) := by
  have hu := saddleU_pos (by omega : 0 < n) hr
  have hu' : saddleU n r ≤ firstSaddleU0 r₀ := firstSaddleRadius_leU0 hn hr hr₀ (by linarith)
  have hr₁' : r < 1 := by linarith
  have ht := pow_le_pow_left₀ hη hηT 2
  have hN : saddleU n r * r ≤ firstSaddleU0 r₀ * r₀ :=
    mul_le_mul hu' hr₀ hr.le (hu.le.trans hu')
  have hr0 : 0 < r₀ := hr.trans_le hr₀
  have hd : (0 : ℝ) < 4 * (1 - r₀) := by linarith
  have hb : saddleU n r * r / (4 * (1 - r)) ≤ r₀ * firstSaddleU0 r₀ / (4 * (1 - r₀)) := by
    rw [mul_comm r₀]
    have hN₀ : 0 ≤ firstSaddleU0 r₀ * r₀ := mul_nonneg (Real.sqrt_nonneg _) hr0.le
    exact div_le_div₀ hN₀ hN hd (by linarith)
  rw [verticalPoint_mul]
  refine (norm_pairedLog_sub_saddleG_div_le r θ _ η hr.le hr₁' hu).trans ?_
  rw [show saddleU n r * (1 + η ^ 2) * r / (4 * (1 - r)) =
    (1 + η ^ 2) * (saddleU n r * r / (4 * (1 - r))) by ring]
  exact mul_le_mul (by linarith only [ht]) hb (by positivity) (by positivity)

private theorem integral_gaussian_interval_bound {b a c : ℝ} (hb : 0 < b) (hac : a ≤ c) :
    (∫ x in a..c, Real.exp (-b * x ^ 2)) ≤ Real.sqrt (Real.pi / b) := by
  rw [integral_of_le hac, ← integral_gaussian]
  exact setIntegral_le_integral (integrable_exp_neg_mul_sq hb) (ae_of_all _ fun _ => Real.exp_nonneg _)

private theorem integral_const_bound {f : ℝ → ℝ} (hf : Continuous f) {a b C : ℝ}
    (hab : a ≤ b) (hC : ∀ x ∈ Ioo a b, f x ≤ C) :
    (∫ x in a..b, f x) ≤ (b - a) * C := by
  change _ ≤ (b - a) • C
  rw [← intervalIntegral.integral_const]
  exact intervalIntegral.integral_mono_on_of_le_Ioo hab (hf.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) hC

private theorem gaussian_caseOne_constants {ω : ℝ} (hω : 0 < ω) :
    Real.sqrt (Real.pi / (ω * 0.55 / Real.pi ^ 2)) * Real.sqrt (Real.pi / (ω / 20)) =
      Real.pi ^ 2 * Real.sqrt (20 / 0.55) / ω := by
  have hL : 0 ≤ Real.sqrt (Real.pi / (ω * 0.55 / Real.pi ^ 2)) *
      Real.sqrt (Real.pi / (ω / 20)) := by positivity
  have hR : 0 ≤ Real.pi ^ 2 * Real.sqrt (20 / 0.55) / ω := by positivity
  apply (sq_eq_sq₀ hL hR).mp
  rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  field_simp [hω.ne', Real.pi_ne_zero]

set_option maxHeartbeats 1200000 in
/-- The first term of (40) in Case 1, in the rescaled form of (41). -/
theorem firstSaddleMainArcBudget_le_caseOne {n : ℕ} (hn : 6400 ≤ n) {r r₀ : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ r₀) (hr₁ : r₀ ≤ 1 / 4) :
    firstSaddleMainArcBudget n r ≤ firstSaddleB r₀ (saddleOmega n r) := by
  let f := firstSaddleMainArcKernel n r
  let ω := saddleOmega n r
  let ρ := saddleSlope r
  let d := 5 * r₀ * firstSaddleU0 r₀ / (2 * (1 - r₀))
  let e := 257 * r₀ * firstSaddleU0 r₀ / (4 * (1 - r₀))
  let D := Real.exp d - 1
  let E := Real.exp e - 1
  let A := Real.sqrt (Real.pi / (ω * 0.55 / Real.pi ^ 2))
  let G (η : ℝ) := Real.exp (-(ω / 20) * (η - ρ) ^ 2)
  let B := Real.exp (-(1 - r₀ / 2) * ω) * D
  let C := Real.exp (-0.4 * ω) * E
  have hn' : 0 < n := by omega
  have hω : 0 < ω := saddleOmega_pos hn' hr
  have hp := Real.pi_pos
  have hr0 : 0 < r₀ := hr.trans_le hr₀
  have hr' : r ≤ 1 := by linarith
  have hden₀ : 0 < 1 - r₀ := by linarith
  have hd₀ : 0 ≤ d := by dsimp [d, firstSaddleU0]; positivity
  have hD : 0 ≤ D := sub_nonneg.mpr (Real.one_le_exp hd₀)
  have hDf (η θ : ℝ) (hη : 0 ≤ η) (hη₃ : η ≤ 3) :
      Real.exp ‖pairedLog r θ (verticalPoint (saddleU n r) (saddleU n r * η)) -
        saddleG r θ / verticalPoint (saddleU n r) (saddleU n r * η)‖ - 1 ≤ D := by
    apply sub_le_sub_right (Real.exp_le_exp.mpr ?_) _
    refine (midpoint_caseOne_error_le hn hr hr₀ hr₁ hη hη₃).trans_eq ?_
    dsimp only [d]
    field_simp [hden₀.ne']
    ring
  have hEf (η θ : ℝ) (hη : 0 ≤ η) (hη₁₆ : η ≤ 16) :
      Real.exp ‖pairedLog r θ (verticalPoint (saddleU n r) (saddleU n r * η)) -
        saddleG r θ / verticalPoint (saddleU n r) (saddleU n r * η)‖ - 1 ≤ E := by
    apply sub_le_sub_right (Real.exp_le_exp.mpr ?_) _
    refine (midpoint_caseOne_error_le hn hr hr₀ hr₁ hη hη₁₆).trans_eq ?_
    dsimp only [e]
    ring
  have hcont : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := continuous_firstSaddleMainArcKernel hn' hr hr'
  have hθcont (η : ℝ) : Continuous (f η) := by
    have hh := hcont.comp (continuous_const.prodMk continuous_id : Continuous (fun θ : ℝ => (η, θ)))
    simpa only [Function.comp_def] using hh
  have hηcont : Continuous (fun η => ∫ θ in -Real.pi..Real.pi, f η θ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont _ _
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hCore (η : ℝ) (hη₀ : 0 ≤ η) (hη₃ : η ≤ 3) :
      (∫ θ in (-Real.pi / 2)..(Real.pi / 2), f η θ) ≤ (G η * D) * A := by
    let H (θ : ℝ) := Real.exp (-(ω * 0.55 / Real.pi ^ 2) * θ ^ 2)
    have hH : Continuous H := by dsimp [H]; fun_prop
    calc
      _ ≤ ∫ θ in (-Real.pi / 2)..(Real.pi / 2), (G η * D) * H θ := by
        apply intervalIntegral.integral_mono_on (by linarith)
          ((hθcont η).intervalIntegrable _ _) ((hH.const_mul _).intervalIntegrable _ _)
        intro θ hθ
        have hangle : |θ| ≤ Real.pi / 2 := abs_le.mpr (by simpa [neg_div] using hθ)
        have hgap := saddleGap_central_eta_le_three hr hr' hη₀ hη₃ hangle
        have hpow : Real.exp (-ω * saddleGap r θ η) ≤ G η * H θ := by
          dsimp only [G, H]
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          calc
            _ ≤ -ω * ((η - ρ) ^ 2 / 20 + 0.55 * θ ^ 2 / Real.pi ^ 2) :=
              mul_le_mul_of_nonpos_left hgap (by linarith)
            _ = _ := by ring
        unfold f firstSaddleMainArcKernel
        exact (mul_le_mul hpow (hDf η θ hη₀ hη₃)
          (sub_nonneg.mpr (Real.one_le_exp (norm_nonneg _))) (by positivity)).trans_eq (by ring)
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (integral_gaussian_interval_bound (by positivity) (by linarith))
          (mul_nonneg (Real.exp_nonneg _) hD)
  have hSide (η θ : ℝ) (hη₀ : 0 ≤ η) (hη₃ : η ≤ 3)
      (hθlo : Real.pi / 2 < |θ|) (hθhi : |θ| ≤ Real.pi) : f η θ ≤ B := by
    have hgap := saddleGap_opposite_of_radius_le hr hr' hr₀ hη₀ hθlo hθhi
    have hpow : Real.exp (-ω * saddleGap r θ η) ≤ Real.exp (-(1 - r₀ / 2) * ω) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul, mul_neg, mul_comm] using mul_le_mul_of_nonpos_right hgap (show -ω ≤ 0 by linarith)
    unfold f firstSaddleMainArcKernel B
    exact mul_le_mul hpow (hDf η θ hη₀ hη₃)
      (sub_nonneg.mpr (Real.one_le_exp (norm_nonneg _))) (by positivity)
  have hLow (η : ℝ) (hη₀ : 0 ≤ η) (hη₃ : η ≤ 3) :
      (∫ θ in -Real.pi..Real.pi, f η θ) ≤ (A * D) * G η + Real.pi * B := by
    have hleft := integral_const_bound (hθcont η) (C := B) (show -Real.pi ≤ -Real.pi / 2 by linarith)
      (fun θ hθ => hSide η θ hη₀ hη₃ (by rw [abs_of_neg (by linarith [hθ.2])]; linarith [hθ.2])
        (abs_le.mpr ⟨hθ.1.le, by linarith [hθ.2]⟩))
    have hright := integral_const_bound (hθcont η) (C := B) (show Real.pi / 2 ≤ Real.pi by linarith)
      (fun θ hθ => hSide η θ hη₀ hη₃ (by rw [abs_of_pos (by linarith [hθ.1])]; exact hθ.1)
        (abs_le.mpr ⟨by linarith [hθ.1], hθ.2.le⟩))
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hθcont η).intervalIntegrable (-Real.pi) (Real.pi / 2)) ((hθcont η).intervalIntegrable _ _),
      ← intervalIntegral.integral_add_adjacent_intervals
        ((hθcont η).intervalIntegrable (-Real.pi) (-Real.pi / 2)) ((hθcont η).intervalIntegrable _ _)]
    linarith only [hleft, hright, hCore η hη₀ hη₃]
  have hHigh (η : ℝ) (hη₃ : 3 ≤ η) (hη₁₆ : η ≤ 16) :
      (∫ θ in -Real.pi..Real.pi, f η θ) ≤ (2 * Real.pi) * C := by
    have h := integral_const_bound (hθcont η) (C := C) (show -Real.pi ≤ Real.pi by linarith)
      (fun θ _ => ?_)
    · linarith only [h]
    · have hgap := saddleGap_eta_ge_three (θ := θ) hr hr' hη₃
      have hpow : Real.exp (-ω * saddleGap r θ η) ≤ Real.exp (-0.4 * ω) := by
        apply Real.exp_le_exp.mpr
        simpa only [neg_mul, mul_neg, mul_comm] using mul_le_mul_of_nonpos_right hgap (show -ω ≤ 0 by linarith)
      unfold f firstSaddleMainArcKernel C
      exact mul_le_mul hpow (hEf η θ (by linarith) hη₁₆)
        (sub_nonneg.mpr (Real.one_le_exp (norm_nonneg _))) (by positivity)
  have hLower :
      (∫ η in (0 : ℝ)..3, ∫ θ in -Real.pi..Real.pi, f η θ) ≤
        (Real.pi ^ 2 * Real.sqrt (20 / 0.55) / ω) * D + 3 * Real.pi * B := by
    calc
      _ ≤ ∫ η in (0 : ℝ)..3, ((A * D) * G η + Real.pi * B) := by
        exact intervalIntegral.integral_mono_on (by norm_num) (hηcont.intervalIntegrable _ _)
          (((hG.const_mul _).add continuous_const).intervalIntegrable _ _)
          (fun η hη => hLow η hη.1 hη.2)
      _ = (A * D) * (∫ η in (0 : ℝ)..3, G η) + 3 * (Real.pi * B) := by
        rw [intervalIntegral.integral_add ((hG.const_mul _).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        norm_num
      _ ≤ _ := by
        have hInt : (∫ η in (0 : ℝ)..3, G η) ≤ Real.sqrt (Real.pi / (ω / 20)) := by
          dsimp only [G]
          rw [intervalIntegral.integral_comp_sub_right
            (f := fun η => Real.exp (-(ω / 20) * η ^ 2))]
          exact integral_gaussian_interval_bound (by positivity) (by linarith)
        have hA : 0 ≤ A := Real.sqrt_nonneg _
        refine (add_le_add (mul_le_mul_of_nonneg_left hInt (mul_nonneg hA hD))
          (le_rfl : 3 * (Real.pi * B) ≤ 3 * (Real.pi * B))).trans_eq ?_
        have hGauss : A * Real.sqrt (Real.pi / (ω / 20)) =
            Real.pi ^ 2 * Real.sqrt (20 / 0.55) / ω := gaussian_caseOne_constants hω
        rw [mul_right_comm A D, hGauss]
        ring
  have hUpper :
      (∫ η in (3 : ℝ)..16, ∫ θ in -Real.pi..Real.pi, f η θ) ≤ 13 * (2 * Real.pi) * C := by
    have hh := integral_const_bound hηcont (C := (2 * Real.pi) * C) (by norm_num : (3 : ℝ) ≤ 16)
      (fun η hη => hHigh η hη.1.le hη.2.le)
    linarith only [hh]
  unfold firstSaddleMainArcBudget
  change 3 * ω / (4 * Real.pi) * (∫ η in (0 : ℝ)..16, ∫ θ in -Real.pi..Real.pi, f η θ) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hηcont.intervalIntegrable (0 : ℝ) 3) (hηcont.intervalIntegrable _ _)]
  refine (mul_le_mul_of_nonneg_left (add_le_add hLower hUpper) (by positivity)).trans_eq ?_
  change 3 * ω / (4 * Real.pi) *
     ((Real.pi ^ 2 * Real.sqrt (20 / 0.55) / ω) * D + 3 * Real.pi * B +
       13 * (2 * Real.pi) * C) =
    0.75 * Real.pi * Real.sqrt (20 / 0.55) * D + 2.25 * ω * D * Real.exp (-(1 - r₀ / 2) * ω) +
      19.5 * ω * E * Real.exp (-0.4 * ω)
  dsimp only [B, C]
  field_simp [hω.ne', Real.pi_ne_zero]
  ring

end DurfeeCCS.Step08
