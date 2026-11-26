module

public import DurfeeCCS.Step08.DurfeeContour

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Converting the four pointwise minor-arc estimates to the page 22 envelope. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07

def FirstSaddleArcEstimates (r r₀ u v θ : ℝ) : Prop :=
  let A := ‖pairedLog r θ (verticalPoint u v)‖ / (r / u)
  A ≤ firstSaddleOffArcs r₀ u ∨ A ≤ firstSaddleHighDenominatorArc r₀ u ∨
  A ≤ firstSaddlePiArc r₀ u ∨ A ≤ 0.478

/-- Each of the four minor arcs inherits the strict numerical envelope. -/
theorem norm_pairedLog_lt_minorEnvelope {n : ℕ} (hn : 6400 ≤ n)
    {r r₀ β off high πBound μ v θ : ℝ}
    (hr : 0 < r) (hrr : r ≤ r₀) (hr₀ : r₀ ≤ 1) (hβ : 0 < β)
    (ha : β * r ≤ (saddleS r).re ^ 2)
    (hrow : FirstSaddleArcRow r₀ β off high πBound μ)
    (hArc : FirstSaddleArcEstimates r r₀ (saddleU n r) v θ) :
    ‖pairedLog r θ (verticalPoint (saddleU n r) v)‖ < μ * saddleOmega n r := by
  let u := saddleU n r
  let ω := saddleOmega n r
  have hu : 0 < u := saddleU_pos (by omega) hr
  have hw : 0 < ω := saddleOmega_pos (by omega) hr
  have hratio : r / u ≤ ω / β := by
    rw [div_le_div_iff₀ hu hβ]
    calc
      _ = β * r := mul_comm _ _
      _ ≤ _ := ha
      _ = u * ω := (saddleU_mul_omega (by omega : 0 < n) r).symm
      _ = _ := mul_comm _ _
  obtain ⟨hO,hH,hV,hZ⟩ := hrow.saddleEnvelope hn hr hrr hr₀ hβ
  let A := ‖pairedLog r θ (verticalPoint u v)‖ / (r / u)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hBound : A / β < μ := by
    rcases hArc with h | h | h | h
    · exact (div_le_div_of_nonneg_right h hβ.le).trans_lt hO
    · exact (div_le_div_of_nonneg_right h hβ.le).trans_lt hH
    · exact (div_le_div_of_nonneg_right h hβ.le).trans_lt hV
    · exact (div_le_div_of_nonneg_right h hβ.le).trans_lt hZ
  change ‖pairedLog r θ (verticalPoint u v)‖ < μ * ω
  calc
    _ = A * (r / u) := by dsimp only [A]; rw [div_mul_cancel₀ _ (div_pos hr hu).ne']
    _ ≤ A * (ω / β) := mul_le_mul_of_nonneg_left hratio hA
    _ = (A / β) * ω := by ring
    _ < _ := mul_lt_mul_of_pos_right hBound hw

theorem norm_pairedLog_le_minorEnvelope {n : ℕ} (hn : 6400 ≤ n)
    {r r₀ β off high πBound μ v θ : ℝ}
    (hr : 0 < r) (hrr : r ≤ r₀) (hr₀ : r₀ ≤ 1) (hβ : 0 < β)
    (ha : β * r ≤ (saddleS r).re ^ 2)
    (hrow : FirstSaddleArcRow r₀ β off high πBound μ)
    (hArc : FirstSaddleArcEstimates r r₀ (saddleU n r) v θ) :
    ‖pairedLog r θ (verticalPoint (saddleU n r) v)‖ ≤ μ * saddleOmega n r :=
  (norm_pairedLog_lt_minorEnvelope hn hr hrr hr₀ hβ ha hrow hArc).le

/-- The strict bound on the real part divided by `ω` in the page 22 table. -/
theorem re_pairedLog_div_omega_lt_minorEnvelope {n : ℕ} (hn : 6400 ≤ n)
    {r r₀ β off high πBound μ v θ : ℝ}
    (hr : 0 < r) (hrr : r ≤ r₀) (hr₀ : r₀ ≤ 1) (hβ : 0 < β)
    (ha : β * r ≤ (saddleS r).re ^ 2)
    (hrow : FirstSaddleArcRow r₀ β off high πBound μ)
    (hArc : FirstSaddleArcEstimates r r₀ (saddleU n r) v θ) :
    (pairedLog r θ (verticalPoint (saddleU n r) v)).re / saddleOmega n r < μ :=
  (div_lt_iff₀ (saddleOmega_pos (by omega : 0 < n) hr)).2
    ((Complex.re_le_norm _).trans_lt (norm_pairedLog_lt_minorEnvelope hn hr hrr hr₀ hβ ha hrow hArc))

theorem durfee_minor_error_case_two {n : ℕ} (hn : 0 < n) {r μ : ℝ}
    (hr : 1 / 4 < r) (hr₁ : r ≤ 1) (hμ : 0 ≤ μ)
    (hlog : ∀ v, 16 * saddleU n r ≤ |v| → |v| ≤ Real.pi →
      ∀ θ, (pairedLog r θ (verticalPoint (saddleU n r) v)).re ≤ μ * saddleOmega n r) :
    let u := saddleU n r
    let ω := saddleOmega n r
    Real.exp ω / (2 * Real.pi) *
      (∫ v in Icc (-Real.pi) Real.pi \ Icc (-(16 * u)) (16 * u),
        ‖durfeeExponentialMean r u v‖) ≤
      saddleAmplitude n r * firstSaddleMinorArcError ω μ := by
  dsimp only
  let u := saddleU n r
  let ω := saddleOmega n r
  let s := Icc (-Real.pi) Real.pi \ Icc (-(16 * u)) (16 * u)
  have hr' : 0 < r := by linarith
  have hrabs : |r| ≤ 1 := by rwa [abs_of_pos hr']
  have hu := saddleU_pos hn hr'
  have hω : 0 < ω := saddleOmega_pos hn hr'
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsi : MeasurableSet s := measurableSet_Icc.diff measurableSet_Icc
  have hnBound : (n : ℝ) ≤ 4 * ω ^ 2 := by
    have ha := (firstSaddle_coordinates_bounds hr' hr₁).1
    change r ≤ (saddleS r).re ^ 2 at ha
    have hpos := mul_le_mul_of_nonneg_left (show 1 ≤ 4 * (saddleS r).re ^ 2 by linarith)
      hn'.le
    rw [show ω ^ 2 = (n : ℝ) * (saddleS r).re ^ 2 from saddleOmega_sq r]
    linarith only [hpos]
  have hnorm (v : ℝ) (hv : v ∈ s) :
      ‖durfeeExponentialMean r u v‖ ≤ 2 * Real.exp (μ * ω) := by
    have hmin : 16 * u ≤ |v| := not_lt.mp (fun h => hv.2 (abs_le.mp h.le))
    have hmax : |v| ≤ Real.pi := abs_le.mpr hv.1
    have hcont : Continuous (fun θ => exp (pairedLog r θ (verticalPoint u v)) - 1) := by
      have hp : Continuous (fun θ : ℝ => (v, θ)) := continuous_const.prodMk continuous_id
      exact ((Complex.continuous_exp.comp (continuous_pairedLog_vertical r hrabs hu)).comp hp).sub
        continuous_const
    have hp (θ : ℝ) : ‖exp (pairedLog r θ (verticalPoint u v)) - 1‖ ≤ 2 * Real.exp (μ * ω) := by
      have h := norm_sub_le (exp (pairedLog r θ (verticalPoint u v))) (1 : ℂ)
      rw [norm_one, Complex.norm_exp] at h
      have hExp := Real.exp_le_exp.mpr (hlog v hmin hmax θ)
      have hOne := Real.one_le_exp_iff.mpr (mul_nonneg hμ hω.le)
      linarith only [h,hExp,hOne]
    refine (norm_angularAverage_le _).trans ?_
    have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith [Real.pi_pos])
      (hcont.norm.intervalIntegrable (-Real.pi) Real.pi)
      (continuous_const.intervalIntegrable (-Real.pi) Real.pi)
      (fun θ _ => hp θ)
    unfold angularMean
    calc
      _ ≤ (2 * Real.pi)⁻¹ * (∫ θ : ℝ in -Real.pi..Real.pi, 2 * Real.exp (μ * ω)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp; ring
  have hI : (∫ v in s, ‖durfeeExponentialMean r u v‖) ≤ 4 * Real.pi * Real.exp (μ * ω) := by
    let t := Icc (-Real.pi) Real.pi
    have hst : s ⊆ t := sdiff_subset
    have hF := (continuous_durfeeExponentialMean hrabs hu).norm
    have hC : IntegrableOn (fun _ : ℝ => 2 * Real.exp (μ * ω)) t := continuous_const.integrableOn_Icc
    calc
      _ ≤ ∫ v in s, 2 * Real.exp (μ * ω) :=
        setIntegral_mono_on (hF.integrableOn_Icc.mono_set hst) (hC.mono_set hst) hsi hnorm
      _ ≤ ∫ v in t, 2 * Real.exp (μ * ω) :=
        setIntegral_mono_set hC (Filter.Eventually.of_forall (fun _ => by positivity))
          (Filter.Eventually.of_forall hst)
      _ = _ := by simp [t, integral_const, Real.volume_Icc, Real.toNNReal_of_nonneg, sub_neg_eq_add,
        show 0 ≤ Real.pi + Real.pi by positivity, smul_eq_mul]; ring
  change Real.exp ω / (2 * Real.pi) * _ ≤ saddleAmplitude n r * firstSaddleMinorArcError ω μ
  have hEq : Real.exp (ω + μ * ω) = Real.exp (2 * ω) * Real.exp (-(1 - μ) * ω) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp ω / (2 * Real.pi) * (4 * Real.pi * Real.exp (μ * ω)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (2 * Real.exp (2 * ω) / (3 * Real.pi * (n : ℝ))) *
        (3 * Real.pi * n * Real.exp (-(1 - μ) * ω)) := by
      calc
        _ = 2 * Real.exp (ω + μ * ω) := by rw [Real.exp_add]; field_simp <;> ring
        _ = _ := by rw [hEq]; field_simp <;> ring
    _ ≤ saddleAmplitude n r * (3 * Real.pi * n * Real.exp (-(1 - μ) * ω)) :=
      mul_le_mul_of_nonneg_right (saddleAmplitude_lower hn hr' hr₁) (by positivity)
    _ ≤ _ := by
      unfold firstSaddleMinorArcError
      apply mul_le_mul_of_nonneg_left _ (saddleAmplitude_pos hn hr').le
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnBound (show 0 ≤ 3 * Real.pi by positivity))
        (Real.exp_nonneg (-(1 - μ) * ω))
      linarith only [h]

end DurfeeCCS.Step08
