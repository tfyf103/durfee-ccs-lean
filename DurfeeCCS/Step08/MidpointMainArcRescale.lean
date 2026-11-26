module

public import DurfeeCCS.Step08.MidpointMainArc
public import DurfeeCCS.Step08.AngularErrors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Symmetry and change of variables on the common contour arc in (40)–(41). -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06 MeasureTheory Set
open scoped ComplexConjugate

theorem pairedLog_add_pi_conj (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    pairedLog r (θ + Real.pi) (conj ζ) = conj (pairedLog r θ ζ) := by
  have hζ' : 0 < (conj ζ).re := by simpa using hζ
  rw [pairedLog_eq_tsum_mode r _ hr hζ', pairedLog_eq_tsum_mode r θ hr hζ,
    Complex.conj_tsum]
  apply tsum_congr
  intro n
  let k : ℕ := n + 1
  have hcos : Real.cos ((k : ℝ) * (θ + Real.pi)) =
      (-1) ^ k * Real.cos ((k : ℝ) * θ) := by
    rw [mul_add, Real.cos_add_nat_mul_pi]
  change pairedLogCoeff r (conj ζ) n * (Real.cos ((k : ℝ) * (θ + Real.pi)) : ℂ) =
    conj (pairedLogCoeff r ζ n * (Real.cos ((k : ℝ) * θ) : ℂ))
  have hpow : ((-1 : ℂ) ^ k) * ((-(r : ℂ) * I) ^ k) = (-(r : ℂ) * -I) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hcos, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  simp only [pairedLogCoeff, map_mul, map_div₀, map_neg, map_pow, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast, ← Complex.sinh_conj]
  change -2 * (-(r : ℂ) * I) ^ k /
    ((k : ℂ) * (2 * sinh ((k : ℂ) * conj ζ / 2))) *
    ((-1 : ℂ) ^ k * (Real.cos ((k : ℝ) * θ) : ℂ)) = _
  calc
    _ = -2 * (((-1 : ℂ) ^ k) * ((-(r : ℂ) * I) ^ k)) /
      ((k : ℂ) * (2 * sinh ((k : ℂ) * conj ζ / 2))) *
      (Real.cos ((k : ℝ) * θ) : ℂ) := by ring
    _ = _ := by rw [hpow]

theorem verticalPoint_neg (u v : ℝ) : verticalPoint u (-v) = conj (verticalPoint u v) := by
  simp [verticalPoint]

/-- Conjugating and shifting by a half-turn preserves the conjugacy of the full angular mean. -/
theorem angularAverage_neg_conj_of_add_pi {F : ℝ → ℝ → ℂ}
    (hc : ∀ v, Continuous (F v)) (hconj : ∀ v θ, F (-v) (θ + Real.pi) = conj (F v θ))
    (v : ℝ) : angularAverage (F (-v)) = conj (angularAverage (F v)) := by
  have hpos (v : ℝ) : (∫ θ in (0 : ℝ)..Real.pi, F (-v) θ) =
      conj (∫ θ in -Real.pi..(0 : ℝ), F v θ) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    have ht := intervalIntegral.integral_comp_add_right (a := -Real.pi) (b := (0 : ℝ))
      (F (-v)) Real.pi
    rw [neg_add_cancel, zero_add] at ht
    rw [← ht]
    exact intervalIntegral.integral_congr fun θ _ => hconj v θ
  have hneg : (∫ θ in -Real.pi..(0 : ℝ), F (-v) θ) =
      conj (∫ θ in (0 : ℝ)..Real.pi, F v θ) := by
    have h := congrArg (starRingEnd ℂ) (hpos (-v))
    simpa only [neg_neg, Complex.conj_conj] using h.symm
  unfold angularAverage
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hc (-v)).intervalIntegrable (-Real.pi) 0) ((hc (-v)).intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals
      ((hc v).intervalIntegrable (-Real.pi) 0) ((hc v).intervalIntegrable _ _),
    hpos, hneg, map_mul, map_inv₀, map_add, map_mul, Complex.conj_ofReal, map_ofNat, add_comm]

/-- The integrand under the angular average in the common-arc term of (40). -/
def firstSaddleCommonArcDifference (r u v θ : ℝ) : ℂ :=
  Complex.exp (pairedLog r θ (verticalPoint u v)) - Complex.exp (saddleG r θ / verticalPoint u v)

theorem continuous_firstSaddleCommonArcDifference {r : ℝ} (hr : |r| ≤ 1) {u : ℝ} (hu : 0 < u) :
    Continuous (fun p : ℝ × ℝ => firstSaddleCommonArcDifference r u p.1 p.2) := by
  have hζ : Continuous (fun p : ℝ × ℝ => verticalPoint u p.1) := by
    unfold verticalPoint
    fun_prop
  have hg := (continuous_saddleG hr).comp (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  unfold firstSaddleCommonArcDifference
  exact (Complex.continuous_exp.comp (continuous_pairedLog_vertical r hr hu)).sub
    (Complex.continuous_exp.comp (hg.div hζ (fun p => verticalPoint_ne_zero hu p.1)))

theorem even_norm_firstSaddleCommonArcDifference {r : ℝ} (hr : |r| ≤ 1) {u : ℝ} (hu : 0 < u) :
    Function.Even (fun v => ‖angularAverage (firstSaddleCommonArcDifference r u v)‖) := by
  intro v
  have hc (q : ℝ) : Continuous (firstSaddleCommonArcDifference r u q) := by
    have hh := (continuous_firstSaddleCommonArcDifference hr hu).comp
      (continuous_const.prodMk continuous_id : Continuous (fun θ : ℝ => (q, θ)))
    simpa only [Function.comp_def] using hh
  have hconj (q θ : ℝ) : firstSaddleCommonArcDifference r u (-q) (θ + Real.pi) =
      conj (firstSaddleCommonArcDifference r u q θ) := by
    unfold firstSaddleCommonArcDifference
    rw [verticalPoint_neg, pairedLog_add_pi_conj r θ hr (by simpa only [verticalPoint_re] using hu),
      saddleG_add_pi hr, ← map_div₀, Complex.exp_conj, Complex.exp_conj, map_sub]
  change ‖angularAverage (firstSaddleCommonArcDifference r u (-v))‖ =
    ‖angularAverage (firstSaddleCommonArcDifference r u v)‖
  rw [angularAverage_neg_conj_of_add_pi hc hconj v, Complex.norm_conj]

private theorem integral_symm_even {f : ℝ → ℝ} (hf : Continuous f) (he : Function.Even f) (a : ℝ) :
    (∫ x in -a..a, f x) = 2 * ∫ x in (0 : ℝ)..a, f x := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a) f
  have hh : (fun x => f (-x)) = f := funext he
  rw [hh, neg_zero] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-a) 0)
    (hf.intervalIntegrable _ _), ← h]
  ring

theorem re_saddleG_div_vertical_mul {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ η : ℝ) :
    (saddleG r θ / verticalPoint (saddleU n r) (saddleU n r * η)).re =
      saddleOmega n r * (1 - saddleGap r θ η) := by
  let u := saddleU n r
  let ω := saddleOmega n r
  have hu : 0 < u := saddleU_pos hn hr
  have hω : 0 < ω := saddleOmega_pos hn hr
  have hScale : u * ω = (saddleS r).re ^ 2 := saddleU_mul_omega hn r
  change (saddleG r θ / verticalPoint u (u * η)).re = ω * (1 - saddleGap r θ η)
  rw [Complex.div_re, Complex.normSq_apply, verticalPoint_re, verticalPoint_im,
    saddleGap, sub_sub_cancel, ← hScale]
  have hden : (0 : ℝ) < 1 + η ^ 2 := by positivity
  have hden' : 0 < u * u + u * η * (u * η) := by
    have h := mul_pos (sq_pos_of_pos hu) hden
    linarith only [h, show u * u + u * η * (u * η) = u ^ 2 * (1 + η ^ 2) by ring]
  field_simp [hu.ne', hω.ne', hden.ne', hden'.ne']

set_option maxHeartbeats 1200000 in
/-- Equation (41) bounds the common-arc contribution in (40). -/
theorem firstSaddleCommonArc_le {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    let u := saddleU n r
    Real.exp (saddleOmega n r) / (2 * Real.pi) *
      (∫ v in Icc (-(16 * u)) (16 * u),
        ‖angularAverage (firstSaddleCommonArcDifference r u v)‖) ≤
      saddleAmplitude n r * firstSaddleMainArcBudget n r := by
  let u := saddleU n r
  let ω := saddleOmega n r
  let F (v : ℝ) := ‖angularAverage (firstSaddleCommonArcDifference r u v)‖
  let K (η : ℝ) := ∫ θ in -Real.pi..Real.pi, firstSaddleMainArcKernel n r η θ
  have hu : 0 < u := saddleU_pos hn hr
  have hω : 0 < ω := saddleOmega_pos hn hr
  have hp := Real.pi_pos
  have hr' : |r| ≤ 1 := by simpa [abs_of_pos hr] using hr₁
  have hFc : Continuous F := by
    unfold F angularAverage
    exact (continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_firstSaddleCommonArcDifference hr' hu) _ _)).norm
  have hKc : Continuous K := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_firstSaddleMainArcKernel hn hr hr₁) _ _
  have hPoint (η : ℝ) : F (u * η) ≤ (2 * Real.pi)⁻¹ * Real.exp ω * K η := by
    refine (norm_angularAverage_le _).trans ?_
    unfold angularMean
    have hInt : (∫ θ in -Real.pi..Real.pi, ‖firstSaddleCommonArcDifference r u (u * η) θ‖) ≤
        ∫ θ in -Real.pi..Real.pi, Real.exp ω * firstSaddleMainArcKernel n r η θ := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ (fun θ _ => ?_)
      · have hh := (continuous_firstSaddleCommonArcDifference hr' hu).comp
          (continuous_const.prodMk continuous_id : Continuous (fun θ : ℝ => (u * η, θ)))
        simpa only [Function.comp_def] using hh.norm.intervalIntegrable (-Real.pi) Real.pi
      · have hh := (continuous_firstSaddleMainArcKernel hn hr hr₁).comp
          (continuous_const.prodMk continuous_id : Continuous (fun θ : ℝ => (η, θ)))
        simpa only [Function.comp_def] using (hh.const_mul (Real.exp ω)).intervalIntegrable (-Real.pi) Real.pi
      · unfold firstSaddleCommonArcDifference firstSaddleMainArcKernel
        refine (norm_exp_sub_exp_le_exp_norm _ _).trans_eq ?_
        rw [re_saddleG_div_vertical_mul hn hr, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
    rw [intervalIntegral.integral_const_mul] at hInt
    simpa only [K, mul_assoc] using mul_le_mul_of_nonneg_left hInt
      (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
  have hK : 0 ≤ ∫ η in (0 : ℝ)..16, K η := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro η _
    exact intervalIntegral.integral_nonneg (by linarith) (fun θ _ => firstSaddleMainArcKernel_nonneg n r η θ)
  have hRescale : (∫ v in Icc (-(16 * u)) (16 * u), F v) =
      (2 * u) * ∫ η in (0 : ℝ)..16, F (u * η) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (show -(16 * u) ≤ 16 * u by linarith),
      integral_symm_even hFc (even_norm_firstSaddleCommonArcDifference hr' hu)]
    rw [intervalIntegral.integral_comp_mul_left F hu.ne', mul_zero, smul_eq_mul, mul_comm u 16]
    field_simp [hu.ne']
  have hScaled : (∫ η in (0 : ℝ)..16, F (u * η)) ≤
      ((2 * Real.pi)⁻¹ * Real.exp ω) * ∫ η in (0 : ℝ)..16, K η := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by norm_num)
      ((hFc.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
      ((hKc.const_mul _).intervalIntegrable _ _) (fun η _ => hPoint η)
  have hA := saddleAmplitude_lower hn hr hr₁
  change Real.exp ω / (2 * Real.pi) *
    (∫ v in Icc (-(16 * u)) (16 * u), F v) ≤ saddleAmplitude n r * _
  rw [hRescale]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hScaled (by positivity))
    (by positivity)).trans ?_
  have hNu : (n : ℝ) * u = ω := saddleU_mul_n hn r
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  change _ ≤ saddleAmplitude n r * (3 * ω / (4 * Real.pi) * ∫ η in (0 : ℝ)..16, K η)
  calc
    _ = (2 * Real.exp (2 * ω) / (3 * Real.pi * n)) *
        (3 * ω / (4 * Real.pi) * ∫ η in (0 : ℝ)..16, K η) := by
      rw [show 2 * ω = ω + ω by ring, Real.exp_add, ← hNu]
      field_simp [hN.ne', hp.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (mul_nonneg (by positivity) hK)

end DurfeeCCS.Step08
