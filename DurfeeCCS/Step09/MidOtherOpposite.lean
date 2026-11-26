module

public import DurfeeCCS.Step09.MidOtherGaussian
public import DurfeeCCS.Step09.MidOtherPhase
public import DurfeeCCS.Step09.MidOtherDecay
public import DurfeeCCS.Step09.MidMajorContinuity
public import DurfeeCCS.Step09.MidMultiplierConj
public import DurfeeCCS.Step09.MidPhaseShape

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Absolute integrals of the two main modes on their opposite half-arcs. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08
open scoped ComplexConjugate

private theorem midPhase_neg_one_bounds {r : ℝ} (hr : 1 ≤ r) (χ : ℝ) :
    (midPhase r (-1) χ).re ≤ (saddleS r ^ 2).re - χ ^ 2 / (1 + r⁻¹ ^ 2) ∧
      |(midPhase r (-1) χ).im| ≤ (saddleS r ^ 2).im := by
  have hr0 : 0 < r := by linarith
  have h : r ^ 2 / (1 + r ^ 2) * χ ^ 2 = χ ^ 2 / (1 + r⁻¹ ^ 2) := by
    field_simp [hr0.ne']
    ring
  simpa only [midPhase_conj hr, Complex.conj_im, Complex.conj_re, abs_neg, ← h]
    using midPhase_zero_components hr χ

private theorem midPhase_neg_one_im_nonpos {r χ : ℝ} (hr : 1 ≤ r)
    (h : |χ| ≤ Real.pi / 2 ∨ 1 ≤ Real.log r) : (midPhase r (-1) χ).im ≤ 0 := by
  have hr0 : 0 < r := by linarith
  have ht : 0 < r⁻¹ := inv_pos.mpr hr0
  have ht1 := inv_le_one_of_one_le₀ hr
  rw [(midPhase_components r (-1) χ).2, midFrequency_neg_one, midModeRadius_neg_one]
  rcases h with h | h
  · have hcos := Real.cos_nonneg_of_mem_Icc (abs_le.mp h)
    have him := saddleG_im_nonneg_of_cos_nonneg ht ht1 hcos
    have hlog := Real.log_nonneg hr
    nlinarith only [him, mul_nonneg hlog Real.pi_pos.le]
  · have hIm := (abs_le.mp (saddleG_im_abs_le_origin ht ht1 χ)).1
    have hA := saddlePhaseSquare_im_le_twice ht
    rw [← saddleS_sq, ← saddleG_zero] at hA
    have hprod := mul_le_mul_of_nonneg_right h Real.pi_pos.le
    nlinarith only [hA, hIm, hprod, ht1, Real.pi_gt_d2]

private theorem midRe_exponent_neg_one_sector {n : ℕ} (hn : 0 < n) {r η χ : ℝ}
    (hr : 1 ≤ r) (hη : η ∈ Icc 0 8) (h : |χ| ≤ Real.pi / 2 ∨ 1 ≤ Real.log r) :
    ((n : ℂ) * midEtaPoint n r η + midPhase r (-1) χ / midEtaPoint n r η).re ≤
      2 * midOmega n r - Real.sqrt n * (saddleS r).im ^ 2 / (saddleS r).re -
        Real.sqrt n * χ ^ 2 / (130 * (saddleS r).re) := by
  exact midRe_exponent_opposite_sign hn hr (by simpa [abs_of_nonneg hη.1] using hη.2)
    (midPhase_neg_one_bounds hr χ).1
    (mul_nonpos_of_nonneg_of_nonpos hη.1 (midPhase_neg_one_im_nonpos hr h))

private theorem norm_midIntegrand_neg_one_reflect {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 1 ≤ r) (η χ : ℝ) :
    ‖midIntegrand n r 0 (-η) χ‖ = ‖midIntegrand n r (-1) η χ‖ := by
  have hr' : 0 < r := by linarith
  have hζ : 0 < (midEtaPoint n r (-η)).re := by
    rw [midEtaPoint_re]
    exact saddleU_pos hn hr'
  have hb := midMultiplier_neg_one_conj hr hζ χ
  rw [midEtaPoint_neg_conj, Complex.conj_conj] at hb
  have hz : midEtaPoint n r (-η) = conj (midEtaPoint n r η) := midEtaPoint_neg_conj n r η
  have hF : midIntegrand n r (-1) η χ = conj (midIntegrand n r 0 (-η) χ) := by
    dsimp only [midIntegrand]
    rw [hb, midPhase_conj hr, hz]
    simp only [map_mul, ← Complex.exp_conj, map_add, map_div₀, Complex.conj_natCast,
      Complex.conj_conj]
  rw [hF, norm_conj]

private theorem integral_midOpposite_reflection {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 1 ≤ r) :
    (∫ η in (-8 : ℝ)..0, ∫ χ : ℝ, ‖midIntegrand n r 0 η χ‖) =
    (∫ η in (0 : ℝ)..8, ∫ χ : ℝ, ‖midIntegrand n r (-1) η χ‖) := by
  rw [show (0 : ℝ) = -(0 : ℝ) by simp,
    ← intervalIntegral.integral_comp_neg (f := fun η => ∫ χ : ℝ, ‖midIntegrand n r 0 η χ‖)]
  simp only [neg_zero]
  simp_rw [norm_midIntegrand_neg_one_reflect hn hr]

private theorem integral_prod_sector_split {f : ℝ → ℝ → ℂ} {S : Set ℝ}
    (hS : MeasurableSet S)
    (hcore : IntegrableOn (Function.uncurry f) (Icc 0 8 ×ˢ S) (volume.prod volume))
    (hout : IntegrableOn (Function.uncurry f) (Icc 0 8 ×ˢ Sᶜ) (volume.prod volume)) :
    (∫ η in (0 : ℝ)..8, ∫ y : ℝ, ‖f η y‖) =
      (∫ η in (0 : ℝ)..8, ∫ y in S, ‖f η y‖) +
      (∫ η in (0 : ℝ)..8, ∫ y in Sᶜ, ‖f η y‖) := by
  let A : Set ℝ := Icc 0 8
  have h0 : (0 : ℝ) ≤ 8 := by norm_num
  have hU : A ×ˢ (univ : Set ℝ) = (A ×ˢ S) ∪ (A ×ˢ Sᶜ) := by
    rw [← prod_union, union_compl_self]
  have hd : Disjoint (A ×ˢ S) (A ×ˢ Sᶜ) := by
    refine Set.disjoint_left.mpr ?_
    exact fun _ hx hy => hy.2 hx.2
  let F (z : ℝ × ℝ) := ‖f z.1 z.2‖
  have hInt : IntegrableOn F (A ×ˢ (univ : Set ℝ)) (volume.prod volume) := by
    rw [hU]
    exact IntegrableOn.union hcore.norm hout.norm
  simp_rw [intervalIntegral.integral_of_le h0, ← integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ z in A ×ˢ (univ : Set ℝ), F z ∂volume.prod volume := by
      simpa only [setIntegral_univ] using (setIntegral_prod _ hInt).symm
    _ = (∫ z in A ×ˢ S, F z ∂volume.prod volume) +
          (∫ z in A ×ˢ Sᶜ, F z ∂volume.prod volume) := by
      rw [hU]
      exact setIntegral_union hd (measurableSet_Icc.prod hS.compl) hcore.norm hout.norm
    _ = _ := by
      have hS₁ : IntegrableOn F (A ×ˢ S) (volume.prod volume) := hcore.norm
      have hS₂ : IntegrableOn F (A ×ˢ Sᶜ) (volume.prod volume) := hout.norm
      exact congrArg₂ (· + ·) (setIntegral_prod F hS₁) (setIntegral_prod F hS₂)

private theorem opposite_a_le_half {r : ℝ} (hr : 0 < r) (hlog : Real.log r ≤ 0.5) :
    (saddleS r).re ≤ 1.377 := by
  have ha : (saddleS (Real.exp 0.5)).re ≤ 1.37623 := by
    simpa [saddleEndpointData, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (10 : Fin 21)).re_upper
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hr] at h
  exact ((monotoneOn_saddleS_re hr (Real.exp_pos _) h).trans ha).trans (by norm_num)

private theorem opposite_a_le_one {r : ℝ} (hr : 0 < r) (hlog : Real.log r ≤ 1) :
    (saddleS r).re ≤ 1.733 := by
  have ha : (saddleS (Real.exp 1)).re ≤ 1.73266 := by
    simpa [saddleEndpointData, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (13 : Fin 21)).re_upper
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hr] at h
  exact ((monotoneOn_saddleS_re hr (Real.exp_pos _) h).trans ha).trans (by norm_num)

private theorem opposite_b_sq_ge {r : ℝ} (hr : 1 ≤ r) : 0.733 ≤ (saddleS r).im ^ 2 := by
  have hb := saddle_at_one_lower.2.trans (monotoneOn_saddleS_im (by simp) hr hr)
  have h := pow_le_pow_left₀ (show 0 ≤ (0.85623 : ℝ) by norm_num) hb 2
  linarith only [h]

private theorem opposite_b_sq_ge_large {r : ℝ} (hr : 1 ≤ r) (hlog : 1 ≤ Real.log r) :
    1.245 ≤ (saddleS r).im ^ 2 := by
  have hb : (1.11585 : ℝ) ≤ (saddleS (Real.exp 1)).im := by
    simpa [saddleEndpointData, Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (13 : Fin 21)).im_lower
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (show 0 < r by linarith)] at h
  have hb' := hb.trans (monotoneOn_saddleS_im (Real.one_le_exp_iff.mpr (by norm_num)) hr h)
  have hk := pow_le_pow_left₀ (show 0 ≤ (1.11585 : ℝ) by norm_num) hb' 2
  linarith only [hk]

/-- The two opposite half-arc absolute integrals normalized by the saddle amplitude. -/
theorem midOther_oppositeBudget_at_saddle {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) :
    (midU n r / (4 * Real.pi ^ 2 * saddleAmplitude n r)) *
      ((∫ η in (-8 : ℝ)..0, ∫ χ : ℝ, ‖midIntegrand n r 0 η χ‖) +
       (∫ η in (0 : ℝ)..8, ∫ χ : ℝ, ‖midIntegrand n r (-1) η χ‖)) <
      if Real.log r < 1 then 0.000011 else 0.00006 := by
  let x := Real.sqrt (n : ℝ)
  let a := (saddleS r).re
  let P := midU n r / (4 * Real.pi ^ 2 * saddleAmplitude n r)
  let f := midIntegrand n r (-1)
  let S : Set ℝ := {y | |y| ≤ Real.pi / 2}
  have hn' : 0 < n := by omega
  have hr' : 0 < r := by linarith
  have hx : 80 ≤ x := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hxp : 0 < x := by linarith
  have h := midSaddle_data hn hr hmax
  have ha : 0 < a := by linarith [h.1]
  have hP : 0 ≤ P := by
    unfold P
    exact div_nonneg (saddleU_pos hn' hr').le
      (by positivity [saddleAmplitude_pos hn' hr'])
  have hS : MeasurableSet S := measurableSet_le continuous_abs.measurable measurable_const
  have hf : Measurable (Function.uncurry f) := (continuous_midIntegrand hn' hr (-1)).measurable
  have hηmag (η : ℝ) (hη : η ∈ Icc (0 : ℝ) 8) : |η| ≤ 8 := by
    rw [abs_of_nonneg hη.1]
    exact hη.2
  have hB (η : ℝ) (hη : η ∈ Icc (0 : ℝ) 8) (χ : ℝ) :
      ‖midMultiplier r (-1) (midEtaPoint n r η) χ‖ ≤ 2100 :=
    (norm_midMultiplier_lt_2100 hn hr hmax (hηmag η hη) (-1) χ).le
  rw [integral_midOpposite_reflection hn' hr]
  by_cases hlarge : 1 ≤ Real.log r
  · rw [ite_eq_right (not_lt.mpr hlarge)]
    have hPhi (η : ℝ) (hη : η ∈ Icc (0 : ℝ) 8) (χ : ℝ) (_ : χ ∈ univ) :=
      midRe_exponent_neg_one_sector hn' hr hη (χ := χ) (Or.inr hlarge)
    have hδ : 1.245 * x / a ≤ x * (saddleS r).im ^ 2 / a := by
      rw [mul_comm (1.245 : ℝ)]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (opposite_b_sq_ge_large hr hlarge) hxp.le) ha.le
    have hb := midOtherGaussian_unshifted (p := -1) (C := 110)
      (δ := 1.245*x/a) (l := 0) (h := 8) hn' hr' (by norm_num) MeasurableSet.univ hf
      (by norm_num) midOtherGaussian_constant_small
      (fun η hη χ _ => (norm_midMultiplier_lt_two hn hr hmax hlarge (hηmag η hη) (-1) χ).le)
      (fun η hη χ hχ => (hPhi η hη χ hχ).trans (by linarith only [hδ]))
    have hrate := midOther_large_opposite_budget_lt hx ha h.2.1
    simp only [setIntegral_univ] at hb
    change P * ((∫ η in (0 : ℝ)..8, ∫ χ : ℝ, ‖f η χ‖) +
       (∫ η in (0 : ℝ)..8, ∫ χ : ℝ, ‖f η χ‖)) < _
    have hbound := hb.2
    change P * (∫ η in (0 : ℝ)..8, ∫ χ : ℝ, ‖f η χ‖) ≤
      ((8 - 0 : ℝ) / 16) * Real.sqrt (a*x) * Real.exp (-(1.245*x/a)) * 110 at hbound
    linarith only [hbound, hrate]
  · have hsmall : Real.log r < 1 := lt_of_not_ge hlarge
    rw [ite_eq_left hsmall]
    have ha' := opposite_a_le_one hr' hsmall.le
    have hδ : (0.733 / 1.733) * x ≤ x * (saddleS r).im ^ 2 / a := by
      have hq : (0.733 : ℝ) / 1.733 ≤ (saddleS r).im ^ 2 / a :=
        (div_le_div_of_nonneg_right (opposite_b_sq_ge hr) (by norm_num : (0 : ℝ) ≤ 1.733)).trans
          (div_le_div_of_nonneg_left (sq_nonneg _) ha ha')
      linarith only [mul_le_mul_of_nonneg_right hq hxp.le,
        show x * (saddleS r).im ^ 2 / a = ((saddleS r).im ^ 2 / a) * x by ring]
    have hc := midOtherGaussian_unshifted (p := -1) (C := 109000)
      (δ := (0.733 / 1.733) * x) (l := 0) (h := 8) hn' hr' (by norm_num) hS hf
      (by norm_num) midOtherGaussian_constant_large (fun η hη χ _ => hB η hη χ)
      (fun η hη χ hχ => (midRe_exponent_neg_one_sector hn' hr hη (Or.inl hχ)).trans
        (by linarith only [hδ]))
    have hK := midOther_small_opposite_core_budget_lt hx ha.le ha'
    let c : ℝ := if Real.log r ≤ 0.5 then 0.32 else 0.44
    have hgap (η : ℝ) : c ≤ oppositeHalfLogPhaseLoss (Real.log r) (η - midSlope r) := by
      unfold c
      split_ifs with h
      · exact (oppositeHalf_first_log_interval (Real.log_nonneg hr) h).le
      · exact (oppositeHalf_second_log_interval (le_of_lt (lt_of_not_ge h)) hsmall.le).le
    have ht := midOtherGaussian_shifted (p := -1) (C := 109000) (c := Real.pi / 2)
      (δ := c*x) (l := 0) (h := 8) hn' hr' (by norm_num) (by positivity) hf
      (by norm_num) midOtherGaussian_constant_large
      (fun η hη χ _ => hB η hη χ) (fun η hη χ hχ => by
        have hh := midPhase_neg_one_bounds hr χ
        have hp := midRe_exponent_opposite_shifted hn' hr hη.1 (hηmag η hη) hχ hh.1
          ((le_abs_self _).trans hh.2)
        exact hp.trans (by linarith only [mul_le_mul_of_nonneg_right (hgap η) hxp.le]))
    have hrate : 109000 * (Real.sqrt (a * x) * Real.exp (-(c*x))) < 0.00001 := by
      unfold c
      split_ifs with h
      · simpa only [neg_mul] using
          midOther_small_opposite_first_budget_lt hx ha.le (opposite_a_le_half hr' h)
      · simpa only [neg_mul] using
          (midOther_small_opposite_second_budget_lt hx ha.le ha').trans
            (by norm_num : (0.000001 : ℝ) < 0.00001)
    have hTail : {y : ℝ | Real.pi / 2 < |y|} = Sᶜ := by
      ext y
      simp [S]
    rw [hTail] at ht
    have hsplit := integral_prod_sector_split (f := f) hS hc.1 ht.1
    change P * ((∫ η in (0 : ℝ)..8, ∫ χ : ℝ, ‖f η χ‖) +
      (∫ η in (0 : ℝ)..8, ∫ χ : ℝ, ‖f η χ‖)) < _
    have hCore := hc.2
    change P * (∫ η in (0 : ℝ)..8, ∫ χ in S, ‖f η χ‖) ≤
      ((8 - 0 : ℝ) / 16) * Real.sqrt (a*x) * Real.exp (-(0.733 / 1.733 * x)) * 109000 at hCore
    have hOut := ht.2
    change P * (∫ η in (0 : ℝ)..8, ∫ χ in Sᶜ, ‖f η χ‖) ≤
      ((8 - 0 : ℝ) / 16) * Real.sqrt (a*x) * Real.exp (-(c*x)) * 109000 at hOut
    rw [hsplit]
    simp only [neg_mul] at hK
    linarith only [hCore, hOut, hK, hrate]

end DurfeeCCS.Step09
