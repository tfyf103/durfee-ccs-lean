module

public import DurfeeCCS.Step09.MidPhase
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The Gaussian mass and the normalization used in (65). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step08

theorem integral_shifted_gaussian_tail {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    IntegrableOn (fun y : ℝ => Real.exp (-b * (|y| - c) ^ 2)) {y : ℝ | c < |y|} ∧
      (∫ y in {y : ℝ | c < |y|}, Real.exp (-b * (|y| - c) ^ 2)) = Real.sqrt (Real.pi / b) := by
  let f (y : ℝ) := Real.exp (-b * (|y| - c) ^ 2)
  let g (y : ℝ) := Real.exp (-b * y ^ 2)
  have he : MeasurableEmbedding (fun y : ℝ => y + -c) :=
    (Homeomorph.addRight (-c)).measurableEmbedding
  have hpre : (fun y : ℝ => y + -c) ⁻¹' Ioi 0 = Ioi c := by ext y; simp
  have hg : IntegrableOn g (Ioi 0) := (integrable_exp_neg_mul_sq hb).integrableOn
  have hg' : IntegrableOn (fun y : ℝ => g (y + -c)) (Ioi c) := by
    have h := ((measurePreserving_add_right (volume : Measure ℝ) (-c)).integrableOn_comp_preimage he).mpr hg
    rwa [hpre] at h
  have heq (y : ℝ) (hy : y ∈ Ioi c) : f y = g (y + -c) := by
    have hy' : 0 ≤ y := hc.trans (le_of_lt hy)
    simp [f, g, abs_of_nonneg hy', sub_eq_add_neg]
  have hf : IntegrableOn f (Ioi c) :=
    hg'.congr (Set.EqOn.eventuallyEq_of_mem (fun y hy => (heq y hy).symm)
      (ae_restrict_mem measurableSet_Ioi))
  have hI : (∫ y in Ioi c, f y) = ∫ y in Ioi 0, g y := by
    calc
      _ = ∫ y in Ioi c, g (y + -c) := setIntegral_congr_fun measurableSet_Ioi heq
      _ = _ := by
        have h := (measurePreserving_add_right (volume : Measure ℝ) (-c)).setIntegral_preimage_emb he g (Ioi 0)
        rwa [hpre] at h
  have hneg : IntegrableOn f (Iio (-c)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun y : ℝ => -y) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simpa only [Function.comp_def, f, abs_neg, neg_preimage, neg_Iio, neg_neg] using hf
  have hIn : (∫ y in Iio (-c), f y) = ∫ y in Ioi c, f y := by
    rw [← integral_Iic_eq_integral_Iio]
    simpa only [f, abs_neg, neg_neg] using integral_comp_neg_Iic (-c) f
  have hS : {y : ℝ | c < |y|} = Iio (-c) ∪ Ioi c := by
    ext y
    change c < |y| ↔ y < -c ∨ c < y
    rw [← not_le, abs_le, not_and_or, not_le, not_le]
  have hd : Disjoint (Iio (-c)) (Ioi c) := by
    apply Set.disjoint_left.mpr
    intro y hy hy'
    simp only [mem_Iio, mem_Ioi] at hy hy'
    linarith only [hc, hy, hy']
  change IntegrableOn f _ ∧ (∫ y in _, f y) = _
  rw [hS, setIntegral_union hd measurableSet_Ioi hneg hf, hIn, hI]
  refine ⟨hneg.union hf, ?_⟩
  change (∫ x in Ioi 0, Real.exp (-b * x ^ 2)) + ∫ x in Ioi 0, Real.exp (-b * x ^ 2) = _
  rw [integral_gaussian_Ioi]
  ring

theorem saddleAmplitude_gt_mid {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    (saddleS r).re * Real.exp (2 * midOmega n r) / (2 * Real.pi * (n : ℝ)) <
      saddleAmplitude n r := by
  obtain ⟨hb, hab⟩ := saddleS_components hr
  have ha := hb.trans hab
  have hs : (saddleS r).re ≤ ‖saddleS r‖ := Complex.re_le_norm _
  have hg : Real.sqrt r < (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
    have hh := Real.rpow_lt_rpow (sq_nonneg r) (show r ^ 2 < 1 + r ^ 2 by linarith)
      (show (0 : ℝ) < 1 / 4 by norm_num)
    have he : (r ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt r := by
      rw [← Real.rpow_natCast_mul hr.le 2 (1 / 4), Real.sqrt_eq_rpow]
      norm_num
    rw [he] at hh
    exact hh
  have hpos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  unfold saddleAmplitude midOmega Step08.saddleOmega
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (lt_div_iff₀ (by positivity)).mpr
  calc
    _ = (saddleS r).re * Real.sqrt r * Real.exp (2 * (saddleS r).re * Real.sqrt n) := by
      field_simp
    _ < _ := mul_lt_mul_of_pos_right
      ((mul_lt_mul_of_pos_left hg ha).trans_le
        (mul_le_mul_of_nonneg_right hs (by positivity))) (Real.exp_pos _)

private theorem midOtherGauss_prod {F : ℝ → ℝ → ℂ} {G : ℝ → ℝ} {l h c : ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hf : Measurable (Function.uncurry F)) (hG : IntegrableOn G S)
    (hpoint : ∀ η ∈ Icc l h, ∀ y ∈ S, ‖F η y‖ ≤ c * G y) :
    IntegrableOn (Function.uncurry F) (Icc l h ×ˢ S) (volume.prod volume) := by
  let μ : Measure ℝ := volume.restrict (Icc l h)
  let ν : Measure ℝ := volume.restrict S
  rw [IntegrableOn, ← Measure.prod_restrict]
  change Integrable (Function.uncurry F) (μ.prod ν)
  have hMeas := hf.aestronglyMeasurable (μ := μ.prod ν)
  refine (integrable_prod_iff hMeas).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with η hη
    exact (hG.const_mul c).mono' (hf.comp measurable_prodMk_left).aestronglyMeasurable <| by
      filter_upwards [ae_restrict_mem hS] with y hy
      exact hpoint η hη y hy
  · have hM : AEStronglyMeasurable (fun η => ∫ y, ‖F η y‖ ∂ν) μ :=
      hf.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    refine (integrable_const (c * ∫ y, G y ∂ν)).mono' hM ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with η hη
    have hNonneg : 0 ≤ ∫ y, ‖F η y‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
    change ‖∫ y, ‖F η y‖ ∂ν‖ ≤ _
    rw [Real.norm_of_nonneg hNonneg, ← integral_const_mul]
    exact integral_mono_of_nonneg (.of_forall (fun _ => norm_nonneg _)) (hG.const_mul c) <| by
      filter_upwards [ae_restrict_mem hS] with y hy
      exact hpoint η hη y hy

/-- The general Gaussian comparison of (65), including absolute integrability
of the two-variable frequency integrand on the rectangle. -/
theorem midOtherGaussian_bound {F : ℝ → ℝ → ℂ} {G : ℝ → ℝ} {l h a x M δ K C : ℝ} {S : Set ℝ}
    (hlh : l ≤ h) (ha : 0 < a) (hx : 0 < x) (hM : 0 < M)
    (hMlow : a * Real.exp (2 * a * x) / (2 * Real.pi * x ^ 2) ≤ M)
    (hK : 0 ≤ K) (hC : K * 16 * Real.sqrt (130 * Real.pi) / (2 * Real.pi) ≤ C)
    (hS : MeasurableSet S) (hf : Measurable (Function.uncurry F)) (hG : IntegrableOn G S)
    (hGint : (∫ y in S, G y) ≤ Real.sqrt (130 * Real.pi * a / x))
    (hpoint : ∀ η ∈ Icc l h, ∀ y ∈ S, ‖F η y‖ ≤ K * Real.exp (2 * a * x - δ) * G y) :
    IntegrableOn (Function.uncurry F) (Icc l h ×ˢ S) (volume.prod volume) ∧
      a / (4 * Real.pi ^ 2 * x * M) * (∫ η in l..h, ∫ y in S, ‖F η y‖) ≤
        ((h - l) / 16) * Real.sqrt (a * x) * Real.exp (-δ) * C := by
  let c := K * Real.exp (2 * a * x - δ)
  have hc : 0 ≤ c := by unfold c; positivity
  have hprod := midOtherGauss_prod hS hf hG hpoint
  have hGexp : 0 ≤ Real.sqrt (130 * Real.pi * a / x) := Real.sqrt_nonneg _
  have hCpos : 0 ≤ C := (by positivity : 0 ≤ K * 16 * Real.sqrt (130 * Real.pi) / (2 * Real.pi)).trans hC
  have houter : (∫ η in l..h, ∫ y in S, ‖F η y‖) ≤ (h - l) * c * Real.sqrt (130 * Real.pi * a / x) := by
    rw [intervalIntegral.integral_of_le hlh, ← integral_Icc_eq_integral_Ioc]
    calc
      _ ≤ ∫ _η in Icc l h, c * Real.sqrt (130 * Real.pi * a / x) := by
        apply integral_mono_of_nonneg (.of_forall (fun _ => integral_nonneg fun _ => norm_nonneg _))
          (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with η hη
        calc
          _ ≤ ∫ y in S, c * G y := by
            apply integral_mono_of_nonneg (.of_forall (fun _ => norm_nonneg _)) (hG.const_mul c)
            filter_upwards [ae_restrict_mem hS] with y hy
            exact hpoint η hη y hy
          _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hGint hc
      _ = _ := by rw [setIntegral_const, Real.volume_real_Icc_of_le hlh, smul_eq_mul]; ring
  refine ⟨hprod, (mul_le_mul_of_nonneg_left houter (by positivity)).trans ?_⟩
  have he : 0 < Real.exp (2 * a * x) := Real.exp_pos _
  have hδ : 0 ≤ Real.exp (-δ) := Real.exp_nonneg _
  have hcoef : a / (4 * Real.pi ^ 2 * x * M) ≤ x / (2 * Real.pi * Real.exp (2 * a * x)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hp := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * x ^ 2)).mp hMlow
    nlinarith only [mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * Real.pi by positivity)]
  have hsqrt : x * Real.sqrt (130 * Real.pi * a / x) =
      Real.sqrt (a * x) * Real.sqrt (130 * Real.pi) := by
    calc
      _ = Real.sqrt (x ^ 2 * (130 * Real.pi * a / x)) := by
        rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le]
      _ = _ := by
        rw [← Real.sqrt_mul (show 0 ≤ a * x by positivity)]
        congr 1
        field_simp
  calc
    _ ≤ x / (2 * Real.pi * Real.exp (2 * a * x)) *
        ((h - l) * c * Real.sqrt (130 * Real.pi * a / x)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = ((h - l) / 16) * Real.sqrt (a * x) * Real.exp (-δ) *
        (K * 16 * Real.sqrt (130 * Real.pi) / (2 * Real.pi)) := by
      have hE : Real.exp (2 * a * x - δ) = Real.exp (2 * a * x) * Real.exp (-δ) := by
        rw [sub_eq_add_neg, Real.exp_add]
      unfold c
      rw [hE]
      calc
        _ = (h - l) * K * Real.exp (-δ) / (2 * Real.pi) *
            (x * Real.sqrt (130 * Real.pi * a / x)) := by field_simp
        _ = _ := by rw [hsqrt]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hC (by positivity)

theorem midOtherGaussian_constant_large :
    (2100 : ℝ) * 16 * Real.sqrt (130 * Real.pi) / (2 * Real.pi) ≤ 109000 := by
  have hs : Real.sqrt (130 * Real.pi) ≤ 20.22 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith only [Real.pi_lt_d6]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [hs, Real.pi_gt_d6]

theorem midOtherGaussian_constant_small :
    (2 : ℝ) * 16 * Real.sqrt (130 * Real.pi) / (2 * Real.pi) ≤ 110 := by
  have hs : Real.sqrt (130 * Real.pi) ≤ 20.22 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith only [Real.pi_lt_d6]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [hs, Real.pi_gt_d6]

private theorem midOther_gaussian_mass {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Real.sqrt (Real.pi / (x / (130 * a))) = Real.sqrt (130 * Real.pi * a / x) := by
  congr 1
  field_simp

/-- Equation (65) for an arbitrary measurable angular subset and unshifted Gaussian. -/
theorem midOtherGaussian_unshifted {n : ℕ} (hn : 0 < n) {r l h δ K C : ℝ} {p : ℤ} {S : Set ℝ}
    (hr : 0 < r) (hlh : l ≤ h) (hS : MeasurableSet S)
    (hf : Measurable (Function.uncurry (midIntegrand n r p)))
    (hK : 0 ≤ K) (hC : K * 16 * Real.sqrt (130 * Real.pi) / (2 * Real.pi) ≤ C)
    (hMult : ∀ η ∈ Icc l h, ∀ y ∈ S, ‖midMultiplier r p (midEtaPoint n r η) y‖ ≤ K)
    (hPhase : ∀ η ∈ Icc l h, ∀ y ∈ S,
      ((n : ℂ) * midEtaPoint n r η + midPhase r p y / midEtaPoint n r η).re ≤
        2 * midOmega n r - δ - Real.sqrt n * y ^ 2 / (130 * (saddleS r).re)) :
    IntegrableOn (Function.uncurry (midIntegrand n r p))
      (Icc l h ×ˢ S) (volume.prod volume) ∧
    (midU n r / (4 * Real.pi ^ 2 * saddleAmplitude n r)) *
        (∫ η in l..h, ∫ y in S, ‖midIntegrand n r p η y‖) ≤
      ((h - l) / 16) * Real.sqrt (midOmega n r) * Real.exp (-δ) * C := by
  let a := (saddleS r).re
  let x := Real.sqrt (n : ℝ)
  let b := x / (130 * a)
  let G := fun y : ℝ => Real.exp (-b * y ^ 2)
  have hω : midOmega n r = a * x := by rfl
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  have hx : 0 < x := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hb : 0 < b := by unfold b; positivity
  have hM := saddleAmplitude_pos hn hr
  have hL : a * Real.exp (2 * a * x) / (2 * Real.pi * x ^ 2) ≤ saddleAmplitude n r := by
    unfold x
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    have hh := (saddleAmplitude_gt_mid hn hr).le
    rw [hω, ← mul_assoc] at hh
    exact hh
  have hG : Integrable G := integrable_exp_neg_mul_sq hb
  have hGi : (∫ y in S, G y) ≤ Real.sqrt (130 * Real.pi * a / x) := by
    have heq : (∫ y, G y) = Real.sqrt (130 * Real.pi * a / x) := by
      unfold G
      rw [integral_gaussian b]
      exact midOther_gaussian_mass ha hx
    rw [← heq]
    exact setIntegral_le_integral hG (.of_forall (fun _ => Real.exp_nonneg _))
  have hp (η : ℝ) (hη : η ∈ Icc l h) (y : ℝ) (hy : y ∈ S) :
    ‖midIntegrand n r p η y‖ ≤ K * Real.exp (2 * a * x - δ) * G y := by
    unfold midIntegrand
    rw [norm_mul, Complex.norm_exp]
    have hphase := Real.exp_le_exp.mpr (hPhase η hη y hy)
    have hp' : Real.exp (2 * a * x - δ - Real.sqrt n * y ^ 2 / (130 * a)) =
        Real.exp (2 * a * x - δ) * G y := by
      unfold G b x
      rw [← Real.exp_add]
      congr 1
      ring
    exact (mul_le_mul hphase (hMult η hη y hy) (norm_nonneg _) (Real.exp_nonneg _)).trans_eq
      (by rw [hω, ← mul_assoc, hp']; ring)
  have H := midOtherGaussian_bound hlh ha hx hM hL hK hC hS hf hG.integrableOn hGi hp
  refine ⟨H.1, ?_⟩
  rw [hω]
  have hEq : midU n r / (4 * Real.pi ^ 2 * saddleAmplitude n r) =
      a / (4 * Real.pi ^ 2 * x * saddleAmplitude n r) := by
    change (a / x) / _ = _
    field_simp
  exact hEq.symm ▸ H.2

/-- The shifted Gaussian version of (65) for the outside angular sector. -/
theorem midOtherGaussian_shifted {n : ℕ} (hn : 0 < n) {r l h δ K C c : ℝ} {p : ℤ}
    (hr : 0 < r) (hlh : l ≤ h) (hc : 0 ≤ c)
    (hf : Measurable (Function.uncurry (midIntegrand n r p)))
    (hK : 0 ≤ K) (hC : K * 16 * Real.sqrt (130 * Real.pi) / (2 * Real.pi) ≤ C)
    (hMult : ∀ η ∈ Icc l h, ∀ y : ℝ, c < |y| → ‖midMultiplier r p (midEtaPoint n r η) y‖ ≤ K)
    (hPhase : ∀ η ∈ Icc l h, ∀ y : ℝ, c < |y| →
      ((n : ℂ) * midEtaPoint n r η + midPhase r p y / midEtaPoint n r η).re ≤
        2 * midOmega n r - δ - Real.sqrt n * (|y| - c) ^ 2 / (130 * (saddleS r).re)) :
    IntegrableOn (Function.uncurry (midIntegrand n r p))
      (Icc l h ×ˢ {y : ℝ | c < |y|}) (volume.prod volume) ∧
    (midU n r / (4 * Real.pi ^ 2 * saddleAmplitude n r)) *
        (∫ η in l..h, ∫ y in {y : ℝ | c < |y|}, ‖midIntegrand n r p η y‖) ≤
      ((h - l) / 16) * Real.sqrt (midOmega n r) * Real.exp (-δ) * C := by
  let a := (saddleS r).re
  let x := Real.sqrt (n : ℝ)
  let b := x / (130 * a)
  let G := fun y : ℝ => Real.exp (-b * (|y| - c) ^ 2)
  let S : Set ℝ := {y : ℝ | c < |y|}
  have hω : midOmega n r = a * x := by rfl
  have ha : 0 < a := (saddleS_components hr).1.trans (saddleS_components hr).2
  have hx : 0 < x := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hb : 0 < b := by unfold b; positivity
  have hM := saddleAmplitude_pos hn hr
  have hL : a * Real.exp (2 * a * x) / (2 * Real.pi * x ^ 2) ≤ saddleAmplitude n r := by
    unfold x
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    have hh := (saddleAmplitude_gt_mid hn hr).le
    rw [hω, ← mul_assoc] at hh
    exact hh
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_abs.measurable
  have ⟨hG,hI⟩ := integral_shifted_gaussian_tail hb hc
  have hGi : (∫ y in S, G y) ≤ Real.sqrt (130 * Real.pi * a / x) := by
    change (∫ y in {y : ℝ | c < |y|}, Real.exp (-b * (|y| - c) ^ 2)) ≤ _
    rw [hI, midOther_gaussian_mass ha hx]
  have hp (η : ℝ) (hη : η ∈ Icc l h) (y : ℝ) (hy : y ∈ S) :
    ‖midIntegrand n r p η y‖ ≤ K * Real.exp (2 * a * x - δ) * G y := by
    unfold midIntegrand
    rw [norm_mul, Complex.norm_exp]
    have hphase := Real.exp_le_exp.mpr (hPhase η hη y hy)
    have hp' : Real.exp (2 * a * x - δ - Real.sqrt n * (|y| - c) ^ 2 / (130 * a)) =
        Real.exp (2 * a * x - δ) * G y := by
      unfold G b x
      rw [← Real.exp_add]
      congr 1
      ring
    exact (mul_le_mul hphase (hMult η hη y hy) (norm_nonneg _) (Real.exp_nonneg _)).trans_eq
      (by rw [hω, ← mul_assoc, hp']; ring)
  have H := midOtherGaussian_bound hlh ha hx hM hL hK hC hS hf hG hGi hp
  refine ⟨H.1, ?_⟩
  rw [hω]
  have hEq : midU n r / (4 * Real.pi ^ 2 * saddleAmplitude n r) =
      a / (4 * Real.pi ^ 2 * x * saddleAmplitude n r) := by
    change (a / x) / _ = _
    field_simp
  exact hEq.symm ▸ H.2

end DurfeeCCS.Step09
