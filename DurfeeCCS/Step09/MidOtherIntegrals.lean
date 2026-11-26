module

public import DurfeeCCS.Step09.MidOtherGaussian
public import DurfeeCCS.Step09.MidOtherModeBounds
public import DurfeeCCS.Step09.MidOtherLattice
public import DurfeeCCS.Step09.MidMajorContinuity
public import DurfeeCCS.Step09.MidMultiplierUniform

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Absolute frequency integrals on the central interval. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Real MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

def midOtherMass (n : ℕ) (r : ℝ) (p : ℤ) (l h : ℝ) : ℝ :=
  ∫ η in l..h, ∫ χ : ℝ, ‖midIntegrand n r p η χ‖

def midOtherMassFactor (n : ℕ) (r : ℝ) : ℝ :=
  midU n r / (4 * π ^ 2 * saddleAmplitude n r)

def midOtherNormalizedMass (n : ℕ) (r : ℝ) (p : ℤ) : ℝ :=
  midOtherMassFactor n r * midOtherMass n r p (-8) 8

theorem midOtherMassFactor_pos {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    0 < midOtherMassFactor n r := by
  unfold midOtherMassFactor
  exact div_pos (saddleU_pos hn hr) (by
    have h := saddleAmplitude_pos hn hr
    positivity)

theorem midOtherMass_nonneg (n : ℕ) (r : ℝ) (p : ℤ) {l h : ℝ} (hlh : l ≤ h) :
    0 ≤ midOtherMass n r p l h := by
  unfold midOtherMass
  refine intervalIntegral.integral_nonneg hlh (fun _ _ => ?_)
  exact integral_nonneg fun _ => norm_nonneg _

theorem midOtherNormalizedMass_nonneg {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (p : ℤ) :
    0 ≤ midOtherNormalizedMass n r p :=
  mul_nonneg (midOtherMassFactor_pos hn hr).le (midOtherMass_nonneg n r p (by norm_num))

theorem midOther_full_gauss_bound {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 1 ≤ r) {p : ℤ}
    {δ K C : ℝ} (hK : 0 ≤ K) (hC : K*16*√(130*π)/(2*π) ≤ C)
    (hMult : ∀ η : ℝ, |η| ≤ 8 → ∀ χ : ℝ, ‖midMultiplier r p (midEtaPoint n r η) χ‖ ≤ K)
    (hPhase : ∀ η : ℝ, |η| ≤ 8 → ∀ χ : ℝ,
      ((n : ℂ)*midEtaPoint n r η + midPhase r p χ/midEtaPoint n r η).re ≤
        2*midOmega n r - δ - √(n : ℝ)*χ^2/(130*(saddleS r).re)) :
    IntegrableOn (Function.uncurry (midIntegrand n r p)) (Icc (-8) 8 ×ˢ (univ : Set ℝ))
      (volume.prod volume) ∧ midOtherNormalizedMass n r p ≤ √(midOmega n r)*exp (-δ)*C := by
  have hrp : 0 < r := by linarith
  have hf : Measurable (Function.uncurry (midIntegrand n r p)) :=
    (continuous_midIntegrand hn hr p).measurable
  have H := midOtherGaussian_unshifted hn (r := r) (p := p) (l := -8) (h := 8)
    hrp (by norm_num) (S := univ) MeasurableSet.univ hf hK hC
    (fun η hη χ _ => hMult η (abs_le.mpr hη) χ)
    (fun η hη χ _ => hPhase η (abs_le.mpr hη) χ)
  refine ⟨H.1, ?_⟩
  unfold midOtherNormalizedMass midOtherMassFactor midOtherMass
  simpa only [Measure.restrict_univ, sub_neg_eq_add, show (8 : ℝ) + 8 = 16 by norm_num, div_self
    (show (16 : ℝ) ≠ 0 by norm_num), one_mul] using H.2

theorem mid_integrable_all {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ exp 1 * √(n : ℝ)) (p : ℤ) :
    IntegrableOn (Function.uncurry (midIntegrand n r p))
      (Icc (-8) 8 ×ˢ (univ : Set ℝ)) (volume.prod volume) :=
  (midOther_full_gauss_bound (by omega) hr (by norm_num) midOtherGaussian_constant_large
    (fun η hη χ => (norm_midMultiplier_lt_2100 hn hr hmax hη p χ).le)
    (fun η hη χ => midRe_exponent_nonprincipal (by omega) hr hη p)).1

theorem mid_intervalIntegrable_all {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ exp 1 * √(n : ℝ)) (p : ℤ) {l h : ℝ} (hl : -8 ≤ l) (hh : h ≤ 8) (hlh : l ≤ h) :
    IntervalIntegrable (fun η : ℝ => ∫ χ : ℝ, midIntegrand n r p η χ) volume l h := by
  have hprod := mid_integrable_all hn hr hmax p
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at hprod
  have hI : IntegrableOn (fun η : ℝ => ∫ χ : ℝ, midIntegrand n r p η χ) (Icc (-8) 8) :=
    hprod.integral_prod_left
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hlh).2
    (hI.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc hl hh)))

/-- The integrable Gaussian series controlling all far frequencies. -/
theorem midOther_far_bound {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ exp 1 * √(n : ℝ)) :
    let a := (saddleS r).re
    let F (p : ℤ) := if 40*a < |midFrequency p| then midOtherNormalizedMass n r p else 0
    Summable F ∧ (∑' p : ℤ, F p) < 0.000001 := by
  let a := (saddleS r).re
  let x := √(n : ℝ)
  let u := midU n r
  let ω := midOmega n r
  let F (p : ℤ) := if 40*a < |midFrequency p| then midOtherNormalizedMass n r p else 0
  let K := (6 : ℝ) * 109000 * √ω * exp (-4*ω)
  have hn' : 0 < n := by omega
  have hx : 80 ≤ x := le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hx' : 0 < x := by linarith
  have hrp : 0 < r := by linarith
  have ha : 1 < a := (midSaddle_data hn hr hmax).1
  have ha' : 0 < a := by linarith
  have ho : 80 ≤ ω := by
    change 80 ≤ a*x
    exact hx.trans (le_mul_of_one_le_left (by positivity) ha.le)
  have hu : 0 < u := saddleU_pos hn' hrp
  have hu' : u ≤ 0.072 := (midU_lt_072 hn hr hmax).le
  obtain ⟨hU,hUs⟩ := midOtherFarWeight_sum hu hu'
  let W (p : ℤ) := (109000 * √ω * exp (-4*ω)) * midOtherFarWeight u p
  have hW : Summable W := hU.mul_left _
  have hf0 (p : ℤ) : 0 ≤ F p := by
    unfold F
    split_ifs <;> simp [midOtherNormalizedMass_nonneg hn' hrp p]
  have hpoint (p : ℤ) : F p ≤ W p := by
    unfold F
    split_ifs with hp
    · have hm := (midOther_full_gauss_bound (δ := x*(midFrequency p)^2/(200*a)) hn' hr
        (by norm_num) midOtherGaussian_constant_large
        (fun η hη χ => (norm_midMultiplier_lt_2100 hn hr hmax hη p χ).le)
        (fun η hη χ => midRe_exponent_far_mode hn' hr ha.le hη hp)).2
      have hpq := pow_le_pow_left₀ (show 0 ≤ 40*a by positivity) hp.le 2
      rw [sq_abs] at hpq
      have hsplit : 4*ω + (midFrequency p)^2/(400*u) ≤ x*(midFrequency p)^2/(200*a) := by
        change 4*(a*x) + (midFrequency p)^2/(400*(a/x)) ≤ _
        have h₀ : (midFrequency p)^2/(400*(a/x)) = (x/(400*a))*(midFrequency p)^2 := by
          field_simp
        rw [h₀]
        have ht := mul_le_mul_of_nonneg_left hpq (show 0 ≤ x / (400*a) by positivity)
        have ht' : (x/(400*a))*(40*a)^2 = 4*(a*x) := by field_simp; ring
        have ht'' : x*(midFrequency p)^2/(200*a) =
            2*(x/(400*a))*(midFrequency p)^2 := by ring
        rw [ht'] at ht
        rw [ht'']
        linarith only [ht]
      have hExp := exp_le_exp.mpr (neg_le_neg hsplit)
      have hN : exp (-(4*ω + (midFrequency p)^2/(400*u))) =
          exp (-4*ω) * midOtherFarWeight u p := by
        unfold midOtherFarWeight
        rw [← exp_add]
        congr 1
        ring
      rw [hN] at hExp
      refine hm.trans ?_
      unfold W
      have H := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hExp (show 0 ≤ √ω by positivity)) (show (0 : ℝ) ≤ 109000 by norm_num)
      convert H using 1 <;> ring
    · unfold W midOtherFarWeight
      positivity
  have hf : Summable F := hW.of_nonneg_of_le hf0 hpoint
  refine ⟨hf, (hf.tsum_le_tsum hpoint hW).trans_lt ?_⟩
  unfold W
  rw [tsum_mul_left]
  have hb := mul_le_mul_of_nonneg_left hUs (show 0 ≤ 109000*√ω*exp (-4*ω) by positivity)
  have hb6 : (109000*√ω*exp (-4*ω)) * (5 : ℝ) ≤ K := by
    unfold K
    nlinarith only [show 0 ≤ 109000*√ω*exp (-4*ω) by positivity]
  exact (hb.trans hb6).trans_lt (midOther_far_budget_lt ho)

end DurfeeCCS.Step09
