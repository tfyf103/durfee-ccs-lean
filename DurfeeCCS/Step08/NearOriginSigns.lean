module

public import DurfeeCCS.Step08.NearOriginDefs
public import DurfeeCCS.Step06.Bessel
public import DurfeeCCS.Step06.BesselDerivative
public import DurfeeCCS.Step06.BesselIntegrals
public import DurfeeCCS.Step06.Nemes
public import DurfeeCCS.Step07.ElementaryBounds
public import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Real Bessel margins and explicit constants used by Corollary 3.2. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open DurfeeCCS.Step06 DurfeeCCS.Step07 MeasureTheory Set
open scoped Real

/-- Modified Bessel function at a real argument. -/
def originI (ν : ℕ) (x : ℝ) : ℝ := (besselI ν (x : ℂ)).re

/-- Ordinary Bessel function at a real argument. -/
def originJ (ν : ℕ) (x : ℝ) : ℝ := (besselJ ν (x : ℂ)).re

private theorem besselITerm_ofReal (ν k : ℕ) (x : ℝ) :
    besselITerm ν k (x : ℂ) =
      (((x / 2) ^ (2 * k + ν) / ((k.factorial : ℝ) * ((k + ν).factorial : ℝ)) : ℝ) : ℂ) := by
  push_cast
  rfl

theorem originI_pos (ν : ℕ) {x : ℝ} (hx : 0 < x) : 0 < originI ν x := by
  have hs := summable_besselITerm ν (x : ℂ)
  have hsr : Summable (fun k => (besselITerm ν k (x : ℂ)).re) :=
    hs.map Complex.reCLM Complex.reCLM.continuous
  unfold originI besselI
  rw [Complex.re_tsum hs]
  refine lt_of_lt_of_le ?_ (hsr.le_tsum 0 fun k _ => ?_)
  · rw [besselITerm_ofReal, Complex.ofReal_re]
    positivity
  · rw [besselITerm_ofReal, Complex.ofReal_re]
    positivity

private theorem originI_ofReal (ν : ℕ) (x : ℝ) :
    (originI ν x : ℂ) = besselI ν (x : ℂ) := by
  unfold originI besselI
  rw [Complex.re_tsum (summable_besselITerm ν (x : ℂ)), Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  rw [besselITerm_ofReal, Complex.ofReal_re]

private theorem originJ_ofReal (ν : ℕ) (x : ℝ) :
    (originJ ν x : ℂ) = besselJ ν (x : ℂ) :=
  (besselJ_ofReal_eq ν x).symm

private theorem originI_zero_integral (x : ℝ) :
    originI 0 x = (∫ θ in (0 : ℝ)..π, Real.exp (x * Real.cos θ)) / π := by
  rw [originI, besselI_zero_integral]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp,
    intervalIntegral.integral_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]
  ring

private theorem exp_four_gt : 50 < Real.exp (4 : ℝ) := by
  refine lt_of_lt_of_le ?_ (expTaylor_le_exp (by norm_num) 9)
  norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

private theorem exp_five_gt : 140 < Real.exp (5 : ℝ) := by
  refine lt_of_lt_of_le ?_ (expTaylor_le_exp (by norm_num) 11)
  norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

private theorem gaussian_tail_le {b : ℝ} (hb : 0 < b) :
    (∫ θ : ℝ in Ioi π, Real.exp (-b * θ ^ 2)) ≤ Real.exp (-b * π ^ 2) / (b * π) := by
  have hβ : -b * π < 0 := by nlinarith [mul_pos hb Real.pi_pos]
  calc
    _ ≤ ∫ θ : ℝ in Ioi π, Real.exp ((-b * π) * θ) := by
      apply setIntegral_mono_on (integrable_exp_neg_mul_sq hb).integrableOn
        (integrableOn_exp_mul_Ioi hβ π) measurableSet_Ioi
      intro θ hθ
      apply Real.exp_le_exp.mpr
      have hπθ : π < θ := hθ
      have hdiff := mul_nonneg hb.le (mul_nonneg (Real.pi_pos.le.trans hπθ.le) (sub_nonneg.mpr hπθ.le))
      nlinarith
    _ = _ := by
      rw [integral_exp_mul_Ioi hβ]
      have he : -b * π * π = -b * π ^ 2 := by ring
      rw [he, neg_mul b π, neg_div_neg_eq]

theorem originI_zero_lower {x : ℝ} (hx : π ≤ x) :
    (99 / 100 : ℝ) * Real.exp x / Real.sqrt (2 * π * x) < originI 0 x := by
  let b := x / 2
  have hp := Real.pi_pos
  have hp3 : 3 < π := by linarith [Real.pi_gt_d2]
  have hx0 : 0 < x := hp.trans_le hx
  have hb : 0 < b := by dsimp [b]; positivity
  let g : ℝ → ℝ := fun θ => Real.exp (-b * θ ^ 2)
  have hg : Integrable g := integrable_exp_neg_mul_sq hb
  have htail' : Real.exp (-b * π ^ 2) < 1 / 100 := by
    have hbπ : 5 ≤ b * π ^ 2 := by
      have hb1 : 1 ≤ b := by dsimp [b]; linarith
      have h1 : 5 ≤ π ^ 2 := by nlinarith
      calc
        5 ≤ π ^ 2 := h1
        _ = 1 * π ^ 2 := by ring
        _ ≤ b * π ^ 2 := mul_le_mul_of_nonneg_right hb1 (sq_nonneg π)
    have he := Real.exp_le_exp.mpr (show -b * π ^ 2 ≤ -5 by linarith)
    rw [Real.exp_neg] at he
    refine he.trans_lt ?_
    rw [inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 5) (by norm_num)]
    linarith [exp_five_gt]
  have hbs : Real.sqrt b * Real.sqrt b = b := by
    rw [← pow_two, Real.sq_sqrt hb.le]
  have hs : 1 ≤ Real.sqrt b := Real.le_sqrt_of_sq_le (by dsimp [b]; nlinarith)
  have hps : 1 ≤ Real.sqrt π := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs' : 1 / (b * π) ≤ Real.sqrt (π / b) / 2 := by
    rw [Real.sqrt_div hp.le]
    apply (div_le_iff₀ (mul_pos hb hp)).2
    field_simp [(Real.sqrt_pos.2 hb).ne']
    nlinarith [mul_le_mul_of_nonneg_left hps hp.le,
      mul_le_mul_of_nonneg_right hs (show 0 ≤ π * Real.sqrt π by positivity)]
  have htail : (∫ θ in Ioi π, g θ) < (1 / 100 : ℝ) * (Real.sqrt (π / b) / 2) := by
    refine (gaussian_tail_le hb).trans_lt ?_
    calc
      _ < (1 / 100 : ℝ) * (1 / (b * π)) := by
        rw [div_eq_mul_one_div]
        exact mul_lt_mul_of_pos_right htail' (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hs' (by norm_num)
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (a := 0) (b := π) hg.integrableOn hg.integrableOn
  change _ + _ = (∫ θ in Ioi (0 : ℝ), Real.exp (-b * θ ^ 2)) at hsplit
  rw [integral_gaussian_Ioi] at hsplit
  have hgauss : 99 / 100 * (Real.sqrt (π / b) / 2) < ∫ θ in (0 : ℝ)..π, g θ := by
    linarith
  have hcos : Real.exp x * (∫ θ in (0 : ℝ)..π, g θ) ≤
      ∫ θ in (0 : ℝ)..π, Real.exp (x * Real.cos θ) := by
    rw [← intervalIntegral.integral_const_mul]
    have hgcont : Continuous g := by dsimp [g]; fun_prop
    have hhcont : Continuous (fun θ : ℝ => Real.exp (x * Real.cos θ)) := by fun_prop
    apply intervalIntegral.integral_mono_on hp.le
      ((continuous_const.mul hgcont).intervalIntegrable 0 π) (hhcont.intervalIntegrable 0 π)
    intro θ _
    change Real.exp x * Real.exp (-b * θ ^ 2) ≤ Real.exp (x * Real.cos θ)
    rw [← Real.exp_add, Real.exp_le_exp]
    have hh := mul_le_mul_of_nonneg_left
      (Real.one_sub_sq_div_two_le_cos (x := θ)) hx0.le
    dsimp [b]
    linarith
  have hconvert : Real.sqrt (π / b) / 2 / π = 1 / Real.sqrt (2 * π * x) := by
    have hb' : π / b * (2 * π * x) = (2 * π) ^ 2 := by dsimp [b]; field_simp
    have hprod : Real.sqrt (π / b) * Real.sqrt (2 * π * x) = 2 * π := by
      rw [← Real.sqrt_mul (show 0 ≤ π / b by positivity), hb',
        Real.sqrt_sq (show 0 ≤ 2 * π by positivity)]
    rw [show Real.sqrt (π / b) / 2 / π = Real.sqrt (π / b) / (2 * π) by ring,
      div_eq_div_iff (by positivity) (by positivity), one_mul]
    exact hprod
  rw [originI_zero_integral]
  have hstrong := mul_lt_mul_of_pos_left hgauss (Real.exp_pos x)
  have hfinal := div_lt_div_of_pos_right (hstrong.trans_le hcos) hp
  have heq : Real.exp x * ((99 / 100 : ℝ) * (Real.sqrt (π / b) / 2)) / π =
      (99 / 100 : ℝ) * Real.exp x / Real.sqrt (2 * π * x) := by
    rw [show Real.exp x * ((99 / 100 : ℝ) * (Real.sqrt (π / b) / 2)) / π =
      (99 / 100 : ℝ) * Real.exp x * (Real.sqrt (π / b) / 2 / π) by ring, hconvert]
    ring
  rwa [heq] at hfinal

theorem originI_one_lower {t : ℝ} (ht : 1 ≤ t) :
    (1 - 1 / t) * originI 0 t < originI 1 t := by
  let F (z : ℝ) := Real.exp z * (originI 1 z - (1 - 1 / z) * originI 0 z)
  have hderiv (z : ℝ) (hz : 1 ≤ z) :
      HasDerivAt F (Real.exp z * (z - 1) / z ^ 2 * originI 0 z) z := by
    have hz0 : z ≠ 0 := by linarith
    have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast hz0
    have hI0 : HasDerivAt (originI 0) (originI 1 z) z :=
      (hasDerivAt_besselI_zero (z : ℂ)).real_of_complex
    have hI1 : HasDerivAt (originI 1) (originI 0 z - originI 1 z / z) z := by
      change HasDerivAt (fun t : ℝ => (besselI 1 (t : ℂ)).re) _ z
      simpa only [originI, Complex.sub_re, Complex.div_ofReal_re, Complex.ofReal_re]
        using (hasDerivAt_besselI_one_of_ne_zero (z : ℂ) hzc).real_of_complex
    have hi := (hasDerivAt_const z (1 : ℝ)).div (hasDerivAt_id z) hz0
    have hg := (hasDerivAt_const z (1 : ℝ)).sub hi
    have hF := (Real.hasDerivAt_exp z).mul (hI1.sub (hg.mul hI0))
    convert hF using 1
    · rfl
    · simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq, zero_mul, one_mul, zero_sub]
      field_simp
      ring
  have hmono : MonotoneOn F (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun z hz => (hderiv z hz).continuousAt.continuousWithinAt
    · exact fun z hz => (hderiv z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : 1 ≤ z := interior_subset hz
      rw [(hderiv z hz').deriv]
      exact mul_nonneg (div_nonneg (mul_nonneg (Real.exp_pos z).le (sub_nonneg.mpr hz')) (sq_nonneg z))
        (originI_pos 0 (by linarith)).le
  have hF : 0 < F t := by
    have h1 : 0 < F 1 := by
      simpa [F] using mul_pos (Real.exp_pos 1) (originI_pos 1 (by norm_num : (0 : ℝ) < 1))
    exact h1.trans_le (hmono (a := 1) le_rfl ht ht)
  exact sub_pos.mp (pos_of_mul_pos_right hF (Real.exp_pos t).le)

/-- The sign of the coefficient at the k-th near-origin sample. -/
def originParity (k : ℕ) : ℝ := (-1 : ℝ) ^ k

private theorem originParity_abs (k : ℕ) : |originParity k| = 1 := by
  simp [originParity, abs_pow]

private theorem originParity_square (k : ℕ) : originParity k ^ 2 = 1 := by
  rw [← sq_abs, originParity_abs, one_pow]

private theorem cos_origin_phase_zero (k : ℕ) :
    Real.cos (besselPhase 0 ((k : ℝ) * π)) = originParity k * (Real.sqrt 2 / 2) := by
  simp only [besselPhase, Nat.cast_zero, zero_mul, zero_div, sub_zero, originParity,
    Real.cos_nat_mul_pi_sub, Real.cos_pi_div_four]

private theorem cos_origin_phase_one (k : ℕ) :
    Real.cos (besselPhase 1 ((k : ℝ) * π)) = -originParity k * (Real.sqrt 2 / 2) := by
  rw [show besselPhase 1 ((k : ℝ) * π) = (k : ℝ) * π - (π / 4 + π / 2) by
    simp only [besselPhase, Nat.cast_one, one_mul]; ring,
    Real.cos_nat_mul_pi_sub, Real.cos_add_pi_div_two, Real.sin_pi_div_four, mul_neg, neg_mul, originParity]

private theorem signed_lower_of_nemes (k : ℕ) {a e d : ℝ}
    (h : |a - originParity k * e| ≤ d) : e - d ≤ originParity k * a := by
  have ht : |originParity k * (a - originParity k * e)| ≤ d := by
    rwa [abs_mul, originParity_abs, one_mul]
  rw [mul_sub, ← mul_assoc, ← pow_two, originParity_square, one_mul] at ht
  linarith [(abs_le.mp ht).1]

/-- Rational lower bounds for the two signed, normalized ordinary Bessel values. -/
theorem originJ_signed_lower (k : ℕ) (hk : 1 ≤ k) :
    let x := (k : ℝ) * π
    let A := Real.sqrt (π * x / 2)
    79 / 120 < A * (originParity k * originJ 0 x) ∧
      23 / 40 < A * (-(originParity k * originJ 1 x)) := by
  dsimp only
  let x := (k : ℝ) * π
  let A := Real.sqrt (π * x / 2)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx : π ≤ x := by dsimp only [x]; nlinarith [mul_nonneg (sub_nonneg.mpr hk') Real.pi_pos.le]
  have hx3 : 3 < x := by linarith [Real.pi_gt_d2]
  have hx0 : 0 < x := by linarith
  have hsqrt : (7 / 10 : ℝ) < Real.sqrt 2 / 2 := by
    have hs : (1.4 : ℝ) < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    linarith
  have he0 : 1 / (8 * x) < (1 / 24 : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have he1 : 3 / (8 * x) < (3 / 24 : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have h0 : |A * originJ 0 x - originParity k * (Real.sqrt 2 / 2)| ≤ 1 / (8 * x) := by
    have h := nemes_first_error 0 (Or.inl rfl) hx0
    rw [show |4 * ((0 : ℕ) : ℝ) ^ 2 - 1| = (1 : ℝ) by norm_num] at h
    simpa only [A, originJ, x, cos_origin_phase_zero] using h
  have h1 : |(-(A * originJ 1 x)) - originParity k * (Real.sqrt 2 / 2)| ≤ 3 / (8 * x) := by
    rw [show -(A * originJ 1 x) - originParity k * (Real.sqrt 2 / 2) =
      -(A * originJ 1 x + originParity k * (Real.sqrt 2 / 2)) by ring, abs_neg]
    have hf := nemes_first_error 1 (Or.inr rfl) hx0
    rw [show |4 * ((1 : ℕ) : ℝ) ^ 2 - 1| = (3 : ℝ) by norm_num] at hf
    change |A * originJ 1 x - Real.cos (besselPhase 1 ((k : ℝ) * π))| ≤ _ at hf
    rw [cos_origin_phase_one, neg_mul, sub_neg_eq_add] at hf
    exact hf
  have h0' := signed_lower_of_nemes k h0
  have h1' := signed_lower_of_nemes k h1
  change 79 / 120 < A * (originParity k * originJ 0 x) ∧
    23 / 40 < A * (-(originParity k * originJ 1 x))
  constructor
  · rw [mul_left_comm A]
    linarith
  · rw [mul_neg, mul_left_comm A, ← mul_neg]
    linarith

private theorem signed_originJ_two_pos (k : ℕ) (hk : 1 ≤ k) :
    let x := (k : ℝ) * π
    0 < -(originParity k * originJ 2 x) := by
  dsimp only
  let x := (k : ℝ) * π
  have hx : 0 < x := by dsimp [x]; positivity
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hJ := besselJ_two_eq (x : ℂ) hxc
  rw [← originJ_ofReal 2 x, ← originJ_ofReal 1 x, ← originJ_ofReal 0 x] at hJ
  have hJ' : originJ 2 x = 2 * originJ 1 x / x - originJ 0 x := by exact_mod_cast hJ
  have h := originJ_signed_lower k hk
  change _ < Real.sqrt (π * x / 2) * (originParity k * originJ 0 x) ∧
    _ < Real.sqrt (π * x / 2) * (-(originParity k * originJ 1 x)) at h
  have h0 := pos_of_mul_pos_right ((by norm_num : 0 < (79 / 120 : ℝ)).trans h.1)
    (Real.sqrt_nonneg _)
  have h1 := pos_of_mul_pos_right ((by norm_num : 0 < (23 / 40 : ℝ)).trans h.2)
    (Real.sqrt_nonneg _)
  change 0 < -(originParity k * originJ 2 x)
  rw [hJ']
  have heq : -(originParity k * (2 * originJ 1 x / x - originJ 0 x)) =
      2 / x * (-(originParity k * originJ 1 x)) + originParity k * originJ 0 x := by ring
  rw [heq]
  positivity

/-- The signed main Bessel term at every positive integral multiple of π. -/
theorem bessel_signed_margin (k : ℕ) (hk : 1 ≤ k) :
    let x := (k : ℝ) * π
    (63 / 400 : ℝ) * Real.exp x <
      originParity k * (x / 2) *
        (originJ 0 x * originI 1 x - originJ 1 x * originI 0 x) ∧
    0 < -(originParity k * originJ 2 x * originI 2 x) := by
  dsimp only
  let x := (k : ℝ) * π
  let A := Real.sqrt (π * x / 2)
  let U := A * (originParity k * originJ 0 x)
  let V := A * (-(originParity k * originJ 1 x))
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hxπ : π ≤ x := by dsimp [x]; nlinarith [mul_nonneg (sub_nonneg.mpr hk') Real.pi_pos.le]
  have hx3 : 3 < x := by linarith [Real.pi_gt_d2]
  have hx0 : 0 < x := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hs : (79 / 120 : ℝ) < U ∧ (23 / 40 : ℝ) < V := originJ_signed_lower k hk
  have hI0 := originI_pos 0 hx0
  have hI1 := originI_one_lower (t := x) (by linarith)
  have ht : (2 / 3 : ℝ) < 1 - 1 / x := by
    have hq : 1 / x < (1 / 3 : ℝ) := by
      apply (div_lt_div_iff₀ hx0 (by norm_num)).mpr
      linarith
    linarith
  have hI1' : (2 / 3 : ℝ) * originI 0 x < originI 1 x :=
    (mul_lt_mul_of_pos_right ht hI0).trans hI1
  have hUV : originI 0 x < U * originI 1 x + V * originI 0 x := by
    have hU : 0 < U := (by norm_num : 0 < (79 / 120 : ℝ)).trans hs.1
    have hA1 := mul_lt_mul_of_pos_left hI1' hU
    have hA0 := mul_lt_mul_of_pos_right hs.1 (show 0 < (2 / 3 : ℝ) * originI 0 x by positivity)
    have hB0 := mul_lt_mul_of_pos_right hs.2 hI0
    nlinarith [hA0.trans hA1]
  have hp := Real.pi_pos
  have hP : A * Real.sqrt (2 * π * x) = π * x := by
    dsimp [A]
    rw [← Real.sqrt_mul (show 0 ≤ π * x / 2 by positivity),
      show π * x / 2 * (2 * π * x) = (π * x) ^ 2 by ring,
      Real.sqrt_sq (show 0 ≤ π * x by positivity)]
  have hpiprec : π < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d6]
  have lower : (63 / 400 : ℝ) < 99 / (200 * π) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith
  have hS : originParity k * (x / 2) *
        (originJ 0 x * originI 1 x - originJ 1 x * originI 0 x) =
      (x / 2 / A) * (U * originI 1 x + V * originI 0 x) := by
    dsimp [U, V]
    field_simp
    ring
  change _ < originParity k * (x / 2) *
      (originJ 0 x * originI 1 x - originJ 1 x * originI 0 x) ∧
      0 < -(originParity k * originJ 2 x * originI 2 x)
  constructor
  · rw [hS]
    calc
      _ < (99 / (200 * π) : ℝ) * Real.exp x := mul_lt_mul_of_pos_right lower (Real.exp_pos x)
      _ = (x / 2 / A) * ((99 / 100 : ℝ) * Real.exp x / Real.sqrt (2 * π * x)) := by
        have he : (x / 2 / A) * ((99 / 100 : ℝ) * Real.exp x / Real.sqrt (2 * π * x)) =
              (99 / 200 : ℝ) * Real.exp x * x / (A * Real.sqrt (2 * π * x)) := by ring
        rw [he, hP]
        field_simp
      _ < (x / 2 / A) * originI 0 x := mul_lt_mul_of_pos_left (originI_zero_lower hxπ) (by positivity)
      _ < _ := mul_lt_mul_of_pos_left hUV (by positivity)
  · rw [← neg_mul]
    exact mul_pos (signed_originJ_two_pos k hk) (originI_pos 2 hx0)

private theorem pow_mul_exp_maximum (j : ℕ) (hj : 0 < j) {σ : ℝ} (hσ : 0 ≤ σ) :
    σ ^ j * Real.exp (-σ / 2) ≤ (2 * (j : ℝ)) ^ j * Real.exp (-(j : ℝ)) := by
  let d := 2 * (j : ℝ)
  let y := σ / d
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have hd : 0 < d := by dsimp [d]; positivity
  have hy : 0 ≤ y := div_nonneg hσ hd.le
  have hdy : d * y = σ := by dsimp [y]; field_simp
  have hmax : y ^ j ≤ Real.exp ((j : ℝ) * (y - 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hy (by linarith [Real.add_one_le_exp (y - 1)]) j
  calc
    σ ^ j * Real.exp (-σ / 2) = d ^ j * (y ^ j * Real.exp (-σ / 2)) := by
      have hp : σ ^ j = d ^ j * y ^ j := by rw [← hdy, mul_pow]
      rw [hp, mul_assoc]
    _ ≤ d ^ j * (Real.exp ((j : ℝ) * (y - 1)) * Real.exp (-σ / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le) (pow_nonneg hd.le _)
    _ = _ := by
      rw [← Real.exp_add]
      have hσ' : (j : ℝ) * (y - 1) + -σ / 2 = -(j : ℝ) := by
        dsimp [d] at hdy
        linarith
      rw [hσ']

private theorem exp_small_125 : Real.exp (1 / 6 + 1 / 500) < (5 / 4 : ℝ) := by
  refine (exp_le_expTaylor_add_remainder (n := 4) (by norm_num) (by norm_num)).trans_lt ?_
  norm_num [expTaylor, expRemainder, Finset.sum_range_succ, Nat.factorial]

private theorem exp_small_150 : Real.exp (17 / 50) < (3 / 2 : ℝ) := by
  refine (exp_le_expTaylor_add_remainder (n := 5) (by norm_num) (by norm_num)).trans_lt ?_
  norm_num [expTaylor, expRemainder, Finset.sum_range_succ, Nat.factorial]

/-- The scalar error budget of Lemma 3.1 at the thresholds of Corollary 3.2. -/
theorem nearOrigin_error_margin {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : 6400 ≤ n)
    (hr : σ ^ 2 / (n : ℝ) ≤ 1 / 40) (hΔ : nearOriginDelta σ n ≤ 1 / 3) :
    nearOriginEpsilon σ n < 1 / 500 ∧ nearOriginBudget σ n < 3 / 20 := by
  let δ := nearOriginDelta σ n
  let ε := nearOriginEpsilon σ n
  let r := σ ^ 2 / (n : ℝ)
  have hn' : (6400 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hδ0 : 0 ≤ δ := by dsimp [δ, nearOriginDelta]; positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hε0 : 0 ≤ ε := by
    change 0 ≤ δ * (0.66 / n + 0.228 * r + 0.35 * r / n)
    positivity
  have hε : ε < 1 / 500 := by
    change δ * (0.66 / n + 0.228 * r + 0.35 * r / n) < _
    have h1 : 0.66 / (n : ℝ) ≤ 0.66 / 6400 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn'
    have h2 := mul_le_mul_of_nonneg_left hr (by norm_num : 0 ≤ (0.228 : ℝ))
    have h3 : 0.35 * r / (n : ℝ) ≤ 0.35 * (1 / 40) / 6400 := by
      calc
        _ ≤ 0.35 * r / 6400 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hn'
        _ ≤ _ := by gcongr
    refine lt_of_le_of_lt (mul_le_mul hΔ (add_le_add (add_le_add h1 h2) h3) (by positivity) (by norm_num)) ?_
    norm_num
  have hp3 : 3 < π := by linarith [Real.pi_gt_d2]
  have hp9 : 9 ≤ π ^ 2 := by nlinarith
  have hD : δ ≤ (1 / 3 : ℝ) := hΔ
  have he1 : Real.exp (δ / 2 + ε) ≤ (5 / 4 : ℝ) :=
    ((Real.exp_le_exp.mpr (by linarith)).trans_lt exp_small_125).le
  have he2 : Real.exp (δ / 2) ≤ (5 / 4 : ℝ) :=
    ((Real.exp_le_exp.mpr (by linarith)).trans_lt exp_small_125).le
  have he3 : Real.exp (1.02 * δ) ≤ (3 / 2 : ℝ) :=
    ((Real.exp_le_exp.mpr (by linarith)).trans_lt exp_small_150).le
  have hp4 : σ ^ 4 * Real.exp (-σ / 2) ≤ (8 : ℝ) ^ 4 / 50 := by
    refine (pow_mul_exp_maximum 4 (by decide) hσ.le).trans ?_
    have he : Real.exp (-4 : ℝ) ≤ 1 / 50 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) exp_four_gt.le
    calc
      _ = (8 : ℝ) ^ 4 * Real.exp (-4 : ℝ) := by norm_num
      _ ≤ (8 : ℝ) ^ 4 * (1 / 50) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := by ring
  have hp5 : σ ^ 5 * Real.exp (-σ / 2) ≤ (10 : ℝ) ^ 5 / 140 := by
    refine (pow_mul_exp_maximum 5 (by decide) hσ.le).trans ?_
    have he : Real.exp (-5 : ℝ) ≤ 1 / 140 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) exp_five_gt.le
    calc
      _ = (10 : ℝ) ^ 5 * Real.exp (-5 : ℝ) := by norm_num
      _ ≤ (10 : ℝ) ^ 5 * (1 / 140) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := by ring
  have hsmall : δ ^ 2 / 8 ≤ (1 / 72 : ℝ) := by
    have hp := pow_le_pow_left₀ hδ0 hD 2
    nlinarith
  have hfirst :
      15 / (2 * π) * (ε * Real.exp (δ / 2 + ε) + δ ^ 2 / 8 * Real.exp (δ / 2)) ≤
        25 / 8 * (1 / 500 + 1 / 72) := by
    have ha : 15 / (2 * π) ≤ (5 / 2 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    have hb := mul_le_mul hε.le he1 (Real.exp_pos _).le (by norm_num : 0 ≤ (1 / 500 : ℝ))
    have hc := mul_le_mul hsmall he2 (Real.exp_pos _).le (by norm_num : 0 ≤ (1 / 72 : ℝ))
    have hv := mul_le_mul ha (add_le_add hb hc) (by positivity) (by norm_num : 0 ≤ (5 / 2 : ℝ))
    norm_num at hv ⊢
    exact hv
  let p₄ := σ ^ 4 * Real.exp (-σ / 2)
  let p₅ := σ ^ 5 * Real.exp (-σ / 2)
  let bound : ℝ := (3 / 2) * (0.48 * (8 : ℝ) ^ 4 / 50 + 0.36 * (10 : ℝ) ^ 5 / 140) +
    (8 : ℝ) ^ 4 / (9 * 50) + (10 : ℝ) ^ 5 / (4 * 140)
  have hsecond :
      δ * Real.exp (-σ / 2) *
        ((0.48 * σ + 0.36 * σ ^ 2) * Real.exp (1.02 * δ) + σ / π ^ 2 + σ ^ 2 / 4)
        ≤ bound / 6400 := by
    have heq : δ * Real.exp (-σ / 2) *
        ((0.48 * σ + 0.36 * σ ^ 2) * Real.exp (1.02 * δ) + σ / π ^ 2 + σ ^ 2 / 4) =
      ((0.48 * p₄ + 0.36 * p₅) * Real.exp (1.02 * δ) + p₄ / π ^ 2 + p₅ / 4) / n := by
      dsimp [p₄, p₅]
      unfold δ nearOriginDelta
      ring
    rw [heq]
    have hp4' : p₄ / π ^ 2 ≤ (8 : ℝ) ^ 4 / (9 * 50) := by
      calc
        _ ≤ p₄ / 9 := div_le_div_of_nonneg_left (by dsimp [p₄]; positivity) (by norm_num) hp9
        _ ≤ _ := by dsimp [p₄]; linarith only [hp4]
    have hp5' : p₅ / 4 ≤ (10 : ℝ) ^ 5 / (4 * 140) := by dsimp [p₅]; linarith only [hp5]
    have hSum : 0.48 * p₄ + 0.36 * p₅ ≤ 0.48 * (8 : ℝ) ^ 4 / 50 + 0.36 * (10 : ℝ) ^ 5 / 140 := by
      dsimp [p₄, p₅]
      linarith only [hp4, hp5]
    have hPart := mul_le_mul hSum he3 (Real.exp_pos _).le (by positivity)
    apply div_le_div₀ (by dsimp [bound]; positivity) ?_ (by norm_num) hn'
    dsimp [bound]
    linarith only [hPart, hp4', hp5']
  refine ⟨hε, ?_⟩
  have hu := add_le_add hfirst hsecond
  change 15 / (2 * π) * (ε * Real.exp (δ / 2 + ε) + δ ^ 2 / 8 * Real.exp (δ / 2)) +
    δ * Real.exp (-σ / 2) *
      ((0.48 * σ + 0.36 * σ ^ 2) * Real.exp (1.02 * δ) + σ / π ^ 2 + σ ^ 2 / 4) < _
  refine hu.trans_lt ?_
  norm_num [bound]

/-- Half the Bessel argument at the k-th sample. -/
def nearOriginSigma (k : ℕ) : ℝ := (k : ℝ) * π / 2

/-- The negative argument of the Durfee polynomial at the k-th sample. -/
def nearOriginSample (n k : ℕ) : ℝ := -((k : ℝ) * π) ^ 4 / (16 * (n : ℝ) ^ 2)

theorem nearOrigin_sample_parameters {k n : ℕ} (hk : 1 ≤ k) (hn : 6400 ≤ n)
    (hn₂ : 40 * nearOriginSigma k ^ 2 ≤ (n : ℝ))
    (hn₃ : 3 * nearOriginSigma k ^ 3 ≤ (n : ℝ)) :
    let σ := nearOriginSigma k
    let r := σ ^ 2 / (n : ℝ)
    0 < r ∧ r ≤ 1 / 40 ∧ 1 ≤ σ ∧ Real.sqrt ((n : ℝ) * r) = σ ∧
      nearOriginDelta σ n ≤ 1 / 3 := by
  dsimp only
  have hn' : (6400 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hσ : 1 ≤ nearOriginSigma k := by
    unfold nearOriginSigma
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') Real.pi_pos.le, Real.pi_gt_d2]
  refine ⟨by positivity, ?_, hσ, ?_, ?_⟩
  · apply (div_le_iff₀ hn0).mpr
    linarith
  · rw [show (n : ℝ) * (nearOriginSigma k ^ 2 / n) = nearOriginSigma k ^ 2 by field_simp,
      Real.sqrt_sq (show 0 ≤ nearOriginSigma k by linarith)]
  · unfold nearOriginDelta
    apply (div_le_iff₀ hn0).mpr
    linarith

theorem nearOrigin_firstEight_thresholds {n k : ℕ} (hn : 6400 ≤ n) (hk : k ≤ 8) :
    40 * nearOriginSigma k ^ 2 ≤ (n : ℝ) ∧
      3 * nearOriginSigma k ^ 3 ≤ (n : ℝ) := by
  have hn' : (6400 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ 8 := by exact_mod_cast hk
  have hσ0 : 0 ≤ nearOriginSigma k := by unfold nearOriginSigma; positivity
  have hσ : nearOriginSigma k ≤ (4 * (22 / 7) : ℝ) := by
    unfold nearOriginSigma
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') Real.pi_pos.le, Real.pi_lt_d6]
  constructor
  · calc
      _ ≤ 40 * (4 * (22 / 7) : ℝ) ^ 2 := by gcongr
      _ ≤ 6400 := by norm_num
      _ ≤ _ := hn'
  · calc
      _ ≤ 3 * (4 * (22 / 7) : ℝ) ^ 3 := by gcongr
      _ ≤ 6400 := by norm_num
      _ ≤ _ := hn'

/-- The original small-radius domain through σ = 4π satisfies the error hypotheses. -/
theorem nearOrigin_thresholds {n : ℕ} (hn : 6400 ≤ n) {r : ℝ} (hr : 0 < r)
    (hσ : Real.sqrt ((n : ℝ) * r) ≤ 4 * π) :
    r ≤ 1 / 40 ∧ nearOriginDelta (Real.sqrt ((n : ℝ) * r)) n ≤ 1 / 3 := by
  let σ := Real.sqrt ((n : ℝ) * r)
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : nearOriginSigma 8 = 4 * π := by norm_num [nearOriginSigma]; ring
  obtain ⟨h₂, h₃⟩ := nearOrigin_firstEight_thresholds (k := 8) hn (by decide)
  rw [he] at h₂ h₃
  have hs₂ : σ ^ 2 ≤ (4 * π) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
  have hs₃ : σ ^ 3 ≤ (4 * π) ^ 3 := pow_le_pow_left₀ hσ0 hσ 3
  have hσsq : σ ^ 2 = (n : ℝ) * r := Real.sq_sqrt (by positivity)
  have hra : r = σ ^ 2 / (n : ℝ) := by
    rw [hσsq]
    field_simp
  constructor
  · rw [hra]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hs₂, h₂]
  · change σ ^ 3 / (n : ℝ) ≤ 1 / 3
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hs₃, h₃]

private theorem nearOrigin_model_re (σ : ℝ) (n : ℕ) :
    (nearOriginModel σ n).re =
      σ / (n : ℝ) * (originJ 0 (2 * σ) * originI 1 (2 * σ) - originJ 1 (2 * σ) * originI 0 (2 * σ)) -
        σ ^ 4 / (2 * (n : ℝ) ^ 2) * originJ 2 (2 * σ) * originI 2 (2 * σ) := by
  let x := 2 * σ
  have hxeq : (2 : ℂ) * (σ : ℂ) = (x : ℂ) := by simp [x]
  have h : nearOriginModel σ n =
    ((σ / (n : ℝ) * (originJ 0 x * originI 1 x - originJ 1 x * originI 0 x) -
      σ ^ 4 / (2 * (n : ℝ) ^ 2) * originJ 2 x * originI 2 x : ℝ) : ℂ) := by
    rw [nearOriginModel, hxeq, ← originJ_ofReal 0, ← originJ_ofReal 1, ← originJ_ofReal 2,
      ← originI_ofReal 0, ← originI_ofReal 1, ← originI_ofReal 2]
    push_cast
    rfl
  rw [h, Complex.ofReal_re]

theorem nearOrigin_model_signed_margin (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 0 < n) :
    (63 / 400 : ℝ) * Real.exp (2 * nearOriginSigma k) / n <
      originParity k * (nearOriginModel (nearOriginSigma k) n).re := by
  let σ := nearOriginSigma k
  let x := (k : ℝ) * π
  have hx : 2 * σ = x := by dsimp [σ, x, nearOriginSigma]; ring
  have hσ : 0 < σ := by dsimp [σ, nearOriginSigma]; positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h₁ := (bessel_signed_margin k hk).1
  have h₂ := (bessel_signed_margin k hk).2
  change (63 / 400 : ℝ) * Real.exp x <
      originParity k * (x / 2) * (originJ 0 x * originI 1 x - originJ 1 x * originI 0 x) at h₁
  change 0 < -(originParity k * originJ 2 x * originI 2 x) at h₂
  change (63 / 400 : ℝ) * Real.exp (2 * σ) / n <
    originParity k * (nearOriginModel σ n).re
  rw [nearOrigin_model_re, hx]
  have h₃ := div_lt_div_of_pos_right h₁ hn'
  have h₄ := mul_pos (show 0 < σ ^ 4 / (2 * (n : ℝ) ^ 2) by positivity) h₂
  rw [show x / 2 = σ by rw [← hx]; ring] at h₃
  ring_nf at h₃ h₄ ⊢
  linarith only [h₃, h₄]

private theorem durfee_eval_complex_at_real (n : ℕ) (z : ℝ) :
    ((DurfeeCCS.durfeePolynomialComplex n).eval (z : ℂ)).re =
      (DurfeeCCS.durfeePolynomialReal n).eval z := by
  have he : (DurfeeCCS.durfeePolynomialReal n).map Complex.ofRealHom =
      DurfeeCCS.durfeePolynomialComplex n := by
    rw [DurfeeCCS.durfeePolynomialReal, DurfeeCCS.durfeePolynomialComplex, Polynomial.map_map]
    congr 1
  rw [← he]
  change ((Polynomial.map Complex.ofRealHom (DurfeeCCS.durfeePolynomialReal n)).eval
    (Complex.ofRealHom z)).re = _
  rw [Polynomial.eval_map_apply]
  rfl

/-- Transfer the quantitative signed Bessel margin to the Durfee evaluation. -/
theorem nearOrigin_sample_margin_of_local_approximation {k n : ℕ} (hk : 1 ≤ k) (hn : 6400 ≤ n)
    (hn₂ : 40 * nearOriginSigma k ^ 2 ≤ (n : ℝ))
    (hn₃ : 3 * nearOriginSigma k ^ 3 ≤ (n : ℝ))
    (happrox : ‖(DurfeeCCS.durfeePolynomialComplex n).eval (nearOriginSample n k : ℂ) -
      nearOriginModel (nearOriginSigma k) n‖ ≤
      Real.exp (2 * nearOriginSigma k) * nearOriginBudget (nearOriginSigma k) n / n) :
    3 * Real.exp (2 * nearOriginSigma k) / (400 * (n : ℝ)) <
      originParity k * (DurfeeCCS.durfeePolynomialReal n).eval (nearOriginSample n k) := by
  let σ := nearOriginSigma k
  obtain ⟨_, hr, hσ, _, hδ⟩ := nearOrigin_sample_parameters hk hn hn₂ hn₃
  have hσ' : 0 < σ := by linarith
  have hn' : (6400 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn0' : 0 < n := by exact_mod_cast hn0
  have hmode := nearOrigin_model_signed_margin k hk n hn0'
  have hBudget := (nearOrigin_error_margin hσ' hn hr hδ).2
  let E := (DurfeeCCS.durfeePolynomialReal n).eval (nearOriginSample n k)
  let L := (nearOriginModel σ n).re
  have hRe : |E - L| ≤ Real.exp (2 * σ) * nearOriginBudget σ n / n := by
    have he := Complex.abs_re_le_norm
      ((DurfeeCCS.durfeePolynomialComplex n).eval (nearOriginSample n k : ℂ) -
        nearOriginModel σ n)
    rw [Complex.sub_re, durfee_eval_complex_at_real] at he
    exact he.trans happrox
  have hSigned : |originParity k * (E - L)| ≤ Real.exp (2 * σ) * nearOriginBudget σ n / n := by
    rwa [abs_mul, originParity_abs, one_mul]
  have hR := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hBudget (Real.exp_pos (2 * σ))) hn0
  have he := (abs_le.mp hSigned).1
  rw [mul_sub] at he
  change (63 / 400 : ℝ) * Real.exp (2 * σ) / n < originParity k * L at hmode
  change 3 * Real.exp (2 * σ) / (400 * (n : ℝ)) < originParity k * E
  linarith only [he, hR, hmode, show 3 * Real.exp (2 * σ) / (400 * (n : ℝ)) =
    (63 / 400 : ℝ) * Real.exp (2 * σ) / n - Real.exp (2 * σ) * (3 / 20) / n by ring]

/-- The exact norm inequality and domain of Lemma 3.1. -/
def NearOriginApproximationStatement : Prop :=
  ∀ {n : ℕ} {r : ℝ}, 1 ≤ n → 0 < r → r ≤ 1 / 40 →
    let σ := Real.sqrt ((n : ℝ) * r)
    1 ≤ σ → nearOriginDelta σ n ≤ 1 →
    ‖(DurfeeCCS.durfeePolynomialComplex n).eval (-(r : ℂ) ^ 2) -
      nearOriginModel σ n‖ ≤ Real.exp (2 * σ) * nearOriginBudget σ n / n

/-- Corollary 3.2 deduced from the full norm inequality of Lemma 3.1. -/
theorem nearOrigin_sign_at_kpi_of_approximation (approx : NearOriginApproximationStatement)
    {k n : ℕ} (hk : 1 ≤ k) (hn : 6400 ≤ n)
    (hn₂ : 40 * nearOriginSigma k ^ 2 ≤ (n : ℝ))
    (hn₃ : 3 * nearOriginSigma k ^ 3 ≤ (n : ℝ)) :
    Real.sign ((DurfeeCCS.durfeePolynomialReal n).eval (nearOriginSample n k)) = (-1 : ℝ) ^ k := by
  let σ := nearOriginSigma k
  let r := σ ^ 2 / (n : ℝ)
  obtain ⟨hr0, hr, hσ, he, hδ⟩ := nearOrigin_sample_parameters hk hn hn₂ hn₃
  have hσ' : 1 ≤ Real.sqrt ((n : ℝ) * r) := by rwa [he]
  have hδ' : nearOriginDelta (Real.sqrt ((n : ℝ) * r)) n ≤ 1 := by rw [he]; linarith
  have hApprox := approx (n := n) (r := r) (by omega) hr0 hr hσ' hδ'
  have heq : (nearOriginSample n k : ℂ) = -(r : ℂ) ^ 2 := by
    push_cast [nearOriginSample, r, σ, nearOriginSigma]
    ring
  rw [he, ← heq] at hApprox
  have hsign := nearOrigin_sample_margin_of_local_approximation hk hn hn₂ hn₃ hApprox
  let v := (DurfeeCCS.durfeePolynomialReal n).eval (nearOriginSample n k)
  have hpos : 0 < originParity k * v := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact lt_trans (by positivity) hsign
  have hFactor : (originParity k - 1) * (originParity k + 1) = 0 := by
    nlinarith [originParity_square k]
  change Real.sign v = originParity k
  rcases mul_eq_zero.mp hFactor with h | h
  · have hs : originParity k = 1 := by linarith
    rw [hs, one_mul] at hpos
    rw [Real.sign_of_pos hpos, hs]
  · have hs : originParity k = -1 := by linarith
    rw [hs, neg_one_mul] at hpos
    rw [Real.sign_of_neg (neg_pos.mp hpos), hs]

/-- The first eight samples use no threshold beyond n ≥ 6400. -/
theorem nearOrigin_sign_firstEight_of_approximation (approx : NearOriginApproximationStatement)
    {k n : ℕ} (hk₁ : 1 ≤ k) (hk₈ : k ≤ 8) (hn : 6400 ≤ n) :
    Real.sign ((DurfeeCCS.durfeePolynomialReal n).eval (nearOriginSample n k)) = (-1 : ℝ) ^ k := by
  obtain ⟨h₂, h₃⟩ := nearOrigin_firstEight_thresholds hn hk₈
  exact nearOrigin_sign_at_kpi_of_approximation approx hk₁ hn h₂ h₃

end DurfeeCCS.Step08
