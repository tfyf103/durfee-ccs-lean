module

public import DurfeeCCS.Step10.OuterFarNumerics
public import DurfeeCCS.Step10.OuterFarGaps
public import DurfeeCCS.Step07.PowerDecay
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! Bounds for the two endpoint branches and numerical sums of the competitors. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Set

theorem farTau_ge {n : ℕ} (hn : 6401 ≤ n) : (1.02 : ℝ) ≤ farTau n := by
  have h := farCube_lower (outerY_gt80 hn).le
  have hπ := DurfeeCCS.Step07.outerPi_lt
  have hh : 5 / (2 * outerY n ^ (1 / 3 : ℝ)) ≤ 5 / (2 * (4.308869 : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by gcongr)
  unfold farTau
  calc
    _ ≤ (24 / (3.14159265358980 : ℝ) ^ 2) * (1 - 5 / (2 * 4.308869)) := by norm_num
    _ ≤ _ := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_left₀ pi_pos.le hπ.le 2)
      · linarith
      · norm_num
      · positivity

theorem farRightTail_constant : (1.26 : ℝ) / (exp (16 / π ^ 2) - 1) < 0.311 := by
  have hπ := DurfeeCCS.Step07.outerPi_lt
  have hex : (1.621 : ℝ) ≤ 16 / π ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < π ^ 2)).mpr
    nlinarith [pow_le_pow_left₀ pi_pos.le hπ.le 2]
  have hpos : 0 < exp (16 / π ^ 2) - 1 := sub_pos.mpr (one_lt_exp_iff.mpr (by positivity))
  have h : (5.058 : ℝ) < exp 1.621 := by dyadic_interval +kernel [prec := 40]
  have hh := h.trans_le (exp_le_exp.mpr hex)
  apply (div_lt_iff₀ hpos).mpr
  linarith

theorem farMiddleTail_constant {τ : ℝ} (hτ : 1.02 ≤ τ) :
    (1.26 : ℝ) * exp (-τ) / (1 - exp (-3 * τ)) < 0.477 := by
  have hpos : 0 < 1 - exp (-3 * τ) :=
    sub_pos.mpr (exp_lt_one_iff.mpr (by linarith))
  have hex1 : exp (-τ) < (0.360595 : ℝ) :=
    (exp_le_exp.mpr (by linarith : -τ ≤ -1.02)).trans_lt (by dyadic_interval +kernel [prec := 40])
  have hex2 : exp (-3 * τ) < (0.046889 : ℝ) :=
    (exp_le_exp.mpr (by linarith : -3 * τ ≤ -3.06)).trans_lt (by dyadic_interval +kernel [prec := 40])
  apply (div_lt_iff₀ hpos).mpr
  linarith

private theorem farSmallParam_monotone (f a : ℝ) (hf : 12.5 ≤ f)
    (ha : a = sqrt (11 / 12) / f) (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) :
    MonotoneOn (fun x : ℝ => -(5 / 2) * log x - π * f / sqrt 3 * (1 - x) ^ 2)
      (Icc a (1 / 2)) := by
  let L := fun x : ℝ => -(5 / 2) * log x - π * f / sqrt 3 * (1 - x) ^ 2
  have hder (x : ℝ) (hx : 0 < x) : HasDerivAt L
      (-(5 / 2) / x + 2 * π * f / sqrt 3 * (1 - x)) x := by
    have h₁ := (hasDerivAt_log hx.ne').const_mul (-(5 / 2 : ℝ))
    have h₂ := (((hasDerivAt_id x).const_sub (1 : ℝ)).pow 2).const_mul (π * f / sqrt 3)
    convert h₁.sub h₂ using 1
    · rfl
    · simp only [id_eq]
      norm_num
      ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun x hx => (hder x (ha0.trans_le hx.1)).continuousAt.continuousWithinAt
  · exact fun x hx => (hder x (ha0.trans_le (interior_subset hx).1)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Icc a (1 / 2) := interior_subset hx
    have hx0 : 0 < x := ha0.trans_le hx'.1
    have hs : 0 < sqrt (3 : ℝ) := by positivity
    have hf0 : 0 < f := by linarith
    have hq : a * (1 - a) ≤ x * (1 - x) := by
      have hh := mul_nonneg (sub_nonneg.mpr hx'.1)
        (show 0 ≤ 1 - x - a by linarith [hx'.2])
      nlinarith
    have hsa : sqrt (11 / 12 : ℝ) < 0.958 :=
      (sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
    have hsa' : (0.957 : ℝ) < sqrt (11 / 12) :=
      (lt_sqrt (by norm_num)).mpr (by norm_num)
    have hab : a ≤ 0.07664 := by
      rw [ha]
      apply (div_le_iff₀ hf0).mpr
      linarith
    have hfa : f * a = sqrt (11 / 12) := by rw [ha]; field_simp
    have hπ := Real.pi_gt_d2
    have hs3 := farSqrtThree_bounds.2
    have hnum : (5 / 2 : ℝ) ≤ (2 * π / sqrt 3) * sqrt (11 / 12) * (1 - a) := by
      calc
        _ ≤ (2 * 3.14 / 1.73205081 : ℝ) * 0.957 * (1 - 0.07664) := by norm_num
        _ ≤ _ := by gcongr
    rw [(hder x hx0).deriv]
    have hbound := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2 * π * f / sqrt 3 by positivity)
    have hrewrite : 2 * π * f / sqrt 3 * (a * (1 - a)) =
        (2 * π / sqrt 3) * sqrt (11 / 12) * (1 - a) := by
      rw [← hfa]
      ring
    rw [hrewrite] at hbound
    have hprod := hnum.trans hbound
    apply (mul_le_mul_iff_left₀ hx0).mp
    · linarith [show (-(5 / 2) / x + 2 * π * f / sqrt 3 * (1 - x)) * x =
          -(5 / 2) + (2 * π * f / sqrt 3) * (x * (1 - x)) by field_simp]

theorem farSmallRadius_point {f g : ℝ} (hf : 12.5 ≤ f)
    (hg : sqrt (11 / 12) ≤ g) (hgf : g ≤ f / 2) :
    (2.6 / 0.875) * (f / g) ^ (5 / 2 : ℝ) *
        exp (-(π * f / sqrt 3) * (1 - g / f) ^ 2) <
      16.82 * exp (-(π * f / (4 * sqrt 3))) := by
  let a := sqrt (11 / 12) / f
  let x := g / f
  let L := fun x : ℝ => -(5 / 2) * log x - π * f / sqrt 3 * (1 - x) ^ 2
  have hf0 : 0 < f := by linarith
  have hg0 : 0 < g := (sqrt_pos.mpr (by norm_num : 0 < (11 / 12 : ℝ))).trans_le hg
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have hx0 : 0 < x := div_pos hg0 hf0
  have hax : a ≤ x := div_le_div_of_nonneg_right hg hf0.le
  have hx1 : x ≤ 1 / 2 := (div_le_iff₀ hf0).mpr (by linarith)
  have ha1 := hax.trans hx1
  have hmon := farSmallParam_monotone f a hf rfl ha0 ha1
  have hcomp : L x ≤ L (1 / 2) := hmon ⟨hax, hx1⟩ ⟨ha1, le_rfl⟩ hx1
  have he' : (f / g) ^ (5 / 2 : ℝ) * exp (-(π * f / sqrt 3) * (1 - x) ^ 2) ≤
      (2 : ℝ) ^ (5 / 2 : ℝ) * exp (-(π * f / (4 * sqrt 3))) := by
    rw [rpow_def_of_pos (div_pos hf0 hg0), rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      ← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    have hlog : log (f / g) = -log x := by
      rw [show f / g = x⁻¹ by dsimp [x]; rw [inv_div], log_inv]
    have hl2 : log (2 : ℝ) = -log (1 / 2 : ℝ) := by rw [one_div, log_inv, neg_neg]
    rw [hlog, hl2]
    dsimp only [L] at hcomp
    convert hcomp using 1 <;> ring
  have hconst : (2.6 / 0.875 : ℝ) * (2 : ℝ) ^ (5 / 2 : ℝ) < 16.82 := by
    linarith [mul_lt_mul_of_pos_left farTwoRpow52_lt (by norm_num : 0 < (2.6 / 0.875 : ℝ))]
  calc
    _ ≤ (2.6 / 0.875) * ((2 : ℝ) ^ (5 / 2 : ℝ) * exp (-(π * f / (4 * sqrt 3)))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left he' (by norm_num)
    _ < _ := by
      rw [← mul_assoc]
      exact mul_lt_mul_of_pos_right hconst (exp_pos _)

theorem farSmallTail_constant {y f j : ℝ} (hy : 80 ≤ y)
    (hf : 1.96 * y ≤ f ^ 2) (hf0 : 0 ≤ f) (hj : j ≤ 0.42 * y ^ (1 / 3 : ℝ)) :
    j * (16.82 * exp (-(π * f / (4 * sqrt 3)))) < 0.105 := by
  let w := y ^ (1 / 3 : ℝ)
  have hy0 : 0 ≤ y := by linarith
  have hw : 4.308869 ≤ w := farCube_lower hy
  have hw0 : 0 ≤ w := by linarith
  have hwc : w ^ 3 = y := farCube_eq hy0
  have hroot : (2.0757 : ℝ) ≤ sqrt w := le_sqrt_of_sq_le (by linarith)
  have hs := sq_sqrt hw0
  have hfg : 1.4 * w * sqrt w ≤ f := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h hf0 (by decide : 2 ≠ 0)
    rw [mul_pow, mul_pow, hs, show (1.4 : ℝ) ^ 2 * w ^ 2 * w = 1.96 * w ^ 3 by ring, hwc] at hh
    linarith
  have hπ := Real.pi_gt_d4
  have hs3 := farSqrtThree_bounds.2
  have hcoef : (1.3176 : ℝ) ≤ (π / (4 * sqrt 3)) * (1.4 * 2.0757) := by
    calc
      _ ≤ (3.1415 / (4 * 1.73205081) : ℝ) * (1.4 * 2.0757) := by norm_num
      _ ≤ _ := by gcongr
  have hbound : 1.3176 * w ≤ π * f / (4 * sqrt 3) := by
    calc
      _ ≤ (π / (4 * sqrt 3)) * (1.4 * 2.0757) * w := mul_le_mul_of_nonneg_right hcoef hw0
      _ = (π / (4 * sqrt 3)) * (1.4 * w * 2.0757) := by ring
      _ ≤ _ := by
        rw [show π * f / (4 * sqrt 3) = (π / (4 * sqrt 3)) * f by ring]
        exact mul_le_mul_of_nonneg_left ((by gcongr : 1.4 * w * (2.0757 : ℝ) ≤ 1.4 * w * sqrt w).trans hfg)
          (by positivity)
  have hmono := Step07.power_mul_exp_antitoneOn (x₀ := 4.308869) (a := 1.3176) (b := 0)
    1 1 (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
  have hm := hmono (show (4.308869 : ℝ) ∈ Ici 4.308869 from le_rfl) hw hw
  simp only [pow_one, add_zero] at hm
  have hex : exp (-(1.3176 : ℝ) * 4.308869) < 0.00344 := by
    dyadic_interval +kernel [prec := 40]
  calc
    _ ≤ (0.42 * w) * (16.82 * exp (-(π * f / (4 * sqrt 3)))) :=
      mul_le_mul_of_nonneg_right hj (by positivity)
    _ ≤ (0.42 * w) * (16.82 * exp (-1.3176 * w)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith))
        (by norm_num)) (by positivity)
    _ = (16.82 * 0.42) * (w * exp (-1.3176 * w)) := by ring
    _ ≤ (16.82 * 0.42) * (4.308869 * exp (-1.3176 * 4.308869)) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ < _ := by linarith

private theorem farSquare_decay {f : ℝ} (hf : 12.5 ≤ f) :
    f ^ (5 / 2 : ℝ) * exp (-1.35 * f) ≤ (12.5 : ℝ) ^ (5 / 2 : ℝ) * exp (-1.35 * 12.5) := by
  have hf0 : 0 ≤ f := by linarith
  have h := Step07.power_mul_exp_antitoneOn (x₀ := 12.5) (a := 2.7) (b := 0)
    5 1 (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (show (12.5 : ℝ) ∈ Ici 12.5 from le_rfl) hf hf
  simp only [pow_one, add_zero] at h
  by_contra! hb
  have hh := pow_lt_pow_left₀ hb
    (show 0 ≤ (12.5 : ℝ) ^ (5 / 2 : ℝ) * exp (-1.35 * 12.5) by positivity) (by decide : 2 ≠ 0)
  have hsq (x : ℝ) (hx : 0 ≤ x) :
      (x ^ (5 / 2 : ℝ) * exp (-1.35 * x)) ^ (2 : ℕ) = x ^ (5 : ℕ) * exp (-2.7 * x) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hx, ← Real.exp_nat_mul,
      show (5 / 2 : ℝ) * (2 : ℕ) = (5 : ℕ) by norm_num, rpow_natCast]
    congr 2
    norm_num
    ring
  rw [hsq _ (by norm_num), hsq _ hf0] at hh
  exact (not_lt_of_ge h) hh

theorem farSquare_cost {f : ℝ} (hf : 12.5 ≤ f) :
    (4 * (3 : ℝ) ^ (3 / 4 : ℝ) / 0.875) * f ^ (5 / 2 : ℝ) *
      exp (-(π * f / sqrt 3) + π / (6 * sqrt 3 * f)) <
      16.82 * exp (-(π * f / (4 * sqrt 3))) := by
  have hf0 : 0 < f := by linarith
  have hs := farSqrtThree_bounds.1
  have hs' := farSqrtThree_bounds.2
  have hπ := Real.pi_gt_d2
  have hπ' := Real.pi_lt_d2
  have h₁ : (1.35 : ℝ) ≤ 3 * π / (4 * sqrt 3) := by
    calc
      _ ≤ (3 * 3.14 / (4 * 1.73205081) : ℝ) := by norm_num
      _ ≤ _ := by gcongr
  have h₂ : π / (6 * sqrt 3 * f) ≤ (0.026 : ℝ) := by
    calc
      _ ≤ (3.15 / (6 * 1.73205080 * 12.5) : ℝ) := by gcongr
      _ ≤ _ := by norm_num
  have he : -3 * π * f / (4 * sqrt 3) + π / (6 * sqrt 3 * f) ≤ -1.35 * f + 0.026 := by
    have hmul := mul_le_mul_of_nonneg_right h₁ hf0.le
    rw [show -3 * π * f / (4 * sqrt 3) = -(3 * π / (4 * sqrt 3) * f) by ring]
    linarith
  have hb : (12.5 : ℝ) ^ (5 / 2 : ℝ) < 553 := by
    by_contra! h
    have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 553) h 4
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 12.5),
      show (5 / 2 : ℝ) * (4 : ℕ) = (10 : ℕ) by norm_num, rpow_natCast] at hc
    norm_num at hc
  have hex : exp (-1.35 * (12.5 : ℝ) + 0.026) < 1e-7 := by
    dyadic_interval +kernel [prec := 50]
  have hl : (4 * 3 ^ (3 / 4 : ℝ) / 0.875) *
      (f ^ (5 / 2 : ℝ) * exp (-3 * π * f / (4 * sqrt 3) + π / (6 * sqrt 3 * f))) < (16.82 : ℝ) := by
    apply lt_of_le_of_lt (b := (4 * 2.279508 / 0.875) * (553 * exp (-1.35 * 12.5 + 0.026)))
    · apply mul_le_mul
      · gcongr
        exact farThreeRpow34_lt.le
      · calc
          _ ≤ f ^ (5 / 2 : ℝ) * exp (-1.35 * f + 0.026) :=
            mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by positivity)
          _ = (f ^ (5 / 2 : ℝ) * exp (-1.35 * f)) * exp 0.026 := by rw [exp_add, mul_assoc]
          _ ≤ _ := by
            rw [exp_add, ← mul_assoc]
            exact mul_le_mul_of_nonneg_right
              ((farSquare_decay hf).trans (mul_le_mul_of_nonneg_right hb.le (exp_nonneg _))) (exp_nonneg _)
      · positivity
      · norm_num
    · linarith
  have heq : -(π * f / sqrt 3) + π / (6 * sqrt 3 * f) =
      (-3 * π * f / (4 * sqrt 3) + π / (6 * sqrt 3 * f)) + -(π * f / (4 * sqrt 3)) := by ring
  rw [heq, exp_add, ← mul_assoc, mul_assoc (4 * (3 : ℝ) ^ (3 / 4 : ℝ) / 0.875)]
  exact mul_lt_mul_of_pos_right hl (exp_pos _)
end DurfeeCCS.Step10
