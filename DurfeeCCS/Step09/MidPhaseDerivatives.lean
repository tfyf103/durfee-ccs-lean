module

public import DurfeeCCS.Step09.MidPhaseSymmetry
public import DurfeeCCS.Step08.MidpointRectangle

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Differentiating the complex angular phase gives the real curvature bound. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex Set DurfeeCCS.Step06 DurfeeCCS.Step08

def midSaddleSeed (t ε : ℝ) (z : ℂ) : ℂ :=
  -(t : ℂ) * I * exp (z * ((ε : ℂ) * I))

def midSaddleGComplex (t : ℝ) (z : ℂ) : ℂ :=
  -principalDilog (midSaddleSeed t 1 z) - principalDilog (midSaddleSeed t (-1) z)

def midSaddleGDerivative (t : ℝ) (z : ℂ) : ℂ :=
  log (1 - midSaddleSeed t 1 z) * I - log (1 - midSaddleSeed t (-1) z) * I

def midSaddleGSecond (t : ℝ) (z : ℂ) : ℂ :=
  midSaddleSeed t 1 z / (1 - midSaddleSeed t 1 z) +
    midSaddleSeed t (-1) z / (1 - midSaddleSeed t (-1) z)

theorem midSaddleGComplex_ofReal (t θ : ℝ) : midSaddleGComplex t θ = saddleG t θ := by
  unfold midSaddleGComplex midSaddleSeed saddleG
  norm_num

private theorem hasDerivAt_midSaddleSeed (t ε : ℝ) (z : ℂ) :
    HasDerivAt (midSaddleSeed t ε)
      (midSaddleSeed t ε z * ((ε : ℂ) * I)) z := by
  unfold midSaddleSeed
  simpa only [id_eq, mul_assoc, one_mul] using
    (((hasDerivAt_id z).mul_const ((ε : ℂ) * I)).cexp.const_mul (-(t : ℂ) * I))

private theorem midSaddleSeed_ne_zero {t : ℝ} (ht : t ≠ 0) (ε : ℝ) (z : ℂ) :
    midSaddleSeed t ε z ≠ 0 :=
  mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr ht)) I_ne_zero) (exp_ne_zero _)

private theorem midSaddleSeed_ofReal_re_lt_one {t : ℝ} (ht : |t| < 1) (ε x : ℝ) :
    (midSaddleSeed t ε (x : ℂ)).re < 1 := by
  have hh : ‖midSaddleSeed t ε (x : ℂ)‖ = |t| := by
    rw [midSaddleSeed, norm_mul, norm_mul, norm_neg, norm_I, mul_one,
      show (x : ℂ) * ((ε : ℂ) * I) = ((x * ε : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.re_le_norm _).trans_lt (hh ▸ ht)

private theorem hasDerivAt_dilog_midSaddleSeed {t ε : ℝ} {z : ℂ} (ht : t ≠ 0)
    (hz : (midSaddleSeed t ε z).re < 1) :
    HasDerivAt (fun w => principalDilog (midSaddleSeed t ε w))
      (-log (1 - midSaddleSeed t ε z) * ((ε : ℂ) * I)) z := by
  have hc := (hasDerivAt_principalDilog (mem_dilogCut_iff.mpr (Or.inl hz))).comp z
    (hasDerivAt_midSaddleSeed t ε z)
  rw [ite_eq_right (midSaddleSeed_ne_zero ht ε z)] at hc
  rw [← mul_assoc, div_mul_cancel₀ _ (midSaddleSeed_ne_zero ht ε z)] at hc
  exact hc

theorem hasDerivAt_midSaddleGComplex {t : ℝ} {z : ℂ} (ht : t ≠ 0)
    (hp : (midSaddleSeed t 1 z).re < 1) (hm : (midSaddleSeed t (-1) z).re < 1) :
    HasDerivAt (midSaddleGComplex t) (midSaddleGDerivative t z) z := by
  unfold midSaddleGComplex midSaddleGDerivative
  convert ((hasDerivAt_dilog_midSaddleSeed ht hp).neg.sub
    (hasDerivAt_dilog_midSaddleSeed ht hm)) using 1
  push_cast
  ring

theorem hasDerivAt_midSaddleGDerivative {t : ℝ} {z : ℂ}
    (hp : (midSaddleSeed t 1 z).re < 1) (hm : (midSaddleSeed t (-1) z).re < 1) :
    HasDerivAt (midSaddleGDerivative t) (midSaddleGSecond t z) z := by
  have hs {ε : ℝ} (h : (midSaddleSeed t ε z).re < 1) :
      1 - midSaddleSeed t ε z ∈ slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using sub_pos.mpr h
  have hd {ε : ℝ} (h : (midSaddleSeed t ε z).re < 1) :
      HasDerivAt (fun w => log (1 - midSaddleSeed t ε w) * I)
        (-(midSaddleSeed t ε z * ((ε : ℂ) * I)) /
          (1 - midSaddleSeed t ε z) * I) z := by
    exact (((hasDerivAt_midSaddleSeed t ε z).const_sub 1).clog (hs h)).mul_const I
  unfold midSaddleGDerivative midSaddleGSecond
  convert (hd hp).sub (hd hm) using 1
  push_cast
  simp only [one_mul]
  field_simp [(Complex.slitPlane_ne_zero (hs hp)), (Complex.slitPlane_ne_zero (hs hm))]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem midSaddleSeed_ofReal_norm {t : ℝ} (ε x : ℝ) :
    ‖midSaddleSeed t ε (x : ℂ)‖ = |t| := by
  rw [midSaddleSeed, norm_mul, norm_mul, norm_neg, norm_I, mul_one,
    show (x : ℂ) * ((ε : ℂ) * I) = ((x * ε : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem midSaddleGSecond_eq_ratio {t : ℝ} (ht : |t| < 1) (x : ℝ) :
    midSaddleGSecond t x =
      (2 * (t : ℂ) ^ 2 - 2 * (t : ℂ) * I * (Real.cos x : ℂ)) /
        (1 - (t : ℂ) ^ 2 + 2 * (t : ℂ) * I * (Real.cos x : ℂ)) := by
  let p := midSaddleSeed t 1 (x : ℂ)
  let m := midSaddleSeed t (-1) (x : ℂ)
  have hp : (1 - p) ≠ 0 := by
    intro h
    have h₁ := congrArg Complex.re (sub_eq_zero.mp h).symm
    exact (midSaddleSeed_ofReal_re_lt_one ht 1 x).ne (h₁.trans Complex.one_re)
  have hm : (1 - m) ≠ 0 := by
    intro h
    have h₁ := congrArg Complex.re (sub_eq_zero.mp h).symm
    exact (midSaddleSeed_ofReal_re_lt_one ht (-1) x).ne (h₁.trans Complex.one_re)
  have hpm : p * m = -(t : ℂ) ^ 2 := by
    dsimp only [p,m,midSaddleSeed]
    have he : exp ((x : ℂ) * ((1 : ℝ) * I)) * exp ((x : ℂ) * ((-1 : ℝ) * I)) = 1 := by
      rw [← exp_add, show (x : ℂ) * ((1 : ℝ) * I) + (x : ℂ) * ((-1 : ℝ) * I) = 0 by push_cast; ring, exp_zero]
    calc
      _ = ((-(t : ℂ) * I) ^ 2) *
          (exp ((x : ℂ) * ((1 : ℝ) * I)) * exp ((x : ℂ) * ((-1 : ℝ) * I))) := by ring
      _ = _ := by rw [he, mul_one, mul_pow, neg_sq, Complex.I_sq]; ring
  have hadd : p + m = -2 * (t : ℂ) * I * (Real.cos x : ℂ) := by
    dsimp only [p,m,midSaddleSeed]
    have h₁ : (x : ℂ) * ((1 : ℝ) * I) = (x : ℂ) * I := by norm_num
    have h₂ : (x : ℂ) * ((-1 : ℝ) * I) = -(x : ℂ) * I := by norm_num
    rw [h₁,h₂, Complex.ofReal_cos, Complex.cos]
    ring
  have hden : (1-p)*(1-m) = 1 - (t : ℂ) ^ 2 + 2*(t : ℂ)*I*(Real.cos x : ℂ) := by
    calc
      _ = 1 - (p+m) + p*m := by ring
      _ = _ := by rw [hadd,hpm]; ring
  change p/(1-p) + m/(1-m) = _
  have hsum : p/(1-p) + m/(1-m) = (p*(1-m) + m*(1-p))/((1-p)*(1-m)) := by
    field_simp
  rw [hsum, hden]
  congr 1
  calc
    p * (1-m) + m * (1-p) = (p+m) - 2*(p*m) := by ring
    _ = _ := by rw [hadd,hpm]; ring

theorem midSaddleGSecond_re_lower {t : ℝ} (ht : |t| < 1) (x : ℝ) :
    -2 * t ^ 2 / (1+t^2) ≤ (midSaddleGSecond t x).re := by
  rw [midSaddleGSecond_eq_ratio ht]
  let c := Real.cos x
  have ht' : t^2 < 1 := by
    have h : 0 < 1+t := by linarith only [(abs_lt.mp ht).1]
    nlinarith only [mul_pos (sub_pos.mpr (abs_lt.mp ht).2) h]
  have hden : 0 < (1-t^2)^2 + (2*t*c)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (sub_pos.mpr ht')) (sq_nonneg _)
  have hc : 0 ≤ 1-c^2 := by
    dsimp [c]
    nlinarith only [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x)]
  have hid : ((2 * (t : ℂ)^2 - 2 * (t : ℂ)*I*(c : ℂ)) /
    (1-(t : ℂ)^2+2*(t : ℂ)*I*(c : ℂ))).re =
      2 * t^2 * (1-t^2 - 2*c^2) / ((1-t^2)^2 + (2*t*c)^2) := by
    rw [Complex.div_re]
    simp only [← Complex.ofReal_pow, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      mul_one, zero_add, add_zero, sub_zero, zero_sub]
    norm_num
    ring
  change _ ≤ ((2 * (t : ℂ)^2 - 2 * (t : ℂ)*I*(c : ℂ)) /
    (1-(t : ℂ)^2+2*(t : ℂ)*I*(c : ℂ))).re
  rw [hid, div_le_div_iff₀ (by positivity) hden]
  have hp : 0 ≤ 4*t^2*(1-t^2)*(1-c^2) := by positivity
  linear_combination hp

private theorem saddleG_re_lower_open {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) (x : ℝ) :
    (saddleG t 0).re - t^2/(1+t^2)*x^2 ≤ (saddleG t x).re := by
  let C := t^2/(1+t^2)
  let F (x : ℝ) := (saddleG t x).re + C*x^2
  let D (x : ℝ) := (midSaddleGDerivative t (x : ℂ)).re + 2*C*x
  have habs : |t| < 1 := by rwa [abs_of_pos ht]
  have hp (x : ℝ) := midSaddleSeed_ofReal_re_lt_one habs 1 x
  have hm (x : ℝ) := midSaddleSeed_ofReal_re_lt_one habs (-1) x
  have dF (x : ℝ) : HasDerivAt F (D x) x := by
    have h := (hasDerivAt_midSaddleGComplex ht.ne' (hp x) (hm x)).real_of_complex
    simp only [midSaddleGComplex_ofReal] at h
    convert h.add (((hasDerivAt_id x).pow 2).const_mul C) using 1
    · rfl
    · dsimp [D]
      ring
  have dD (x : ℝ) : HasDerivAt D ((midSaddleGSecond t (x : ℂ)).re + 2*C) x := by
    have h := (hasDerivAt_midSaddleGDerivative (hp x) (hm x)).real_of_complex
    convert h.add ((hasDerivAt_id x).const_mul (2*C)) using 1
    · rfl
    · ring
  have D0 : D 0 = 0 := by simp [D, midSaddleGDerivative, midSaddleSeed]
  have hD : Monotone D := monotone_of_deriv_nonneg (fun x => (dD x).differentiableAt) (fun x => by
    rw [(dD x).deriv]
    have h := midSaddleGSecond_re_lower habs x
    change 0 ≤ (midSaddleGSecond t (x : ℂ)).re + 2*(t^2/(1+t^2))
    have ht' : -2 * (t ^ 2 / (1 + t ^ 2)) ≤ (midSaddleGSecond t (x : ℂ)).re := by
      convert h using 1
      ring
    linarith only [ht'])
  have hF : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun x _ => (dF x).continuousAt.continuousWithinAt)
      (fun x _ => (dF x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(dF x).deriv, ← D0]
    exact hD (interior_subset hx)
  have h := hF (show (0:ℝ) ∈ Ici 0 from le_rfl) (abs_nonneg x) (abs_nonneg x)
  have he : saddleG t |x| = saddleG t x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx), saddleG_even t x]
  dsimp [F] at h
  rw [he,sq_abs,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at h
  linarith only [h]

theorem saddleG_re_lower {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (x : ℝ) :
    (saddleG t 0).re - t^2/(1+t^2)*x^2 ≤ (saddleG t x).re := by
  have hmem : t ∈ Icc (0 : ℝ) 1 := ⟨ht.le,ht₁⟩
  let f (q : ℝ) := (saddleG q 0).re - q^2/(1+q^2)*x^2
  let g (q : ℝ) := (saddleG q x).re
  have hf : ContinuousOn f (Icc 0 1) := by
    have h := Complex.continuous_re.comp_continuousOn (continuousOn_saddleG_radius 0)
    have hc : Continuous (fun q : ℝ => q^2/(1+q^2)*x^2) := by
      apply Continuous.mul_const
      exact (continuous_id.pow 2).div (continuous_const.add (continuous_id.pow 2))
        (fun q => by dsimp; positivity)
    exact h.sub hc.continuousOn
  have hg : ContinuousOn g (Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_saddleG_radius x)
  have hcl : t ∈ closure (Ioo (0 : ℝ) 1) := by
    rwa [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  exact ContinuousWithinAt.closure_le hcl ((hf t hmem).mono Ioo_subset_Icc_self)
    ((hg t hmem).mono Ioo_subset_Icc_self) (fun q hq => saddleG_re_lower_open hq.1 hq.2 x)

end DurfeeCCS.Step09
