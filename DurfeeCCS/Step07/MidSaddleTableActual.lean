module

public import DurfeeCCS.Step07.MidSaddleTable
public import DurfeeCCS.Step07.SaddleEndpoints
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The quadratic equation for the shifted square-root in the page 36 certificate. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open DurfeeCCS.Step06

/-- Real offset in the square of the complex phase wβ of page 35. -/
def modeRealOffset (t : ℝ) : ℝ :=
  Real.pi ^ 2 / 3 + (principalDilog (-(↑(Real.exp (-2 * t)) : ℂ))).re / 2

/-- Imaginary offset in wβ. -/
def modeImagOffset (t : ℝ) : ℝ :=
  -2 * (principalDilog (-(↑(Real.exp (-t)) : ℂ) * Complex.I)).im

def modeSquare (t c v β : ℝ) : ℂ :=
  ((t ^ 2 - β ^ 2 + c : ℝ) : ℂ) + ((2 * β * t + v : ℝ) : ℂ) * Complex.I

/-- The xβ of page 35, expressed using the real and imaginary offsets. -/
def modeShiftedSquare (t β : ℝ) : ℝ :=
  (modeSquare t (modeRealOffset t) (modeImagOffset t) β).sqrt.re ^ 2 - t ^ 2

private theorem modeSquare_re (t c v β : ℝ) :
    (modeSquare t c v β).re = t ^ 2 - β ^ 2 + c := by
  simp only [modeSquare, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]

private theorem modeSquare_im (t c v β : ℝ) :
    (modeSquare t c v β).im = 2 * β * t + v := by
  simp only [modeSquare, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

theorem modePolynomial_of_square {t c v β : ℝ} {s : ℂ}
    (hs : s ^ 2 = modeSquare t c v β) :
    modePolynomial t c v β (s.re ^ 2 - t ^ 2) = 0 := by
  have hre := congrArg Complex.re hs
  rw [pow_two, Complex.mul_re, ← pow_two, ← pow_two, modeSquare_re] at hre
  have him := congrArg Complex.im hs
  rw [pow_two, Complex.mul_im, modeSquare_im] at him
  have hi : s.re * s.im + s.im * s.re = 2 * β * t + v := by linarith only [him]
  have hi₂ := congrArg (fun x : ℝ => x ^ 2) hi
  unfold modePolynomial
  linear_combination s.re ^ 2 * hre + hi₂ / 4

theorem modePolynomial_of_shifted_square (t β : ℝ) :
    modePolynomial t (modeRealOffset t) (modeImagOffset t) β (modeShiftedSquare t β) = 0 :=
  modePolynomial_of_square (principalSqrt_sq _)

theorem modeSquare_base {t : ℝ} (ht : 0 ≤ t) :
    modeSquare t (modeRealOffset t) (modeImagOffset t) (Real.pi / 2) =
      saddlePhaseSquare (Real.exp t) := by
  apply Complex.ext
  · rw [modeSquare_re, phaseSquare_re_exp]
    unfold modeRealOffset
    ring
  · rw [modeSquare_im, phaseSquare_im_exp ht]
    unfold modeImagOffset
    ring

theorem modePolynomial_of_saddle {t : ℝ} (ht : 0 ≤ t) :
    modePolynomial t (modeRealOffset t) (modeImagOffset t) (Real.pi / 2)
      ((saddleS (Real.exp t)).re ^ 2 - t ^ 2) = 0 :=
  modePolynomial_of_square ((saddleS_sq _).trans (modeSquare_base ht).symm)

theorem modeRealOffset_bounds {t : ℝ} (ht : 0 ≤ t) :
    2.7 ≤ modeRealOffset t ∧ modeRealOffset t ≤ Real.pi ^ 2 / 3 := by
  have hE₁ : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd := dilog_neg_real_le_self (Real.exp_pos (-2 * t)).le hE₁
  have hd' := dilog_neg_real_re_nonpos (Real.exp_pos (-2 * t)).le hE₁
  have hp := pow_le_pow_left₀ (by norm_num : 0 ≤ (3.141592 : ℝ)) Real.pi_gt_d6.le 2
  unfold modeRealOffset
  constructor <;> linarith

theorem modeImagOffset_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ modeImagOffset t ∧ modeImagOffset t ≤ 2 * Real.exp (-t) := by
  have hE₁ : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd := dilog_negImag_le_self (Real.exp_pos (-t)).le hE₁
  have hd' := (saddlePhaseSquare_quadrant (Real.exp_pos (-t))).2
  unfold saddlePhaseSquare at hd'
  have hh : 0 < -2 * (principalDilog (-(↑(Real.exp (-t)) : ℂ) * Complex.I)).im := by
    simpa [Complex.mul_im] using hd'
  unfold modeImagOffset
  constructor <;> linarith

theorem modePolynomial_root_lt_offset {t c v β x : ℝ} (hc : 2.7 ≤ c) (hv : 0 ≤ v)
    (hv' : v ≤ 2) (htv : t * v ≤ 0.75) (hβ : 1.5 ≤ β)
    (hx : modePolynomial t c v β x = 0) : x < c := by
  have hb₀ : 0 ≤ β := by linarith
  have hβsq : 1.5 * β ≤ β ^ 2 := by nlinarith only [mul_nonneg hb₀ (sub_nonneg.mpr hβ)]
  have hmain : 2.7 * (1.5 * β) ≤ β ^ 2 * c := calc
    _ ≤ 2.7 * β ^ 2 := by gcongr
    _ ≤ _ := by rw [mul_comm]; gcongr
  have htv' : β * t * v ≤ β * 0.75 := by rw [mul_assoc]; gcongr
  have hv2 : v ^ 2 ≤ 4 := (pow_le_pow_left₀ hv hv' 2).trans (by norm_num)
  have hp : 0 < modePolynomial t c v β c := by
    unfold modePolynomial
    nlinarith only [hmain, htv', hv2, hβ]
  by_contra! hxc
  have hd : 0 ≤ x + t ^ 2 + β ^ 2 := by
    have hx' : 0 ≤ x := by linarith
    positivity
  have hg : 0 ≤ (x - c) * (x + t ^ 2 + β ^ 2) := mul_nonneg (sub_nonneg.mpr hxc) hd
  unfold modePolynomial at hp hx
  nlinarith only [hp, hx, hg]

theorem modeSquare_shift_nonneg {t c v β : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c)
    (hv : 0 ≤ v) (hβ : 0 ≤ β) :
    0 ≤ (modeSquare t c v β).sqrt.re ^ 2 - t ^ 2 := by
  let w := modeSquare t c v β
  let s := w.sqrt
  have hS : s ^ 2 = w := principalSqrt_sq _
  have hR := congrArg Complex.re hS
  rw [pow_two, Complex.mul_re, ← pow_two, ← pow_two] at hR
  have hN : ‖w‖ = s.re ^ 2 + s.im ^ 2 := by
    rw [← hS, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hW : t ^ 2 + β ^ 2 - c ≤ ‖w‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg w)
    rw [Complex.sq_norm, Complex.normSq_apply, modeSquare_re, modeSquare_im]
    nlinarith only [mul_nonneg (sq_nonneg t) hc,
      mul_nonneg (mul_nonneg hβ ht) hv, sq_nonneg v]
  change 0 ≤ s.re ^ 2 - t ^ 2
  rw [hN] at hW
  have hre : w.re = t ^ 2 - β ^ 2 + c := modeSquare_re t c v β
  linarith [hR, hW, hre]

/-- Page 36 phase loss for the actual square roots, given the endpoint enclosures
on the chosen logarithm interval. -/
theorem modeGap_of_endpoint_enclosures (wide : Bool) (i : Fin 5) {t β : ℝ}
    (htₗ : (i.val : ℝ) ≤ t) (htᵤ : t ≤ (i.val : ℝ) + 1)
    (haᵤ : (saddleS (Real.exp t)).re ≤ modeUpperAmplitude i)
    (hDₗ : modeLowerGap i ≤ (saddleS (Real.exp t)).re ^ 2 - t ^ 2)
    (hβ : modeMultiplier wide * Real.pi / 2 ≤ β) :
    modeGapTarget wide i <
      ((saddleS (Real.exp t)).re ^ 2 - t ^ 2 - modeShiftedSquare t β) /
        (saddleS (Real.exp t)).re := by
  let c := modeRealOffset t
  let v := modeImagOffset t
  have ht : 0 ≤ t := (Nat.cast_nonneg _).trans htₗ
  have hc := modeRealOffset_bounds ht
  have hv := modeImagOffset_bounds ht
  have hv' : v ≤ 2 := by
    have hh := Real.exp_le_one_iff.mpr (show -t ≤ 0 by linarith)
    exact hv.2.trans (by linarith only [hh])
  have htv : t * v ≤ 0.75 := by
    have hh := mul_le_mul_of_nonneg_left hv.2 ht
    have hcor : t * v ≤ modeImagCorrection t := by unfold modeImagCorrection; linarith
    have hb := modeImagCorrection_bound (0 : Fin 5) (t := t) (by simpa using ht)
    change modeImagCorrection t < 0.736 at hb
    linarith
  have hm : 3 ≤ modeMultiplier wide := by cases wide <;> norm_num [modeMultiplier]
  have hβ' : 1.5 ≤ β := by
    have hb : 3 * Real.pi / 2 ≤ modeMultiplier wide * Real.pi / 2 := by gcongr
    linarith [Real.pi_gt_d6]
  have ha := (saddleS_components (Real.exp_pos t)).1.trans (saddleS_components (Real.exp_pos t)).2
  have hx := modePolynomial_of_shifted_square t β
  have hD := modePolynomial_of_saddle ht
  have hDᵤ := modePolynomial_root_lt_offset hc.1 hv.1 hv' htv (by linarith [Real.pi_gt_d6]) hD
  have hxᵤ := modePolynomial_root_lt_offset hc.1 hv.1 hv' htv hβ' hx
  have hxₗ := modeSquare_shift_nonneg ht (show 0 ≤ c by linarith [hc.1]) hv.1
      (show 0 ≤ β by linarith)
  exact modeGap_at_parameters wide i htₗ htᵤ ha haᵤ hc.2 hv.1 hv.2 hDₗ hDᵤ.le hxₗ hxᵤ.le hβ hx hD

end DurfeeCCS.Step07
