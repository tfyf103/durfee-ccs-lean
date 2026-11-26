module

public import DurfeeCCS.Step09.MidPhase
public import DurfeeCCS.Step07.MidSaddleTableConnections
public import DurfeeCCS.Step08.PhaseGap
public import DurfeeCCS.Step08.SaddleBesselAverage

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Phase estimates supporting the Gaussian bounds for the other modes. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

theorem midRe_exponent {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (η : ℝ) (z : ℂ) :
    ((n : ℂ) * midEtaPoint n r η + z / midEtaPoint n r η).re =
      midOmega n r + (Real.sqrt n / (saddleS r).re) * ((z.re + η * z.im) / (1 + η ^ 2)) := by
  have hu := saddleU_pos hn hr
  have hre : ((n : ℂ) * midEtaPoint n r η).re = midOmega n r := by
    simp [Complex.mul_re, saddleU_mul_n hn r]
  rw [Complex.add_re, hre, Complex.div_re, Complex.normSq_apply, midEtaPoint_re, midEtaPoint_im]
  have ha : 0 < (saddleS r).re := (saddleS_components hr).1.trans (saddleS_components hr).2
  have hx : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hD : 0 < 1 + η ^ 2 := by positivity
  rw [show (saddleU n r * saddleU n r + saddleU n r * η * (saddleU n r * η)) =
    (saddleU n r) ^ 2 * (1 + η ^ 2) by ring]
  simp only [midU, saddleU]
  field_simp

private theorem mid_cauchy_angle_le {r η χ : ℝ} (hr : 1 ≤ r) (hη : |η| ≤ 8) :
    χ ^ 2 / 130 ≤ (χ ^ 2 / (1 + r⁻¹ ^ 2)) / (1 + η ^ 2) := by
  have hη' : η ^ 2 ≤ 64 := by
    have h := pow_le_pow_left₀ (abs_nonneg η) hη 2
    simpa only [sq_abs, show (8 : ℝ) ^ 2 = 64 by norm_num] using h
  have hr' : r⁻¹ ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ r⁻¹) (inv_le_one_of_one_le₀ hr) 2
    simpa only [one_pow] using h
  rw [div_div]
  refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
  have hR : 1 + r⁻¹ ^ 2 ≤ (1 + 1 : ℝ) := add_le_add_right hr' 1
  have hI : 1 + η ^ 2 ≤ (1 + 64 : ℝ) := add_le_add_right hη' 1
  calc
    _ ≤ (1 + 1) * (1 + 64) := mul_le_mul hR hI (by positivity) (by norm_num)
    _ = _ := by norm_num

theorem midRe_exponent_le_modeGap {n : ℕ} (hn : 0 < n) {r η χ : ℝ}
    (hr : 1 ≤ r) (hη : |η| ≤ 8) {z w : ℂ}
    (hRe : z.re ≤ w.re - χ ^ 2 / (1 + r⁻¹ ^ 2)) (hIm : |z.im| ≤ w.im) :
    ((n : ℂ) * midEtaPoint n r η + z / midEtaPoint n r η).re ≤
      2 * midOmega n r -
        (Real.sqrt n / (saddleS r).re) * ((saddleS r).re ^ 2 - w.sqrt.re ^ 2) -
        Real.sqrt n * χ ^ 2 / (130 * (saddleS r).re) := by
  have hr' : 0 < r := by linarith
  have ha : 0 < (saddleS r).re := (saddleS_components hr').1.trans (saddleS_components hr').2
  let c := Real.sqrt (n : ℝ) / (saddleS r).re
  have hC : 0 ≤ c := by unfold c; positivity
  have hD : 0 < 1 + η ^ 2 := by positivity
  have hI : η * z.im ≤ |η| * w.im := by
    calc
      _ ≤ |η * z.im| := le_abs_self _
      _ = |η| * |z.im| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hIm (abs_nonneg _)
  have hw := square_eta_gap w.sqrt |η|
  rw [principalSqrt_sq, sq_abs] at hw
  have hW : (w.re + |η| * w.im) / (1 + η ^ 2) ≤ w.sqrt.re ^ 2 :=
    sub_nonneg.mp (by rw [hw]; positivity)
  have hR := div_le_div_of_nonneg_right (add_le_add hRe hI) hD.le
  have hG := mid_cauchy_angle_le hr hη (χ := χ)
  have hG' : (z.re + η * z.im) / (1 + η ^ 2) ≤ w.sqrt.re ^ 2 - χ ^ 2 / 130 := by
    rw [show w.re - χ ^ 2 / (1 + r⁻¹ ^ 2) + |η| * w.im =
      w.re + |η| * w.im - χ ^ 2 / (1 + r⁻¹ ^ 2) by ring, sub_div] at hR
    linarith only [hR, hG, hW]
  have hm := mul_le_mul_of_nonneg_left hG' hC
  have hz : c * (saddleS r).re ^ 2 = midOmega n r := by
    unfold c midOmega saddleOmega
    field_simp
  rw [midRe_exponent hn hr']
  change midOmega n r + c * _ ≤ 2 * midOmega n r - c * _ - _
  have hGaussian : c * (χ ^ 2 / 130) = Real.sqrt n * χ ^ 2 / (130 * (saddleS r).re) := by
    unfold c
    ring
  nlinarith only [hm, hz, hGaussian]

/-- On the side opposite the saddle, a nonpositive angular imaginary term
forces the full loss `b²/a`. -/
theorem midRe_exponent_opposite_sign {n : ℕ} (hn : 0 < n) {r η χ : ℝ}
    (hr : 1 ≤ r) (hη : |η| ≤ 8) {z : ℂ}
    (hRe : z.re ≤ ((saddleS r) ^ 2).re - χ ^ 2 / (1 + r⁻¹ ^ 2))
    (hIm : η * z.im ≤ 0) :
    ((n : ℂ) * midEtaPoint n r η + z / midEtaPoint n r η).re ≤
      2 * midOmega n r - Real.sqrt n * (saddleS r).im ^ 2 / (saddleS r).re -
      Real.sqrt n * χ ^ 2 / (130 * (saddleS r).re) := by
  let a := (saddleS r).re
  let b := (saddleS r).im
  let x := Real.sqrt (n : ℝ)
  have hr' : 0 < r := by linarith
  have ha : 0 < a := (saddleS_components hr').1.trans (saddleS_components hr').2
  have hReS : ((saddleS r) ^ 2).re = a ^ 2 - b ^ 2 := by simp [a,b,pow_two,Complex.mul_re]
  have hRe0 : 0 < ((saddleS r) ^ 2).re := by
    rw [saddleS_sq]
    exact (saddlePhaseSquare_quadrant hr').1
  have hD : 0 < 1 + η ^ 2 := by positivity
  have h := div_le_div_of_nonneg_right (show z.re + η * z.im ≤
    ((saddleS r) ^ 2).re - χ ^ 2 / (1 + r⁻¹ ^ 2) by linarith only [hRe, hIm]) hD.le
  rw [sub_div] at h
  have hC := mid_cauchy_angle_le hr hη (χ := χ)
  have hBase : ((saddleS r) ^ 2).re / (1 + η ^ 2) ≤ ((saddleS r) ^ 2).re := by
    exact div_le_self hRe0.le (by linarith [sq_nonneg η])
  have hbound : (z.re + η * z.im) / (1 + η ^ 2) ≤ a ^ 2 - b ^ 2 - χ ^ 2 / 130 := by
    linarith only [h,hC,hBase,hReS]
  have hmul := mul_le_mul_of_nonneg_left hbound (show 0 ≤ x / a by positivity)
  rw [midRe_exponent hn hr']
  change a*x + x/a * _ ≤ 2*(a*x) - x*b^2/a - x*χ^2/(130*a)
  calc
    _ ≤ a*x + x/a * (a^2 - b^2 - χ^2/130) := add_le_add_right hmul _
    _ = _ := by field_simp; ring

/-- The complement of the central angular interval on the opposite saddle half. -/
theorem midRe_exponent_opposite_shifted {n : ℕ} (hn : 0 < n) {r η χ : ℝ}
    (hr : 1 ≤ r) (hη₀ : 0 ≤ η) (hη₁ : |η| ≤ 8) (hχ : Real.pi / 2 < |χ|) {z : ℂ}
    (hRe : z.re ≤ ((saddleS r) ^ 2).re - χ ^ 2 / (1 + r⁻¹ ^ 2))
    (hIm : z.im ≤ ((saddleS r) ^ 2).im) :
    ((n : ℂ) * midEtaPoint n r η + z / midEtaPoint n r η).re ≤
      2 * midOmega n r -
        Real.sqrt n * oppositeHalfLogPhaseLoss (Real.log r) (η - midSlope r) -
        Real.sqrt n * (|χ| - Real.pi / 2) ^ 2 / (130 * (saddleS r).re) := by
  have hr' : 0 < r := by linarith
  let a := (saddleS r).re
  let ρ := midSlope r
  let t := η - ρ
  let d := |χ| - Real.pi / 2
  let D := Real.sqrt (n : ℝ) / a
  have ha : 0 < a := (saddleS_components hr').1.trans (saddleS_components hr').2
  have hD : 0 ≤ D := by unfold D; positivity
  have hx : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hD₀ : 0 < 1 + η ^ 2 := by positivity
  have hηsq : 1 + η ^ 2 ≤ 1 + 2 * ρ ^ 2 + 2 * t ^ 2 := by
    unfold t
    nlinarith only [sq_nonneg (η - 2 * ρ)]
  have hχsq : Real.pi ^ 2 / 4 + d ^ 2 ≤ χ ^ 2 := by
    unfold d
    nlinarith only [mul_nonneg (sub_nonneg.mpr hχ.le) Real.pi_pos.le, sq_abs χ]
  have hχD : Real.pi ^ 2 / (4 * (1 + r⁻¹ ^ 2)) + d ^ 2 / (1 + r⁻¹ ^ 2) ≤
      χ ^ 2 / (1 + r⁻¹ ^ 2) := by
    rw [show Real.pi ^ 2 / (4 * (1 + r⁻¹ ^ 2)) = (Real.pi ^ 2 / 4) / (1 + r⁻¹ ^ 2) by field_simp, ← add_div]
    exact div_le_div_of_nonneg_right hχsq (by positivity)
  have haxis : ((saddleS r ^ 2).re + η * (saddleS r ^ 2).im) / (1 + η ^ 2) =
      a ^ 2 - a ^ 2 * t ^ 2 / (1 + η ^ 2) := by
    have h := square_eta_gap (saddleS r) η
    have ht : a * t = (saddleS r).re * η - (saddleS r).im := by
      unfold t ρ a midSlope
      field_simp [show (saddleS r).re ≠ 0 from ha.ne']
      <;> ring
    rw [← ht, mul_pow] at h
    linarith only [h]
  have H : (z.re + η * z.im) / (1 + η ^ 2) ≤
      a ^ 2 - (a ^ 2 * t ^ 2 + Real.pi ^ 2 / (4 * (1 + r⁻¹ ^ 2))) / (1 + η ^ 2) -
      (d ^ 2 / (1 + r⁻¹ ^ 2)) / (1 + η ^ 2) := by
    have hi := mul_le_mul_of_nonneg_left hIm hη₀
    have hh : z.re + η*z.im ≤ ((saddleS r)^2).re + η*((saddleS r)^2).im -
        Real.pi ^ 2 / (4 * (1 + r⁻¹ ^ 2)) - d ^ 2 / (1 + r⁻¹ ^ 2) := by
      linarith only [hi,hRe,hχD]
    have hh' := div_le_div_of_nonneg_right hh hD₀.le
    rw [sub_div, sub_div, haxis] at hh'
    simp only [add_div] at hh' ⊢
    linarith only [hh']
  have hG := mid_cauchy_angle_le hr hη₁ (χ := d)
  have hm : (a ^ 2 * t ^ 2 + Real.pi ^ 2 / (4 * (1 + r⁻¹ ^ 2))) / (1 + 2*ρ^2 + 2*t^2) ≤
      (a ^ 2 * t ^ 2 + Real.pi ^ 2 / (4 * (1 + r⁻¹ ^ 2))) / (1 + η ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) hD₀ hηsq
  have hfrac : 1 / (1 + r⁻¹ ^ 2) = r ^ 2 / (1 + r ^ 2) := by
    field_simp
    ring
  have hLoss : Real.sqrt n * oppositeHalfLogPhaseLoss (Real.log r) t =
      D * ((a ^ 2 * t ^ 2 + Real.pi ^ 2 / (4 * (1 + r⁻¹ ^ 2))) / (1 + 2*ρ^2 + 2*t^2)) := by
    unfold oppositeHalfLogPhaseLoss
    dsimp only
    rw [Real.exp_log hr']
    change Real.sqrt n * ((a ^ 2 * t ^ 2 + r ^ 2 / (1 + r ^ 2) * Real.pi ^ 2 / 4) /
      (a * (1 + 2*ρ^2 + 2*t^2))) = _
    rw [← hfrac]
    unfold D
    field_simp
  have hbound := mul_le_mul_of_nonneg_left (show (z.re + η * z.im) / (1 + η ^ 2) ≤
    a ^ 2 - (a ^ 2 * t ^ 2 + Real.pi ^ 2 / (4 * (1 + r⁻¹ ^ 2))) / (1 + 2*ρ^2 + 2*t^2) -
      d ^ 2 / 130 by linarith only [H,hm,hG]) hD
  rw [midRe_exponent hn hr', hLoss]
  change a * Real.sqrt n + D * _ ≤ 2*(a*Real.sqrt n) - D * _ - Real.sqrt n*d^2/(130*a)
  calc
    _ ≤ a * Real.sqrt n + D *
      (a ^ 2 - (a ^ 2 * t ^ 2 + Real.pi ^ 2 / (4 * (1 + r⁻¹ ^ 2))) / (1 + 2*ρ^2 + 2*t^2) -
        d ^ 2/130) := add_le_add_right hbound _
    _ = _ := by unfold D; field_simp; ring

theorem mid_log_lt_saddleRe {r : ℝ} (hr : 1 ≤ r) : Real.log r < (saddleS r).re := by
  have ht : 0 ≤ Real.log r := Real.log_nonneg hr
  have h0 := saddle_at_one_sq_lower
  have hm := minorArcSaddleGap_mono (show (0 : ℝ) ∈ Ici 0 from le_rfl) ht ht
  dsimp [minorArcSaddleGap] at hm
  rw [Real.exp_zero, Real.exp_log (by linarith : 0 < r)] at hm
  by_contra! h
  have ha : 0 ≤ (saddleS r).re := ((saddleS_components (by linarith : 0 < r)).1.trans
    (saddleS_components (by linarith : 0 < r)).2).le
  have hp := pow_le_pow_left₀ ha h 2
  nlinarith only [hp, hm, h0]

private theorem mid_proj_angle_le_norm (z : ℂ) (η : ℝ) :
    (z.re + η * z.im) / (1 + η ^ 2) ≤ ‖z‖ := by
  let w := verticalPoint 1 η
  have hW : 1 ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    simpa [w] using h
  have hZ : (z / w).re = (z.re + η * z.im) / (1 + η ^ 2) := by
    rw [Complex.div_re, Complex.normSq_apply]
    simp [w, pow_two, add_div, mul_comm]
  rw [← hZ]
  exact (Complex.re_le_norm _).trans (by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hW)

/-- The Gaussian phase loss for the frequencies `|π(p+1/2)|>40a`. -/
theorem midRe_exponent_far_mode {n : ℕ} (hn : 0 < n) {r η χ : ℝ} {p : ℤ}
    (hr : 1 ≤ r) (ha₁ : 1 ≤ (saddleS r).re)
    (hη : |η| ≤ 8) (hp : 40 * (saddleS r).re < |midFrequency p|) :
    ((n : ℂ) * midEtaPoint n r η + midPhase r p χ / midEtaPoint n r η).re ≤
      2 * midOmega n r -
        Real.sqrt n * (midFrequency p) ^ 2 / (200 * (saddleS r).re) -
        Real.sqrt n * χ ^ 2 / (130 * (saddleS r).re) := by
  let z := midPhase r p χ
  let a := (saddleS r).re
  let t := Real.log r
  let f := midFrequency p
  let z₁ : ℂ := (Real.pi : ℂ) ^ 2 / 3 - saddleG (midModeRadius r p) χ
  have hr' : 0 < r := by linarith
  have ha : 0 < a := by linarith
  have ht : 0 ≤ t := Real.log_nonneg hr
  have hta : t ≤ a := (mid_log_lt_saddleRe hr).le
  have hD : 0 < 1 + η ^ 2 := by positivity
  have hD65 : 1 + η ^ 2 ≤ 65 := by
    have h := pow_le_pow_left₀ (abs_nonneg η) hη 2
    rw [sq_abs] at h
    linarith only [h]
  have hf : 0 ≤ |f| := abs_nonneg _
  have hηt : |η*t| ≤ 8*a := by
    rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul hη hta ht (by norm_num)
  have hdist : 0.8 * |f| ≤ |f - η*t| := by
    exact (show 0.8 * |f| ≤ |f| - |η*t| by linarith only [hp,hηt]).trans
      (le_trans (le_abs_self (|f| - |η*t|)) (abs_abs_sub_abs_le_abs_sub _ _))
  have hdist2 : 0.64 * f ^ 2 ≤ (f-η*t) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 0.8 * |f|) hdist 2
    rw [mul_pow, sq_abs, sq_abs] at h
    linarith only [h]
  have hf2 : 1600 ≤ f ^ 2 := by
    have h : 40 ≤ |f| := by linarith only [ha₁,hp]
    have hb := pow_le_pow_left₀ (by norm_num : 0 ≤ (40 : ℝ)) h 2
    norm_num [sq_abs] at hb
    exact hb
  have hfmargin : f ^ 2 / 200 + 6.6 ≤ 0.64 * f ^ 2 / 65 := by
    linarith only [hf2]
  have hgauss : χ ^ 2 / 130 ≤ χ ^ 2 / (1 + η ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hD (hD65.trans (by norm_num))
  have hsep : f ^ 2 / 200 + 6.6 ≤ (f - η*t) ^ 2 / (1 + η ^ 2) :=
    hfmargin.trans (div_le_div₀ (by positivity) hdist2 hD hD65)
  have hπ : Real.pi ^ 2 / 3 * 2 ≤ 6.6 := by
    have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2
    linarith only [h]
  have hGG := norm_saddleG_le (midModeRadius_abs_le_one hr p) χ
  have hR : ‖z₁‖ ≤ 6.6 := by
    have hS : ‖(Real.pi : ℂ) ^ 2 / 3‖ = Real.pi ^ 2 / 3 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    have hGle : ‖saddleG (midModeRadius r p) χ‖ ≤ Real.pi ^ 2 / 3 :=
      hGG.trans (mul_le_of_le_one_right (by positivity) (midModeRadius_abs_le_one hr p))
    exact (norm_sub_le _ _).trans (by rw [hS]; linarith only [hGle, hπ])
  have hR' := (mid_proj_angle_le_norm z₁ η).trans hR
  have hId : (z.re + η * z.im) / (1 + η ^ 2) =
      t ^ 2 - (f - η*t) ^ 2 / (1 + η ^ 2) - χ ^ 2 / (1 + η ^ 2) +
        (z₁.re + η * z₁.im) / (1 + η ^ 2) := by
    have he : z = ((t : ℂ) + (f : ℂ) * I) ^ 2 - (χ : ℂ) ^ 2 + z₁ := by
      unfold z midPhase t f z₁
      ring
    rw [he]
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      mul_zero, add_zero, zero_add, sub_zero, mul_one]
    field_simp
    ring
  have hbound : (z.re + η * z.im) / (1 + η ^ 2) ≤ a ^ 2 - f ^ 2 / 200 - χ ^ 2 / 130 := by
    rw [hId]
    have ht2 := pow_le_pow_left₀ ht hta 2
    linarith only [ht2,hsep,hgauss,hR']
  have hmul := mul_le_mul_of_nonneg_left hbound (show 0 ≤ Real.sqrt (n : ℝ) / a by positivity)
  rw [midRe_exponent hn hr']
  change a * Real.sqrt n + Real.sqrt n / a * _ ≤
    2 * (a * Real.sqrt n) - Real.sqrt n * f ^ 2 / (200 * a) - Real.sqrt n * χ^2 / (130*a)
  calc
    _ ≤ a * Real.sqrt n + Real.sqrt n / a * (a ^ 2 - f ^ 2 / 200 - χ ^ 2 / 130) :=
      add_le_add_right hmul _
    _ = _ := by field_simp; ring

end DurfeeCCS.Step09
