module

public import DurfeeCCS.Step08.SaddleBesselLaplace
public import DurfeeCCS.Step08.SaddleBesselRadicals
public import DurfeeCCS.Step08.SaddleNormalization
public import DurfeeCCS.Step08.PhaseGapParameters
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Evaluation of the linear model after the change of variable in (36). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex Set MeasureTheory DurfeeCCS.Step06

def saddleBesselSlope (r : ℝ) : ℂ := (r : ℂ) * I / (1 + (r : ℂ) * I)

def saddleBesselRate (n : ℕ) (r : ℝ) : ℂ :=
  2 * (Real.sqrt n : ℂ) * saddleBesselSlope r / saddleS r

def saddleBesselPrefactor (n : ℕ) (r : ℝ) : ℂ :=
  (saddleS r).sqrt * Complex.exp (2 * (Real.sqrt n : ℂ) * saddleS r) /
    ((Real.pi : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) *
      (Real.sqrt n : ℂ) * (Real.sqrt (Real.sqrt n) : ℂ))

def saddleBesselModel (n : ℕ) (r ψ : ℝ) : ℂ :=
  saddleBesselPrefactor n r *
    (Complex.exp (-saddleBesselRate n r * (ψ : ℂ)) / (Real.sqrt ψ : ℂ))

theorem sqrt_mul_right_half_planes {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    (z * w).sqrt = z.sqrt * w.sqrt := by
  obtain ⟨hzl, hzu⟩ := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  obtain ⟨hwl, hwu⟩ := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  unfold Complex.sqrt
  apply Complex.mul_cpow
  exact ⟨by linarith, by linarith⟩

private theorem complexSqrt_ne_zero {z : ℂ} (hz : z ≠ 0) : z.sqrt ≠ 0 := by
  intro h
  apply hz
  exact (principalSqrt_sq z).symm.trans (by rw [h]; norm_num)

theorem saddleBesselSlope_components (r : ℝ) :
    (saddleBesselSlope r).re = r ^ 2 / (1 + r ^ 2) ∧
      (saddleBesselSlope r).im = r / (1 + r ^ 2) := by
  unfold saddleBesselSlope
  constructor
  · simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
  · simp only [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring_nf

private theorem saddleBesselSlope_ne_zero {r : ℝ} (hr : 0 < r) : saddleBesselSlope r ≠ 0 := by
  intro hn
  have h := (saddleBesselSlope_components r).1
  rw [hn, Complex.zero_re] at h
  exact (div_pos (sq_pos_of_pos hr) (by positivity)).ne' h.symm

theorem saddleBesselSlope_arg {r : ℝ} (hr : 0 < r) :
    (saddleBesselSlope r).arg = Real.pi / 2 - Real.arctan r := by
  let p := saddleBesselSlope r
  obtain ⟨hp₁, hp₂⟩ := saddleBesselSlope_components r
  have hpre : 0 < p.re := hp₁.symm ▸ div_pos (sq_pos_of_pos hr) (by positivity)
  obtain ⟨hpl, hpu⟩ := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpre))
  have ht : Real.tan p.arg = r⁻¹ := by
    rw [Complex.tan_arg, hp₂, hp₁]
    have hsum : 1 + r ^ 2 ≠ 0 := by positivity
    field_simp
  calc
    p.arg = Real.arctan (Real.tan p.arg) := (Real.arctan_tan hpl hpu).symm
    _ = _ := by rw [ht, Real.arctan_inv_of_pos hr]

theorem norm_saddleBesselSlope {r : ℝ} (hr : 0 < r) :
    ‖saddleBesselSlope r‖ = r / Real.sqrt (1 + r ^ 2) := by
  rw [saddleBesselSlope, norm_div, norm_mul, Complex.norm_of_nonneg hr.le, Complex.norm_I, mul_one]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add]
  congr 1
  ring

theorem norm_sqrt_saddleBesselSlope {r : ℝ} (hr : 0 < r) :
    ‖(saddleBesselSlope r).sqrt‖ = Real.sqrt r / (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  rw [norm_principalSqrt, norm_saddleBesselSlope hr, Real.sqrt_div hr.le]
  congr 1
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (show 0 ≤ 1 + r ^ 2 by positivity)]
  norm_num

theorem integrable_saddleBesselModel {n : ℕ} {r : ℝ} (hRate : 0 < (saddleBesselRate n r).re) :
    IntegrableOn (saddleBesselModel n r) (Ioi 0) := by
  have hi := (integrable_laplace_rpow hRate (p := -1 / 2) (by norm_num)).const_mul
    (saddleBesselPrefactor n r)
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with ψ hψ
  have hψ' : 0 < ψ := hψ
  unfold saddleBesselModel
  simp only [Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [← Complex.ofReal_inv, ← Real.rpow_neg hψ'.le]
  norm_num

/-- The half-line model integral on page 15, before passing to amplitude and phase. -/
theorem integral_saddleBesselModel {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (hRate : 0 < (saddleBesselRate n r).re) :
    (∫ ψ in Ioi 0, saddleBesselModel n r ψ) =
      saddleS r * Complex.exp (2 * (Real.sqrt n : ℂ) * saddleS r) /
        (2 * (Real.pi : ℂ) * n * (saddleBesselSlope r).sqrt) := by
  let s := saddleS r
  let p := saddleBesselSlope r
  let k := saddleBesselRate n r
  let v := Real.sqrt n
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hv : 0 < v := Real.sqrt_pos.mpr hn'
  have hv₀ : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hv₂ : (v : ℂ) ^ 2 = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hn'.le, Complex.ofReal_natCast]
  obtain ⟨hbi, hba⟩ := saddleS_components hr
  have hs : 0 < s.re := hbi.trans hba
  have hs₀ : s ≠ 0 := by intro h; simp [h] at hs
  have hks : k * s = ((2 * v : ℝ) : ℂ) * p := by
    change (2 * (v : ℂ) * p / s) * s = ((2 * v : ℝ) : ℂ) * p
    push_cast
    field_simp
  have hsq : k.sqrt * s.sqrt = (Real.sqrt (2 * v) : ℂ) * p.sqrt := by
    rw [← sqrt_mul_right_half_planes hRate hs, hks, sqrt_ofReal_mul _ (by positivity)]
  have hkn : k.sqrt ≠ 0 := complexSqrt_ne_zero (fun h => by simp [k, h] at hRate)
  have hpn : p.sqrt ≠ 0 := complexSqrt_ne_zero (saddleBesselSlope_ne_zero hr)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπs : (Real.sqrt Real.pi : ℂ) ≠ 0 := by exact_mod_cast
    (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsv : (Real.sqrt v : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  have hst : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hst₂ : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num), Complex.ofReal_ofNat]
  have hsquare : s.sqrt ^ 2 = s := principalSqrt_sq _
  have hvs₂ : (Real.sqrt v : ℂ) ^ 2 = (v : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hv.le]
  have hquot : (Real.sqrt Real.pi : ℂ) / k.sqrt =
      (Real.sqrt Real.pi : ℂ) * s.sqrt / ((Real.sqrt (2 * v) : ℂ) * p.sqrt) := by
    rw [← hsq]
    have hsn := complexSqrt_ne_zero hs₀
    field_simp
  unfold saddleBesselModel
  rw [integral_const_mul, integral_laplace_inv_sqrt hRate,
    sqrt_div_right_half_plane _ Real.pi_pos.le hRate]
  change (s.sqrt * Complex.exp (2 * (v : ℂ) * s) /
    ((Real.pi : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) * (v : ℂ) * (Real.sqrt v : ℂ))) *
    ((Real.sqrt Real.pi : ℂ) / k.sqrt) =
      s * Complex.exp (2 * (v : ℂ) * s) / (2 * (Real.pi : ℂ) * (n : ℂ) * p.sqrt)
  rw [hquot, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_mul, Complex.ofReal_mul, ← hv₂]
  field_simp
  ring_nf
  rw [hst₂, hvs₂, hsquare]
  ring

/-- The complex leading term in (8), in its polar normalization. -/
theorem saddleBesselLead_eq_polar {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    saddleS r * Complex.exp (2 * (Real.sqrt n : ℂ) * saddleS r) /
        (2 * (Real.pi : ℂ) * n * (saddleBesselSlope r).sqrt) =
      (saddleAmplitude n r : ℂ) * Complex.exp ((saddlePhase n r : ℂ) * I) := by
  let s := saddleS r
  let p := (saddleBesselSlope r).sqrt
  let v := Real.sqrt n
  let a := 2 * s.re * v
  let b := 2 * s.im * v
  let c := 2 * Real.pi * (n : ℝ)
  have hp : p ≠ 0 := complexSqrt_ne_zero (saddleBesselSlope_ne_zero hr)
  have hAbsP : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hp).ne'
  have hc : (c : ℂ) ≠ 0 := by
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    exact_mod_cast (show 0 < c by dsimp [c]; positivity).ne'
  have he : Complex.exp (2 * (v : ℂ) * s) =
      (Real.exp a : ℂ) * Complex.exp ((b : ℂ) * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [a, b, Complex.mul_re, Complex.mul_im] <;> ring
  have hnum : s * Complex.exp (2 * (v : ℂ) * s) =
      ((‖s‖ * Real.exp a : ℝ) : ℂ) * Complex.exp (((b + s.arg : ℝ) : ℂ) * I) := by
    calc
      _ = ((‖s‖ : ℂ) * Complex.exp ((s.arg : ℂ) * I)) *
          ((Real.exp a : ℂ) * Complex.exp ((b : ℂ) * I)) := by
        rw [he, Complex.norm_mul_exp_arg_mul_I]
      _ = _ := by
        push_cast
        rw [add_mul, Complex.exp_add]
        ring
  have hden : (c : ℂ) * p =
      ((c * ‖p‖ : ℝ) : ℂ) * Complex.exp ((p.arg : ℂ) * I) := by
    calc
      _ = (c : ℂ) * ((‖p‖ : ℂ) * Complex.exp ((p.arg : ℂ) * I)) :=
        congrArg (fun z => (c : ℂ) * z) (Complex.norm_mul_exp_arg_mul_I p).symm
      _ = _ := by push_cast; ring
  have hphase : b + s.arg - p.arg = saddlePhase n r := by
    change 2 * s.im * v + s.arg - (saddleBesselSlope r).sqrt.arg = saddlePhase n r
    rw [principalSqrt_arg (saddleBesselSlope_ne_zero hr), saddleBesselSlope_arg hr, saddlePhase]
    ring
  have hamp : (‖s‖ * Real.exp a) / (c * ‖p‖) = saddleAmplitude n r := by
    change (‖s‖ * Real.exp a) / (c * ‖(saddleBesselSlope r).sqrt‖) = _
    rw [norm_sqrt_saddleBesselSlope hr, saddleAmplitude]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hpow : (1 + r ^ 2) ^ (1 / 4 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) _).ne'
    dsimp [c, a, s, v]
    field_simp [hpow, (Real.sqrt_pos.mpr hr).ne', Real.pi_ne_zero]
  rw [show 2 * (Real.pi : ℂ) * (n : ℂ) = (c : ℂ) by dsimp [c]; push_cast; rfl]
  change s * Complex.exp (2 * (v : ℂ) * s) / ((c : ℂ) * p) = _
  rw [hnum, hden, ← hphase, ← hamp]
  push_cast
  rw [sub_mul, Complex.exp_sub]
  field_simp

theorem integral_saddleBesselModel_re {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (hRate : 0 < (saddleBesselRate n r).re) :
    (∫ ψ in Ioi 0, saddleBesselModel n r ψ).re =
      saddleAmplitude n r * Real.cos (saddlePhase n r) := by
  rw [integral_saddleBesselModel hn hr hRate, saddleBesselLead_eq_polar hn hr,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem saddleBesselRate_bounds {n : ℕ} {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    saddleGamma r * saddleOmega n r ≤ (saddleBesselRate n r).re ∧
      ‖saddleBesselRate n r‖ ≤ 1.5 * saddleOmega n r := by
  let s := saddleS r
  let A := 2 * saddleBesselSlope r / ((s.re : ℂ) * s)
  have ha := (saddleS_components hr).1.trans (saddleS_components hr).2
  have ha₀ : ((saddleS r).re : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have heq : saddleBesselRate n r = (saddleOmega n r : ℂ) * A := by
    unfold saddleBesselRate saddleOmega
    dsimp only [A, s]
    push_cast
    field_simp [ha₀]
  have hω : 0 ≤ saddleOmega n r := mul_nonneg ha.le (Real.sqrt_nonneg _)
  obtain ⟨hRe, hNorm⟩ := saddle_model_coefficient_bounds hr hr₁
  change saddleGamma r ≤ A.re at hRe
  change ‖A‖ ≤ 1.5 at hNorm
  rw [heq, Complex.re_ofReal_mul, norm_mul, Complex.norm_of_nonneg hω, mul_comm (saddleGamma r),
    mul_comm (1.5 : ℝ)]
  exact ⟨mul_le_mul_of_nonneg_left hRe hω, mul_le_mul_of_nonneg_left hNorm hω⟩

theorem saddleBesselRate_re_pos {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    0 < (saddleBesselRate n r).re := by
  have hγ := (by norm_num : (0 : ℝ) < 0.55).trans_le (saddleGamma_bounds r).1
  exact (mul_pos hγ (saddleOmega_pos hn hr)).trans_le (saddleBesselRate_bounds hr hr₁).1

/-- The normalization bound (38) on the prefactor after the angular substitution. -/
theorem norm_saddleBesselPrefactor_le {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    ‖saddleBesselPrefactor n r‖ ≤
      saddleAmplitude n r * Real.sqrt (1.5 * saddleOmega n r / Real.pi) := by
  let k := saddleBesselRate n r
  have hk := saddleBesselRate_re_pos hn hr hr₁
  have hnz : k ≠ 0 := fun he => by
    change 0 < k.re at hk
    simp [he] at hk
  have hkn := norm_pos_iff.mpr hnz
  have hA : (∫ ψ in Ioi 0, saddleBesselModel n r ψ) =
      (saddleAmplitude n r : ℂ) * Complex.exp ((saddlePhase n r : ℂ) * I) :=
    (integral_saddleBesselModel hn hr hk).trans (saddleBesselLead_eq_polar hn hr)
  have hB : (∫ ψ in Ioi 0, saddleBesselModel n r ψ) =
      saddleBesselPrefactor n r * Complex.sqrt ((Real.pi : ℂ) / k) := by
    unfold saddleBesselModel
    rw [integral_const_mul, integral_laplace_inv_sqrt hk]
  have hnorm := congrArg norm (hA.symm.trans hB)
  have hM := saddleAmplitude_pos hn hr
  simp only [norm_mul, Complex.norm_of_nonneg hM.le, Complex.norm_exp_ofReal_mul_I, mul_one,
    norm_principalSqrt, norm_div, Complex.norm_of_nonneg Real.pi_pos.le] at hnorm
  have hroot : Real.sqrt (Real.pi / ‖k‖) * Real.sqrt (‖k‖ / Real.pi) = 1 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi / ‖k‖)]
    rw [show Real.pi / ‖k‖ * (‖k‖ / Real.pi) = 1 by
      field_simp [hkn.ne', Real.pi_ne_zero], Real.sqrt_one]
  calc
    _ = saddleAmplitude n r * Real.sqrt (‖k‖ / Real.pi) := by
      rw [hnorm, mul_assoc, hroot, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right (saddleBesselRate_bounds hr hr₁).2 Real.pi_pos.le)) hM.le

end DurfeeCCS.Step08
