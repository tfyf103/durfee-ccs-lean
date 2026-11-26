module

public import DurfeeCCS.Step09.MidRangeOverlap
import all DurfeeCCS.Step07.SaddleEndpoints
import all DurfeeCCS.Step08.SaddleBesselEstimate

/-! Exact forms for the unnumbered saddle statements in Sections 3 and 4. -/

public section

namespace DurfeeCCS.Step13

open DurfeeCCS.Step06 DurfeeCCS.Step08 DurfeeCCS.Step09 MeasureTheory Set

/-- Equation (6), with both branches of the symmetric dilogarithm factor. -/
theorem saddleG_formula (r θ : ℝ) :
    saddleG r θ =
      -principalDilog (-(r : ℂ) * Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) -
        principalDilog (-(r : ℂ) * Complex.I * Complex.exp (-(θ : ℂ) * Complex.I)) := rfl

/-- The amplitude and phase normalizations in the two lines of equation (8). -/
theorem saddle_amplitude_phase_formulas (n : ℕ) (r : ℝ) :
    saddleAmplitude n r =
      ‖saddleS r‖ * (1 + r ^ 2) ^ (1 / 4 : ℝ) *
        Real.exp (2 * (saddleS r).re * Real.sqrt n) / (2 * Real.pi * n * Real.sqrt r) ∧
    saddlePhase n r =
      2 * (saddleS r).im * Real.sqrt n + (saddleS r).arg - Real.pi / 4 + Real.arctan r / 2 :=
  ⟨rfl, rfl⟩

/-- The normalization of the local Bessel density in (36), before the angular weight. -/
theorem saddle_central_kernel_model {n : ℕ} (hn : 0 < n) {r : ℝ} {p : ℂ}
    (hs : 0 < (saddleS r).re) (hp : 0 < p.re) (hq : 0 < (p / saddleS r).re) :
    (Real.sqrt 2 : ℂ) * (((Real.pi : ℂ)⁻¹) * (p / (Real.sqrt n : ℂ)) *
      (Complex.exp (2 * (Real.sqrt n : ℂ) * p) /
        (2 * (Real.pi : ℂ) * (2 * (Real.sqrt n : ℂ) * p)).sqrt)) =
      saddleBesselPrefactor n r * (p / saddleS r).sqrt *
        Complex.exp (2 * (Real.sqrt n : ℂ) * (p - saddleS r)) :=
  Step08.saddleBesselCentral_kernel_model hn hs hp hq

/-- At any integral multiple of π in the manuscript's middle radius range, the
Durfee value has the corresponding alternating sign. -/
theorem sign_at_integral_phase {n : ℕ} {k : ℤ} {r : ℝ}
    (hn : 6400 ≤ n) (hmin : 16 * Real.pi ^ 2 / (n : ℝ) ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hphase : saddlePhase n r = (k : ℝ) * Real.pi) :
    Real.sign (durfeeNegativeValue n r) = (-1 : ℝ) ^ k := by
  have hn_nat : 0 < n := by omega
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn_nat
  have hr : 0 < r := (by positivity : 0 < 16 * Real.pi ^ 2 / (n : ℝ)).trans_le hmin
  have hscale : 4 * Real.pi ≤ Real.sqrt ((n : ℝ) * r) := by
    apply Real.le_sqrt_of_sq_le
    have h := (div_le_iff₀ hn_real).mp hmin
    nlinarith only [h]
  have he := saddle_ranges_relative_error hn hr hmax hscale
  have hp := saddleAmplitude_pos hn_nat hr
  rw [hphase, Real.cos_int_mul_pi] at he
  have ha : |(-1 : ℝ) ^ k| = 1 := by norm_num [abs_zpow]
  have hs : (-1 : ℝ) ^ k = 1 ∨ (-1 : ℝ) ^ k = -1 :=
    (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ha
  rcases hs with h | h
  · rw [h, mul_one] at he
    rw [h, Real.sign_of_pos]
    linarith only [(abs_lt.mp he).1, hp]
  · rw [h, mul_neg_one, sub_neg_eq_add] at he
    rw [h, Real.sign_of_neg]
    linarith only [(abs_lt.mp he).2, hp]

/-- The real part of the squared saddle is the alternating even-power series,
indexed by j = k + 1. -/
theorem saddle_square_re_hasSum {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    HasSum (fun k : ℕ => 2 * (-1 : ℝ) ^ k * r ^ (2 * (k + 1)) / ((2 * (k + 1) : ℕ) : ℝ) ^ 2)
      (saddleS r ^ 2).re := by
  rw [saddleS_sq, Step07.phaseSquare_re]
  have hr₂ : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr₁
  have hs := (Step07.dilog_neg_hasSum (sq_nonneg r) hr₂).mul_left (1 / 2 : ℝ)
  rw [← Complex.ofReal_pow]
  convert hs using 1
  · funext k
    simp only [Step07.saddleCoeff, one_mul, Nat.cast_mul, Nat.cast_ofNat, pow_mul]
    ring
  · ring

/-- Half the imaginary part of the squared saddle is the alternating odd-power series. -/
theorem saddle_square_half_im_hasSum {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j * r ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      ((saddleS r ^ 2).im / 2) := by
  rw [saddleS_sq, Step07.phaseSquare_im]
  convert Step07.dilog_negImag_hasSum hr.le hr₁ using 1
  · funext k
    simp only [Step07.saddleCoeff]
    ring
  · ring

/-- The two alternating-series truncation bounds used after equation (22). -/
theorem saddle_alternating_series_bounds {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    3 * r ^ 2 / 8 ≤ (saddleS r ^ 2).re ∧ (saddleS r ^ 2).re ≤ r ^ 2 / 2 ∧
      r * (1 - r ^ 2 / 9) ≤ (saddleS r ^ 2).im / 2 ∧ (saddleS r ^ 2).im / 2 ≤ r := by
  have hr₂ : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr₁
  have hRe := Step07.dilog_neg_hasSum (sq_nonneg r) hr₂
  have hIm := Step07.dilog_negImag_hasSum hr.le hr₁
  have hloRe := (Step07.alternating_bounds 1 (sq_nonneg r) hr₂ hRe 1).1
  have hhiRe := (Step07.alternating_bounds 1 (sq_nonneg r) hr₂ hRe 0).2
  have hloIm := (Step07.alternating_bounds 2 hr.le hr₁ hIm 1).1
  have hhiIm := (Step07.alternating_bounds 2 hr.le hr₁ hIm 0).2
  norm_num [Step07.saddleCoeff, Finset.sum_range_succ] at hloRe hhiRe hloIm hhiIm
  rw [← Complex.ofReal_pow] at hloRe hhiRe
  rw [← neg_mul] at hloIm hhiIm
  rw [saddleS_sq, Step07.phaseSquare_re, Step07.phaseSquare_im, ← Complex.ofReal_pow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [hloRe, mul_le_mul_of_nonneg_left hr₂ (sq_nonneg r)]
  · linarith only [hhiRe]
  · linarith only [hloIm]
  · linarith only [hhiIm]

/-- The exact prefactor ratio and its upper bound in equation (38). -/
theorem saddle_bessel_prefactor_ratio {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) :
    let ratio := Real.sqrt
      (2 * r * Real.sqrt n / (Real.pi * ‖saddleS r‖ * Real.sqrt (1 + r ^ 2)))
    ‖saddleBesselPrefactor n r‖ / saddleAmplitude n r = ratio ∧
      ratio ≤ Real.sqrt (1.5 * saddleOmega n r / Real.pi) := by
  dsimp only
  let k := saddleBesselRate n r
  have hk : 0 < k.re := saddleBesselRate_re_pos hn hr hr₁
  have hkNorm : 0 < ‖k‖ := hk.trans_le (Complex.re_le_norm k)
  have hM := saddleAmplitude_pos hn hr
  have hInt : (∫ ψ in Ioi 0, saddleBesselModel n r ψ) =
      (saddleAmplitude n r : ℂ) * Complex.exp ((saddlePhase n r : ℂ) * Complex.I) :=
    (integral_saddleBesselModel hn hr hk).trans (saddleBesselLead_eq_polar hn hr)
  have hEval : (∫ ψ in Ioi 0, saddleBesselModel n r ψ) =
      saddleBesselPrefactor n r * Complex.sqrt ((Real.pi : ℂ) / k) := by
    unfold saddleBesselModel
    rw [integral_const_mul, integral_laplace_inv_sqrt hk]
  have hNorm := congrArg norm (hInt.symm.trans hEval)
  simp only [norm_mul, Complex.norm_of_nonneg hM.le, Complex.norm_exp_ofReal_mul_I, mul_one,
    norm_principalSqrt, norm_div, Complex.norm_of_nonneg Real.pi_pos.le] at hNorm
  have hRoot : Real.sqrt (Real.pi / ‖k‖) * Real.sqrt (‖k‖ / Real.pi) = 1 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi / ‖k‖)]
    rw [show Real.pi / ‖k‖ * (‖k‖ / Real.pi) = 1 by
      field_simp [hkNorm.ne', Real.pi_ne_zero], Real.sqrt_one]
  have hRate : ‖k‖ / Real.pi =
      2 * r * Real.sqrt n / (Real.pi * ‖saddleS r‖ * Real.sqrt (1 + r ^ 2)) := by
    dsimp only [k, saddleBesselRate]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_of_nonneg (Real.sqrt_nonneg _), norm_saddleBesselSlope hr]
    ring
  rw [← hRate]
  constructor
  · apply (div_eq_iff hM.ne').mpr
    rw [mul_comm, hNorm, mul_assoc, hRoot, mul_one]
  · exact Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right (saddleBesselRate_bounds hr hr₁).2 Real.pi_pos.le)

end DurfeeCCS.Step13
