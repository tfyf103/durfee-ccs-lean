module

public import DurfeeCCS.Step07.SaddleEndpoints
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Reusable rational certificates for saddle components at fixed log radii. -/

@[expose] public section

namespace DurfeeCCS.Step07

open Complex DurfeeCCS.Step06

/-- Rational input and endpoint candidates. The analytic checks use the degree
of the paired dilogarithm sum and the enclosure of the reciprocal radius. -/
structure SaddleEndpointCertificate where
  logRadius : ℚ
  pairs : ℕ
  reciprocalLow : ℚ
  reciprocalHigh : ℚ
  squareReLow : ℚ
  squareReHigh : ℚ
  squareImLow : ℚ
  squareImHigh : ℚ
  squareNormLow : ℚ
  squareNormHigh : ℚ
  reLow : ℚ
  reHigh : ℚ
  imLow : ℚ
  imHigh : ℚ
  gapLow : ℚ

namespace SaddleEndpointCertificate

def piLow : ℚ := 3.14159265358979
def piHigh : ℚ := 3.14159265358980

structure Valid (c : SaddleEndpointCertificate) : Prop where
  log_nonneg : 0 ≤ c.logRadius
  reciprocal_nonneg : 0 ≤ c.reciprocalLow
  reciprocal_le_one : c.reciprocalHigh ≤ 1
  squareRe_nonneg : 0 ≤ c.squareReLow
  squareIm_nonneg : 0 ≤ c.squareImLow
  squareNorm_nonneg : 0 ≤ c.squareNormHigh
  square_re_lower :
    c.squareReLow ≤ piLow^2/12+c.logRadius^2 -
      saddlePartialUpper 1 c.pairs (c.reciprocalLow^2) (c.reciprocalHigh^2) / 2
  square_re_upper :
    piHigh^2/12+c.logRadius^2-saddlePartial 1 c.pairs (c.reciprocalLow^2) (c.reciprocalHigh^2) / 2 ≤
      c.squareReHigh
  square_im_lower :
    c.squareImLow ≤ piLow*c.logRadius+2*saddlePartial 2 c.pairs c.reciprocalLow c.reciprocalHigh
  square_im_upper :
    piHigh*c.logRadius+2*saddlePartialUpper 2 c.pairs c.reciprocalLow c.reciprocalHigh ≤
      c.squareImHigh
  square_norm_lower : c.squareNormLow^2 ≤ c.squareReLow^2 + c.squareImLow^2
  square_norm_upper : c.squareReHigh^2 + c.squareImHigh^2 ≤ c.squareNormHigh^2
  re_upper_nonneg : 0 ≤ c.reHigh
  im_upper_nonneg : 0 ≤ c.imHigh
  re_lower : c.reLow^2 ≤ (c.squareNormLow + c.squareReLow) / 2
  re_upper : (c.squareNormHigh + c.squareReHigh) / 2 ≤ c.reHigh^2
  im_lower : c.imLow^2 ≤ (c.squareNormLow - c.squareReHigh) / 2
  im_upper : (c.squareNormHigh - c.squareReLow) / 2 ≤ c.imHigh^2
  gap_lower : c.gapLow < (c.squareNormLow + c.squareReLow) / 2 - c.logRadius^2

private theorem cast_piLow : (piLow : ℝ) < Real.pi := by
  unfold piLow
  norm_num
  linarith [Real.pi_gt_d20]

private theorem cast_piHigh : Real.pi < (piHigh : ℝ) := by
  unfold piHigh
  norm_num
  linarith [Real.pi_lt_d20]

structure Encloses (c : SaddleEndpointCertificate) : Prop where
  re_lower : (c.reLow : ℝ) ≤ (saddleS (Real.exp c.logRadius)).re
  re_upper : (saddleS (Real.exp c.logRadius)).re ≤ (c.reHigh : ℝ)
  im_lower : (c.imLow : ℝ) ≤ (saddleS (Real.exp c.logRadius)).im
  im_upper : (saddleS (Real.exp c.logRadius)).im ≤ (c.imHigh : ℝ)
  gap_lower : (c.gapLow : ℝ) < (saddleS (Real.exp c.logRadius)).re^2 - (c.logRadius : ℝ)^2

theorem encloses (c : SaddleEndpointCertificate) (h : c.Valid)
    (hl : (c.reciprocalLow : ℝ) ≤ Real.exp (-c.logRadius))
    (hu : Real.exp (-c.logRadius) ≤ (c.reciprocalHigh : ℝ)) :
    c.Encloses := by
  let t : ℝ := c.logRadius
  let z := saddlePhaseSquare (Real.exp t)
  have ht : 0 ≤ t := by
    dsimp only [t]
    exact_mod_cast h.log_nonneg
  have hl₀ : (0 : ℝ) ≤ c.reciprocalLow := by exact_mod_cast h.reciprocal_nonneg
  have hx₁ : ((c.reciprocalLow^2 : ℚ) : ℝ) ≤ Real.exp (-2*t) := by
    rw [Rat.cast_pow, show -2*t = ((2 : ℕ) : ℝ) * (-t) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ hl₀ hl _
  have hx₂ : Real.exp (-2*t) ≤ ((c.reciprocalHigh^2 : ℚ) : ℝ) := by
    rw [Rat.cast_pow, show -2*t = ((2 : ℕ) : ℝ) * (-t) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hu _
  obtain ⟨ha₁, ha₂⟩ := saddlePartial_bounds_re c.pairs (sq_nonneg _) hx₁ hx₂
    (pow_le_one₀ (by exact_mod_cast (Real.exp_pos _).le.trans hu) h.reciprocal_le_one)
  obtain ⟨hb₁, hb₂⟩ := saddlePartial_bounds_im c.pairs h.reciprocal_nonneg hl hu h.reciprocal_le_one
  have hp₁ : (piLow : ℝ)^2 ≤ Real.pi^2 :=
    pow_le_pow_left₀ (by norm_num [piLow]) cast_piLow.le _
  have hp₂ : Real.pi^2 ≤ (piHigh : ℝ)^2 :=
    pow_le_pow_left₀ Real.pi_pos.le cast_piHigh.le _
  have hz₁ : (c.squareReLow : ℝ) ≤ z.re := by
    simp only [z, phaseSquare_re_exp]
    have hr := (Rat.cast_le (K := ℝ)).mpr h.square_re_lower
    push_cast at hr
    linarith
  have hz₂ : z.re ≤ (c.squareReHigh : ℝ) := by
    simp only [z, phaseSquare_re_exp]
    have hr := (Rat.cast_le (K := ℝ)).mpr h.square_re_upper
    push_cast at hr
    linarith
  have hz₃ : (c.squareImLow : ℝ) ≤ z.im := by
    simp only [z, phaseSquare_im_exp ht]
    have hr := (Rat.cast_le (K := ℝ)).mpr h.square_im_lower
    push_cast at hr
    linarith [mul_le_mul_of_nonneg_right cast_piLow.le ht]
  have hz₄ : z.im ≤ (c.squareImHigh : ℝ) := by
    simp only [z, phaseSquare_im_exp ht]
    have hr := (Rat.cast_le (K := ℝ)).mpr h.square_im_upper
    push_cast at hr
    linarith [mul_le_mul_of_nonneg_right cast_piHigh.le ht]
  obtain ⟨hw₁, hw₂⟩ := saddle_norm_bounds_from_components
    (wl := (c.squareNormLow : ℝ)) (wu := (c.squareNormHigh : ℝ))
    (by exact_mod_cast h.squareRe_nonneg) (by exact_mod_cast h.squareIm_nonneg)
    (by exact_mod_cast h.squareNorm_nonneg) hz₁ hz₂ hz₃ hz₄
    (by exact_mod_cast h.square_norm_lower) (by exact_mod_cast h.square_norm_upper)
  obtain ⟨hA, hB⟩ := saddle_component_squares (Real.exp t)
  change _ = (‖z‖ + z.re)/2 at hA
  change _ = (‖z‖ - z.re)/2 at hB
  obtain ⟨hib, hir⟩ := saddleS_components (Real.exp_pos t)
  constructor
  · have hh := (Rat.cast_le (K := ℝ)).mpr h.re_lower
    push_cast at hh
    exact le_of_pow_le_pow_left₀ two_ne_zero (hib.trans hir).le
      (by linarith : (c.reLow : ℝ)^2 ≤ (saddleS (Real.exp t)).re^2)
  · have hh := (Rat.cast_le (K := ℝ)).mpr h.re_upper
    push_cast at hh
    exact (sq_le_sq₀ (hib.trans hir).le (by exact_mod_cast h.re_upper_nonneg)).mp (by linarith)
  · have hh := (Rat.cast_le (K := ℝ)).mpr h.im_lower
    push_cast at hh
    exact le_of_pow_le_pow_left₀ two_ne_zero hib.le
      (by linarith : (c.imLow : ℝ)^2 ≤ (saddleS (Real.exp t)).im^2)
  · have hh := (Rat.cast_le (K := ℝ)).mpr h.im_upper
    push_cast at hh
    exact (sq_le_sq₀ hib.le (by exact_mod_cast h.im_upper_nonneg)).mp (by linarith)
  · have hh := (Rat.cast_lt (K := ℝ)).mpr h.gap_lower
    push_cast at hh
    change _ < _ - t^2 at hh ⊢
    linarith

end SaddleEndpointCertificate

/-- Endpoint certificates for the finite tables on pages 30 and 34. -/
def saddleEndpointData (i : Fin 21) : SaddleEndpointCertificate := ![
  ⟨0.04, 163, 0.9607894391523, 0.9607894391524,
    0.43977006889, 0.43977006890, 1.89556293478, 1.89556293479, 1.94590764251, 1.94590764253,
    1.09217, 1.09218, 0.86779, 0.86780, 1.19123⟩,
  ⟨0.0625, 104, 0.9394130628134, 0.9394130628135,
    0.45654901471, 0.45654901472, 1.93205844840, 1.93205844841, 1.98526745071, 1.98526745073,
    1.10494, 1.10495, 0.87427, 0.87428, 1.21700⟩,
  ⟨0.08, 82, 0.9231163463866, 0.9231163463867,
    0.46997056994, 0.46997056995, 1.96079318964, 1.96079318965, 2.01632890897, 2.01632890899,
    1.11496, 1.11497, 0.87930, 0.87931, 1.23674⟩,
  ⟨0.12, 55, 0.8869204367171, 0.8869204367172,
    0.50189876479, 0.50189876480, 2.02761812824, 2.02761812825, 2.08881249614, 2.08881249617,
    1.13813, 1.13814, 0.89076, 0.89077, 1.28095⟩,
  ⟨0.125, 52, 0.8824969025845, 0.8824969025846,
    0.50601442799, 0.50601442800, 2.03608308307, 2.03608308308, 2.09801928554, 2.09801928556,
    1.14105, 1.14106, 0.89218, 0.89219, 1.28639⟩,
  ⟨0.16, 41, 0.8521437889662, 0.8521437889663,
    0.53561799311, 0.53561799312, 2.09603140983, 2.09603140984, 2.16338491848, 2.16338491850,
    1.16168, 1.16169, 0.90215, 0.90216, 1.32390⟩,
  ⟨0.20, 33, 0.8187307530779, 0.8187307530780,
    0.57119099307, 0.57119099308, 2.16602422765, 2.16602422766, 2.24007145094, 2.24007145096,
    1.18559, 1.18560, 0.91347, 0.91348, 1.36563⟩,
  ⟨0.25, 26, 0.7788007830714, 0.7788007830715,
    0.61835839342, 0.61835839343, 2.25571918233, 2.25571918234, 2.33893910400, 2.33893910402,
    1.21599, 1.21600, 0.92751, 0.92752, 1.41614⟩,
  ⟨0.32, 21, 0.7261490370736, 0.7261490370737,
    0.68964708887, 0.68964708888, 2.38535640063, 2.38535640064, 2.48305019385, 2.48305019387,
    1.25950, 1.25951, 0.94694, 0.94695, 1.48394⟩,
  ⟨0.40, 17, 0.6703200460356, 0.6703200460357,
    0.77899340168, 0.77899340169, 2.53921054368, 2.53921054369, 2.65601598357, 2.65601598359,
    1.31053, 1.31054, 0.96876, 0.96877, 1.55750⟩,
  ⟨0.5, 13, 0.6065306597126, 0.6065306597127,
    0.90314303522, 0.90314303523, 2.73982813100, 2.73982813101, 2.88484410835, 2.88484410837,
    1.37622, 1.37623, 0.99541, 0.99542, 1.64399⟩,
  ⟨0.65, 10, 0.5220457767610, 0.5220457767611,
    1.11700785450, 1.11700785451, 3.05724117933, 3.05724117934, 3.25490862784, 3.25490862786,
    1.47849, 1.47850, 1.03390, 1.03391, 1.76345⟩,
  ⟨0.85, 8, 0.4274149319487, 0.4274149319488,
    1.45748941354, 1.45748941355, 3.50887739813, 3.50887739814, 3.79953891751, 3.79953891753,
    1.62126, 1.62127, 1.08213, 1.08214, 1.90601⟩,
  ⟨1, 7, 0.3678794411714, 0.3678794411715,
    1.75696079106, 1.75696079107, 3.86679235443, 3.86679235444, 4.24723372721, 4.24723372723,
    1.73265, 1.73266, 1.11585, 1.11586, 2.00209⟩,
  ⟨1.5, 5, 0.2231301601484, 0.2231301601485,
    3.04787667325, 3.04787667326, 5.15622379035, 5.15622379036, 5.98967411396, 5.98967411398,
    2.12574, 2.12575, 1.21280, 1.21281, 2.26877⟩,
  ⟨2, 4, 0.1353352832366, 0.1353352832367,
    4.81335080893, 4.81335080894, 6.55330863826, 6.55330863827, 8.13106389829, 8.13106389831,
    2.54405, 2.54406, 1.28796, 1.28797, 2.47220⟩,
  ⟨2.25, 3, 0.1053992245618, 0.1053992245619,
    5.87942788568, 5.87942788569, 7.27912275895, 7.27912275896, 9.35699205956, 9.35699205958,
    2.76011, 2.76012, 1.31862, 1.31863, 2.55570⟩,
  ⟨3, 3, 0.0497870683678, 0.0497870683679,
    9.82122842451, 9.82122842452, 9.52432469754, 9.52432469755, 13.68098273921, 13.68098273923,
    3.42798, 3.42799, 1.38920, 1.38921, 2.75110⟩,
  ⟨4, 3, 0.0183156388887, 0.0183156388888,
    16.82229931617, 16.82229931618, 12.60300052692, 12.60300052693, 21.01964263645, 21.01964263648,
    4.34982, 4.34983, 1.44867, 1.44868, 2.92097⟩,
  ⟨5, 3, 0.0067379469990, 0.0067379469991,
    25.82244433371, 25.82244433372, 15.72143909396, 15.72143909398, 30.23180905193, 30.23180905196,
    5.29406, 5.29407, 1.48481, 1.48482, 3.02712⟩,
  ⟨6, 3, 0.0024787521766, 0.0024787521767,
    36.82246396132, 36.82246396133, 18.85451342250, 18.85451342251, 41.36890775186, 41.36890775188,
    6.25265, 6.25266, 1.50772, 1.50773, 3.09568⟩
] i

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 16384 in
theorem saddleEndpointData_valid (i : Fin 21) : (saddleEndpointData i).Valid := by
  fin_cases i <;> constructor <;> decide +kernel

set_option maxHeartbeats 16000000 in
private theorem saddleEndpointData_exp (i : Fin 21) :
    ((saddleEndpointData i).reciprocalLow : ℝ) ≤ Real.exp (-(saddleEndpointData i).logRadius : ℝ) ∧
      Real.exp (-(saddleEndpointData i).logRadius : ℝ) ≤ ((saddleEndpointData i).reciprocalHigh : ℝ) := by
  fin_cases i <;> constructor <;>
    simp only [saddleEndpointData, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Rat.cast_ofScientific, Rat.cast_natCast, Rat.cast_ofNat] <;>
    dyadic_interval +kernel [prec := 60]

theorem saddleEndpointData_bounds (i : Fin 21) : (saddleEndpointData i).Encloses :=
  (saddleEndpointData i).encloses (saddleEndpointData_valid i)
    (saddleEndpointData_exp i).1 (saddleEndpointData_exp i).2

end DurfeeCCS.Step07
