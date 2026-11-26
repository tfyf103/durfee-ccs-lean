module

public import DurfeeCCS.Step06.BesselSeries
public import DurfeeCCS.Step06.Saddle
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.NumberTheory.ZetaValues

/-! The entire Bessel kernel and the angular symmetries of the average in (32). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set intervalIntegral DurfeeCCS.Step06
open scoped ComplexConjugate

/-- The analytic extension of `sqrt(g/n) I₁(2 sqrt(n g))`. -/
def saddleBesselKernel (n : ℕ) (g : ℂ) : ℂ := g * (besselAuxSeries 1).sum ((n : ℂ) * g)

theorem saddleBesselKernel_eq_tsum (n : ℕ) (g : ℂ) :
    saddleBesselKernel n g = ∑' k : ℕ,
      (n : ℂ) ^ k * g ^ (k + 1) / ((k.factorial : ℂ) * ((k + 1).factorial : ℂ)) := by
  unfold saddleBesselKernel besselAuxSeries
  rw [← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq,
    ← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [smul_eq_mul, besselAuxCoeff, mul_pow, pow_succ]
  ring

theorem analyticAt_saddleBesselKernel (n : ℕ) (g : ℂ) :
    AnalyticAt ℂ (saddleBesselKernel n) g := by
  unfold saddleBesselKernel
  fun_prop

theorem saddleBesselKernel_eq_besselI {n : ℕ} (hn : 0 < n) (g : ℂ) :
    saddleBesselKernel n g = Complex.sqrt g / (Real.sqrt n : ℂ) *
      besselI 1 (2 * (Real.sqrt n : ℂ) * Complex.sqrt g) := by
  have hn' : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hs : (Real.sqrt (n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [saddleBesselKernel, besselI_eq_aux]
  have hz : 2 * (Real.sqrt n : ℂ) * Complex.sqrt g / 2 = (Real.sqrt n : ℂ) * Complex.sqrt g := by ring
  rw [hz, pow_one, mul_pow, hs, principalSqrt_sq]
  rw [← mul_assoc]
  congr 1
  calc
    g = g.sqrt ^ 2 := (principalSqrt_sq g).symm
    _ = g.sqrt / (Real.sqrt n : ℂ) * ((Real.sqrt n : ℂ) * g.sqrt) := by field_simp

theorem saddleBesselKernel_conj (n : ℕ) (g : ℂ) :
    saddleBesselKernel n (conj g) = conj (saddleBesselKernel n g) := by
  simp only [saddleBesselKernel_eq_tsum]
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp

private theorem principalDilog_conj_disk {z : ℂ} (hz : ‖z‖ ≤ 1) :
    principalDilog (conj z) = conj (principalDilog z) := by
  have hc : ‖conj z‖ ≤ 1 := by simpa using hz
  have hs := Complex.hasSum_conj'.mpr (principalDilog_hasSum hz)
  exact (principalDilog_hasSum hc).unique (by simpa using hs)

theorem saddleG_even (r : ℝ) : Function.Even (saddleG r) := by
  intro θ
  simp [saddleG]
  ring

theorem saddleG_add_pi {r : ℝ} (hr : |r| ≤ 1) (θ : ℝ) :
    saddleG r (θ + Real.pi) = conj (saddleG r θ) := by
  have hc₁ : ‖-(r : ℂ) * I * Complex.exp ((θ : ℂ) * I)‖ ≤ 1 := by
    simpa only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_I,
      Complex.norm_exp_ofReal_mul_I, mul_one] using hr
  have hc₂ : ‖-(r : ℂ) * I * Complex.exp (-(θ : ℂ) * I)‖ ≤ 1 := by
    simpa only [← Complex.ofReal_neg, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, norm_I, Complex.norm_exp_ofReal_mul_I, mul_one] using hr
  have hp : Complex.exp (((θ + Real.pi : ℝ) : ℂ) * I) = -Complex.exp ((θ : ℂ) * I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
  have hn : Complex.exp (-((θ + Real.pi : ℝ) : ℂ) * I) = -Complex.exp (-(θ : ℂ) * I) := by
    rw [Complex.ofReal_add, neg_add, add_mul, Complex.exp_add, neg_mul,
      show Complex.exp (- (Real.pi : ℂ) * I) = -1 by
        rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; simp]
    simp
  unfold saddleG
  rw [hp, hn, map_sub, map_neg, ← principalDilog_conj_disk hc₁,
    ← principalDilog_conj_disk hc₂]
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_conj]
  rw [show (θ : ℂ) * -I = -(θ : ℂ) * I by ring,
    show -(θ : ℂ) * -I = (θ : ℂ) * I by ring]
  have harg₁ : -(r : ℂ) * I * -Complex.exp ((θ : ℂ) * I) =
      -(r : ℂ) * -I * Complex.exp ((θ : ℂ) * I) := by ring
  have harg₂ : -(r : ℂ) * I * -Complex.exp (-(θ : ℂ) * I) =
      -(r : ℂ) * -I * Complex.exp (-(θ : ℂ) * I) := by ring
  rw [harg₁, harg₂]
  ring

theorem continuousOn_principalDilog_closedDisk :
    ContinuousOn principalDilog {z : ℂ | ‖z‖ ≤ 1} := by
  let f (k : ℕ) (z : ℂ) := z ^ (k + 1) / (((k + 1 : ℕ) : ℂ) ^ 2)
  have hf (k : ℕ) : Continuous (f k) := by unfold f; fun_prop
  have hsum : Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
  have hb (k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
      ‖f k z‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
    simp only [f, norm_div, norm_pow, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg z) hz) (by positivity)
  refine (continuousOn_tsum (fun k => (hf k).continuousOn) hsum hb).congr ?_
  exact fun z hz => (principalDilog_hasSum hz).tsum_eq.symm

theorem continuous_saddleG {r : ℝ} (hr : |r| ≤ 1) : Continuous (saddleG r) := by
  apply Continuous.sub
  · apply Continuous.neg
    apply continuousOn_principalDilog_closedDisk.comp_continuous (by fun_prop)
    intro θ
    simpa [norm_mul, Complex.norm_exp_ofReal_mul_I] using hr
  · apply continuousOn_principalDilog_closedDisk.comp_continuous (by fun_prop)
    intro θ
    change ‖-(r : ℂ) * I * Complex.exp (-(θ : ℂ) * I)‖ ≤ 1
    simpa only [← Complex.ofReal_neg, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, norm_I, Complex.norm_exp_ofReal_mul_I, mul_one] using hr

set_option maxHeartbeats 800000 in
private theorem norm_principalDilog_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖principalDilog z‖ ≤ ‖z‖ * (Real.pi ^ 2 / 6) := by
  let f (k : ℕ) := z ^ (k + 1) / (((k + 1 : ℕ) : ℂ) ^ 2)
  have hs : HasSum f (principalDilog z) := principalDilog_hasSum hz
  have hu₀ : HasSum (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 6) := by
    apply (hasSum_nat_add_iff (f := fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 2) 1).mpr
    simpa using hasSum_zeta_two
  have hu : HasSum (fun k : ℕ => ‖z‖ * (1 / ((k + 1 : ℕ) : ℝ) ^ 2))
      (‖z‖ * (Real.pi ^ 2 / 6)) :=
    hu₀.mul_left ‖z‖
  have hb (k : ℕ) : ‖f k‖ ≤ ‖z‖ * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    simp only [f, pow_succ _ k, norm_div, norm_mul, norm_pow, Complex.norm_natCast,
      ← mul_div_assoc, mul_one]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg z) (pow_le_one₀ (norm_nonneg z) hz)) (by positivity)
  have hv : Summable fun k => ‖f k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hu.summable
  rw [← hs.tsum_eq, ← hu.tsum_eq]
  exact (norm_tsum_le_tsum_norm hv).trans (hv.tsum_le_tsum hb hu.summable)

/-- The uniform dilogarithm bound used on the outer portion of the central half-arc. -/
theorem norm_saddleG_le {r : ℝ} (hr : |r| ≤ 1) (θ : ℝ) :
    ‖saddleG r θ‖ ≤ Real.pi ^ 2 / 3 * |r| := by
  have hpos : ‖-(r : ℂ) * I * Complex.exp ((θ : ℂ) * I)‖ = |r| := by
    simp [Complex.norm_exp_ofReal_mul_I]
  have hneg : ‖-(r : ℂ) * I * Complex.exp (-(θ : ℂ) * I)‖ = |r| := by
    rw [← Complex.ofReal_neg θ]
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_I,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  unfold saddleG
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  have h₁ := norm_principalDilog_le (show _ ≤ 1 by rw [hpos]; exact hr)
  have h₂ := norm_principalDilog_le (show _ ≤ 1 by rw [hneg]; exact hr)
  rw [hpos] at h₁
  rw [hneg] at h₂
  calc _ ≤ _ := add_le_add h₁ h₂
       _ = _ := by ring

theorem continuous_saddleBesselAngular (n : ℕ) {r : ℝ} (hr : |r| ≤ 1) :
    Continuous (fun θ => saddleBesselKernel n (saddleG r θ)) :=
  (continuous_iff_continuousAt.mpr fun z =>
    (analyticAt_saddleBesselKernel n z).continuousAt).comp (continuous_saddleG hr)

/-- The real number `Q` of Lemma 3.4, represented by the entire kernel. -/
def saddleBesselAverage (n : ℕ) (r : ℝ) : ℝ :=
  (((2 * Real.pi : ℂ)⁻¹) *
    ∫ θ in -Real.pi..Real.pi, saddleBesselKernel n (saddleG r θ)).re

/-- Conjugacy across a half-turn implies that the full average is real. -/
theorem saddleBesselAverage_ofReal (n : ℕ) {r : ℝ} (hr : |r| ≤ 1) :
    (saddleBesselAverage n r : ℂ) = ((2 * Real.pi : ℂ)⁻¹) *
      ∫ θ in -Real.pi..Real.pi, saddleBesselKernel n (saddleG r θ) := by
  let F (θ : ℝ) := saddleBesselKernel n (saddleG r θ)
  have hc : Continuous F := continuous_saddleBesselAngular n hr
  have hs : (∫ θ in -Real.pi..(0 : ℝ), F θ) = conj (∫ θ in (0 : ℝ)..Real.pi, F θ) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    have ht := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := Real.pi) F (-Real.pi)
    rw [zero_add, add_neg_cancel] at ht
    rw [← ht]
    apply intervalIntegral.integral_congr
    intro θ _
    have he : F (θ + -Real.pi + Real.pi) = conj (F (θ + -Real.pi)) := by
      simp only [F, saddleG_add_pi hr, saddleBesselKernel_conj]
    rw [neg_add_cancel_right] at he
    simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ) he.symm
  have hi : (∫ θ in -Real.pi..Real.pi, F θ).im = 0 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-Real.pi) 0) (hc.intervalIntegrable 0 Real.pi),
      hs, Complex.add_im, Complex.conj_im, neg_add_cancel]
  change ((saddleBesselAverage n r : ℝ) : ℂ) = ((2 * Real.pi : ℂ)⁻¹) *
    ∫ θ in -Real.pi..Real.pi, F θ
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im, show ((2 * Real.pi : ℂ)⁻¹) = (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) by
      push_cast; rfl, Complex.im_ofReal_mul, hi, mul_zero]

/-- The real part of the average may be evaluated on the central half-arc as in (32). -/
theorem saddleBesselAverage_half_arc (n : ℕ) {r : ℝ} (hr : |r| ≤ 1) :
    saddleBesselAverage n r =
      (((Real.pi : ℂ)⁻¹) * ∫ θ in (-Real.pi / 2)..(Real.pi / 2),
        saddleBesselKernel n (saddleG r θ)).re := by
  let F (θ : ℝ) := saddleBesselKernel n (saddleG r θ)
  have hc : Continuous F := continuous_saddleBesselAngular n hr
  have hp : Function.Periodic (fun θ => (F θ).re) Real.pi := by
    intro θ
    simp [F, saddleG_add_pi hr θ, saddleBesselKernel_conj]
  have h_int (a b : ℝ) : IntervalIntegrable (fun θ => (F θ).re) volume a b :=
    (Complex.continuous_re.comp hc).intervalIntegrable _ _
  have hm := hp.intervalIntegral_add_eq_add (-Real.pi) 0 h_int
  simp only [zero_add, neg_add_cancel] at hm
  have hhalf := hp.intervalIntegral_add_eq (-Real.pi) (-Real.pi / 2)
  rw [neg_add_cancel, show -Real.pi / 2 + Real.pi = Real.pi / 2 by ring] at hhalf
  unfold saddleBesselAverage
  change (((2 * Real.pi : ℂ)⁻¹) * ∫ θ in -Real.pi..Real.pi, F θ).re =
    (((Real.pi : ℂ)⁻¹) * ∫ θ in (-Real.pi / 2)..(Real.pi / 2), F θ).re
  rw [show ((2 * Real.pi : ℂ)⁻¹) = (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    show ((Real.pi : ℂ)⁻¹) = ((Real.pi⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.re_ofReal_mul]
  have hfull : (∫ θ in -Real.pi..Real.pi, F θ).re =
      ∫ θ in -Real.pi..Real.pi, (F θ).re :=
    (intervalIntegral.intervalIntegral_re (hc.intervalIntegrable _ _)).symm
  have hcentral : (∫ θ in (-Real.pi / 2)..(Real.pi / 2), F θ).re =
      ∫ θ in (-Real.pi / 2)..(Real.pi / 2), (F θ).re :=
    (intervalIntegral.intervalIntegral_re (hc.intervalIntegrable _ _)).symm
  rw [hfull, hcentral, hm, hhalf]
  field_simp [Real.pi_ne_zero]
  ring

/-- The cutoff decomposition (37) of the Bessel average against an integrable model. -/
theorem saddleBesselAverage_cutoff_error (n : ℕ) {r c d : ℝ} (hr : |r| ≤ 1)
    (hc : c ≤ Real.pi / 2) (hd : 0 ≤ d) (model : ℝ → ℂ)
    (hm : IntegrableOn model (Ioi 0)) :
    let K (θ : ℝ) := (Real.pi : ℂ)⁻¹ * saddleBesselKernel n (saddleG r θ)
    |saddleBesselAverage n r - (∫ ψ in Ioi 0, model ψ).re| ≤
      ‖(∫ θ in -c..c, K θ) - (∫ ψ in (0 : ℝ)..d, model ψ)‖ +
      ((∫ θ in (-Real.pi / 2)..-c, ‖K θ‖) + (∫ θ in c..(Real.pi / 2), ‖K θ‖)) +
      ‖∫ ψ in Ioi d, model ψ‖ := by
  intro K
  have hK : Continuous K := continuous_const.mul (continuous_saddleBesselAngular n hr)
  have hKint (a b : ℝ) : IntervalIntegrable K volume a b := hK.intervalIntegrable _ _
  have hQ : saddleBesselAverage n r = (∫ θ in (-Real.pi / 2)..(Real.pi / 2), K θ).re := by
    rw [saddleBesselAverage_half_arc n hr]
    dsimp only [K]
    rw [intervalIntegral.integral_const_mul]
  have hKm :
      (∫ θ in (-Real.pi / 2)..(Real.pi / 2), K θ) =
        (∫ θ in -c..c, K θ) +
          ((∫ θ in (-Real.pi / 2)..-c, K θ) + (∫ θ in c..(Real.pi / 2), K θ)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hKint (-Real.pi / 2) c) (hKint c (Real.pi / 2)),
      ← intervalIntegral.integral_add_adjacent_intervals (hKint (-Real.pi / 2) (-c)) (hKint (-c) c)]
    abel
  have hs : (∫ ψ in Ioi 0, model ψ) =
      (∫ ψ in (0 : ℝ)..d, model ψ) + ∫ ψ in Ioi d, model ψ := by
    rw [intervalIntegral.integral_of_le hd, ← Ioc_union_Ioi_eq_Ioi hd,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
    · exact hm.mono_set (fun _ hx => hx.1)
    · exact hm.mono_set (fun _ hx => hd.trans_lt hx)
  let central := (∫ θ in -c..c, K θ) - (∫ ψ in (0 : ℝ)..d, model ψ)
  let outerLeft := ∫ θ in (-Real.pi / 2)..-c, K θ
  let outerRight := ∫ θ in c..(Real.pi / 2), K θ
  let tail := ∫ ψ in Ioi d, model ψ
  have hdiff : saddleBesselAverage n r - (∫ ψ in Ioi 0, model ψ).re =
      (central + (outerLeft + outerRight) - tail).re := by
    rw [hQ, hKm, hs]
    simp only [central, outerLeft, outerRight, tail, Complex.add_re, Complex.sub_re]
    ring
  have hleft : ‖outerLeft‖ ≤ ∫ θ in (-Real.pi / 2)..-c, ‖K θ‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hright : ‖outerRight‖ ≤ ∫ θ in c..(Real.pi / 2), ‖K θ‖ :=
    intervalIntegral.norm_integral_le_integral_norm hc
  rw [hdiff]
  calc
    _ ≤ ‖central + (outerLeft + outerRight) - tail‖ := Complex.abs_re_le_norm _
    _ ≤ (‖central‖ + (‖outerLeft‖ + ‖outerRight‖)) + ‖tail‖ :=
      (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) le_rfl)
    _ ≤ _ := add_le_add (add_le_add le_rfl (add_le_add hleft hright)) le_rfl

end DurfeeCCS.Step08
