module

public import DurfeeCCS.Step06.BesselSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The three integral representations in (10). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step06

open Nat Set intervalIntegral

private def trigMoment (n m : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi, Real.cos t ^ n * Real.sin t ^ (2 * m)

private theorem cosineMoment_step (n : ℕ) : trigMoment (n + 2) 0 =
    ((n : ℝ) + 1) / ((n : ℝ) + 2) * trigMoment n 0 := by
  simpa [trigMoment] using integral_cos_pow (a := 0) (b := Real.pi) n

private theorem trigMoment_step (n m : ℕ) :
    trigMoment n (m + 1) = trigMoment n m - trigMoment (n + 2) m := by
  have h (k : ℕ) : IntervalIntegrable (fun t => Real.cos t ^ k * Real.sin t ^ (2 * m))
      MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  simp only [trigMoment]
  rw [← integral_sub (h n) (h (n + 2))]
  apply integral_congr
  intro t _
  dsimp only
  rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add, Real.sin_sq, pow_add]
  ring

private theorem cosineMoment_even (k : ℕ) : trigMoment (2 * k) 0 =
    Real.pi * ((2 * k).factorial : ℝ) / ((4 : ℝ) ^ k * (k.factorial : ℝ) ^ 2) := by
  induction k with
  | zero => simp [trigMoment]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, cosineMoment_step, ih,
      Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
      Nat.factorial_succ k, pow_succ (4 : ℝ) k]
    push_cast
    field_simp [show (k.factorial : ℝ) ≠ 0 by positivity]
    ring

private theorem cosineMoment_odd (k : ℕ) : trigMoment (2 * k + 1) 0 = 0 := by
  induction k with
  | zero => simp [trigMoment, integral_cos]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, cosineMoment_step, ih,
      mul_zero]

private theorem trigMoment_even (k m : ℕ) : trigMoment (2 * k) m =
    Real.pi * ((2 * k).factorial : ℝ) * ((2 * m).factorial : ℝ) /
      ((4 : ℝ) ^ (k + m) * (k.factorial : ℝ) * (m.factorial : ℝ) * ((k + m).factorial : ℝ)) := by
  induction m generalizing k with
  | zero => simpa [pow_two, mul_assoc] using cosineMoment_even k
  | succ m ih =>
    rw [trigMoment_step, show 2 * k + 2 = 2 * (k + 1) by omega, ih k, ih (k + 1)]
    have hkm : k + 1 + m = k + m + 1 := by omega
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, show 2 * (m + 1) = 2 * m + 2 by omega,
      show k + (m + 1) = k + m + 1 by omega, hkm,
      Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
      Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m),
      Nat.factorial_succ k, Nat.factorial_succ m, Nat.factorial_succ (k + m),
      pow_succ (4 : ℝ) (k + m)]
    push_cast
    field_simp [show (k.factorial : ℝ) ≠ 0 by positivity,
      show (m.factorial : ℝ) ≠ 0 by positivity,
      show ((k + m).factorial : ℝ) ≠ 0 by positivity]
    ring

private theorem trigMoment_odd (k m : ℕ) : trigMoment (2 * k + 1) m = 0 := by
  induction m generalizing k with
  | zero => exact cosineMoment_odd k
  | succ m ih =>
    rw [trigMoment_step, show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega, ih k,
      ih (k + 1), sub_self]

/-- Termwise integration of the exponential series against the trigonometric weight. -/
private theorem hasSum_exp_trigMoment (m : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ ↦ z ^ n / (n.factorial : ℂ) * (trigMoment n m : ℂ))
      (∫ t in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos t : ℂ)) *
        (Real.sin t : ℂ) ^ (2 * m)) := by
  let F (n : ℕ) (t : ℝ) : ℂ :=
    (z * (Real.cos t : ℂ)) ^ n / (n.factorial : ℂ) * (Real.sin t : ℂ) ^ (2 * m)
  let M (n : ℕ) : ℝ := ‖z‖ ^ n / (n.factorial : ℝ)
  have hF (n : ℕ) : Continuous (F n) := by dsimp [F]; fun_prop
  have hbound (n : ℕ) (t : ℝ) : ‖F n t‖ ≤ M n := by
    simp only [F, M, norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_natCast]
    calc
      _ ≤ ((‖z‖ * 1) ^ n / (n.factorial : ℝ)) * 1 ^ (2 * m) := by
        gcongr
        · exact Real.abs_cos_le_one t
        · exact Real.abs_sin_le_one t
      _ = _ := by simp
  have hsum : Summable M := Real.summable_pow_div_factorial ‖z‖
  have hlim (t : ℝ) : HasSum (fun n => F n t)
      (Complex.exp (z * (Real.cos t : ℂ)) * (Real.sin t : ℂ) ^ (2 * m)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp (z * (Real.cos t : ℂ))).mul_right _
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := Real.pi) (μ := MeasureTheory.volume) (F := F)
    (fun n _ => M n) (fun n => (hF n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (fun t _ => hbound n t))
    (Filter.Eventually.of_forall (fun _ _ => hsum)) intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ => hlim t))
  apply h.congr_fun
  intro n
  symm
  calc
    (∫ t in (0 : ℝ)..Real.pi, F n t) =
        ∫ t in (0 : ℝ)..Real.pi, z ^ n / (n.factorial : ℂ) *
          (((Real.cos t ^ n * Real.sin t ^ (2 * m)) : ℝ) : ℂ) := by
      apply integral_congr
      intro t _
      simp only [F, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    _ = _ := by rw [integral_const_mul, integral_ofReal, trigMoment]

/-- Normalization factor for the Bessel integral with trigonometric weight. -/
def besselIntegralFactor (m : ℕ) (z : ℂ) : ℂ :=
  (z / 2) ^ m * ((4 : ℂ) ^ m * (m.factorial : ℂ)) /
    ((Real.pi : ℂ) * ((2 * m).factorial : ℂ))

theorem besselI_eq_trigIntegral (m : ℕ) (z : ℂ) :
    besselI m z = besselIntegralFactor m z *
      ∫ t in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos t : ℂ)) *
        (Real.sin t : ℂ) ^ (2 * m) := by
  have h := (Nat.divModEquiv 2).symm.hasSum_iff.mpr (hasSum_exp_trigMoment m z)
  dsimp [Function.comp_def] at h
  have he : HasSum (fun k : ℕ ↦ z ^ (2 * k) / ((2 * k).factorial : ℂ) *
      (trigMoment (2 * k) m : ℂ))
      (∫ t in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos t : ℂ)) *
        (Real.sin t : ℂ) ^ (2 * m)) := by
    refine h.prod_fiberwise fun k => ?_
    convert hasSum_fintype (_ : Fin 2 → ℂ) using 1
    rw [Fin.sum_univ_two]
    simp [Nat.mul_comm k 2, trigMoment_odd]
  unfold besselI
  apply HasSum.tsum_eq
  apply (he.mul_left (besselIntegralFactor m z)).congr_fun
  intro k
  symm
  rw [trigMoment_even]
  push_cast
  rw [besselITerm, pow_add (z / 2), pow_mul (z / 2), div_pow z 2, pow_mul z, pow_add (4 : ℂ)]
  norm_num [besselIntegralFactor, div_pow]
  field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero,
    show (k.factorial : ℂ) ≠ 0 by exact_mod_cast k.factorial_ne_zero,
    show (m.factorial : ℂ) ≠ 0 by exact_mod_cast m.factorial_ne_zero,
    show ((2 * k).factorial : ℂ) ≠ 0 by exact_mod_cast (2 * k).factorial_ne_zero,
    show ((2 * m).factorial : ℂ) ≠ 0 by exact_mod_cast (2 * m).factorial_ne_zero]

private theorem integral_comp_cos (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..Real.pi, f (Real.cos t) * (Real.sin t : ℂ)) = ∫ t in (-1 : ℝ)..1, f t := by
  calc
    _ = ∫ t in Real.pi..(0 : ℝ), (-Real.sin t) • f (Real.cos t) := by
      rw [integral_symm]
      simp [Complex.real_smul, integral_neg, mul_comm]
    _ = _ := by
      simpa using integral_deriv_smul_comp (a := Real.pi) (b := 0)
        (fun t _ => Real.hasDerivAt_cos t) Real.continuous_sin.neg.continuousOn hf

private theorem bessel_trig_substitution (m : ℕ) (z : ℂ) :
    (∫ t in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos t : ℂ)) *
      (Real.sin t : ℂ) ^ (2 * (m + 1))) =
      ∫ t in (-1 : ℝ)..1, Complex.exp (z * (t : ℂ)) *
        (Real.sqrt (1 - t ^ 2) : ℂ) ^ (2 * m + 1) := by
  rw [← integral_comp_cos (fun t : ℝ => Complex.exp (z * (t : ℂ)) *
    (Real.sqrt (1 - t ^ 2) : ℂ) ^ (2 * m + 1)) (by fun_prop)]
  apply integral_congr
  intro t ht
  dsimp only
  rw [uIcc_of_le Real.pi_pos.le, mem_Icc] at ht
  rw [← Real.sin_eq_sqrt_one_sub_cos_sq ht.1 ht.2,
    show 2 * (m + 1) = (2 * m + 1) + 1 by omega, pow_succ, mul_assoc]

theorem besselI_zero_integral (z : ℂ) :
    besselI 0 z = (Real.pi : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos t : ℂ)) := by
  simpa [besselIntegralFactor] using besselI_eq_trigIntegral 0 z

theorem besselI_zero_integral_segment (z : ℂ) :
    besselI 0 z = (Real.pi : ℂ)⁻¹ *
      ∫ t in (-1 : ℝ)..1, Complex.exp (z * (t : ℂ)) * (Real.sqrt (1 - t ^ 2) : ℂ)⁻¹ := by
  rw [besselI_zero_integral]
  congr 1
  let g (t : ℝ) := Complex.exp (z * (t : ℂ)) * (Real.sqrt (1 - t ^ 2) : ℂ)⁻¹
  have h := integral_deriv_smul_comp_of_deriv_nonpos (a := Real.pi) (b := 0) (g := g)
    Real.continuous_cos.continuousOn (fun t _ => Real.hasDerivAt_cos t) (by
      intro t ht
      rw [min_eq_right Real.pi_pos.le, max_eq_left Real.pi_pos.le] at ht
      exact neg_nonpos.mpr (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).le)
  calc
    _ = ∫ t in Real.pi..(0 : ℝ), (-Real.sin t) • (g ∘ Real.cos) t := by
      rw [integral_symm 0 Real.pi, ← integral_neg]
      apply integral_congr_Ioo_of_le Real.pi_pos.le
      intro t ht
      have hsin : (Real.sin t : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
      simp only [g, Function.comp_apply, neg_smul, neg_neg, Complex.real_smul]
      rw [← Real.sin_eq_sqrt_one_sub_cos_sq ht.1.le ht.2.le]
      field_simp
    _ = _ := by simpa [g] using h

theorem besselI_one_integral (z : ℂ) :
    besselI 1 z = (z / (Real.pi : ℂ)) *
      ∫ t in (-1 : ℝ)..1, Complex.exp (z * (t : ℂ)) * (Real.sqrt (1 - t ^ 2) : ℂ) := by
  rw [besselI_eq_trigIntegral, bessel_trig_substitution 0 z]
  congr 1
  · unfold besselIntegralFactor
    norm_num
    ring
  · simp

theorem besselI_two_integral (z : ℂ) :
    besselI 2 z = (z ^ 2 / (3 * (Real.pi : ℂ))) *
      ∫ t in (-1 : ℝ)..1, Complex.exp (z * (t : ℂ)) * ((1 - t ^ 2) ^ (3 / 2 : ℝ) : ℝ) := by
  rw [besselI_eq_trigIntegral, bessel_trig_substitution 1 z]
  congr 1
  · unfold besselIntegralFactor
    norm_num
    ring
  · apply integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at ht
    have h : 0 ≤ 1 - t ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by linarith : 0 ≤ 1 + t)]
    rw [← Complex.ofReal_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h]
    norm_num

end DurfeeCCS.Step06
