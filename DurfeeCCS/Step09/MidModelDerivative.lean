module

public import DurfeeCCS.Step09.MidModelBase
public import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Two derivatives of the H function in Lemma 3.7. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set
open DurfeeCCS.Step08 (verticalPoint verticalPoint_re)

def midModelHprime (t ρ η : ℝ) : ℂ :=
  I * midModelH t ρ η / midModelZ η * (1 / 2 - midModelK t ρ / midModelZ η)

def midModelHsecond (t ρ η : ℝ) : ℂ :=
  midModelH t ρ η / midModelZ η ^ 2 *
    (1 / 4 - midModelK t ρ / midModelZ η - (midModelK t ρ / midModelZ η) ^ 2)

theorem midModelZ_slit (η : ℝ) : midModelZ η ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp

theorem hasDerivAt_midModelZ (η : ℝ) : HasDerivAt midModelZ I η := by
  change HasDerivAt (fun x : ℝ => (1 : ℂ) + (x : ℂ) * I) I η
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
    (((Complex.ofRealCLM.hasDerivAt (x := η)).mul_const I).const_add (1 : ℂ))

theorem continuous_midModelZ : Continuous midModelZ :=
  continuous_iff_continuousAt.mpr fun η => (hasDerivAt_midModelZ η).continuousAt

theorem hasDerivAt_midModelSqrt (η : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.sqrt (midModelZ x))
      ((midModelZ η).sqrt / (2 * midModelZ η) * I) η := by
  have hd := (Complex.hasDerivAt_sqrt (midModelZ_slit η)).comp η (hasDerivAt_midModelZ η)
  have hp : midModelZ η ^ (-1 / 2 : ℂ) = (midModelZ η).sqrt / midModelZ η := by
    rw [show (-1 / 2 : ℂ) = (2 : ℂ)⁻¹ - 1 by norm_num,
      Complex.cpow_sub _ _ (midModelZ_ne_zero η), Complex.cpow_one]
    rfl
  rw [hp] at hd
  convert hd using 1
  · rfl
  · ring

theorem hasDerivAt_midModelExp (K : ℂ) (η : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (K / midModelZ x))
      (Complex.exp (K / midModelZ η) * (-K * I / midModelZ η ^ 2)) η := by
  have hd := ((hasDerivAt_const η K).div (hasDerivAt_midModelZ η)
    (midModelZ_ne_zero η)).cexp
  convert hd using 1
  simp only [Pi.div_apply]
  ring

theorem hasDerivAt_midModelH (t ρ η : ℝ) :
    HasDerivAt (midModelH t ρ) (midModelHprime t ρ η) η := by
  let z := midModelZ η
  let K := midModelK t ρ
  have hd := (hasDerivAt_midModelSqrt η).mul (hasDerivAt_midModelExp K η)
  change HasDerivAt (midModelH t ρ) _ η at hd
  convert hd using 1
  unfold midModelHprime midModelH
  field_simp [midModelZ_ne_zero η]
  ring

theorem hasDerivAt_midModelHprime (t ρ η : ℝ) :
    HasDerivAt (midModelHprime t ρ) (midModelHsecond t ρ η) η := by
  let K := midModelK t ρ
  let z := midModelZ η
  have hz : z ≠ 0 := midModelZ_ne_zero η
  have hF := ((hasDerivAt_midModelH t ρ η).const_mul I).div (hasDerivAt_midModelZ η) hz
  have hG := ((hasDerivAt_const η K).div (hasDerivAt_midModelZ η) hz).const_sub (1 / 2)
  have hd := hF.mul hG
  change HasDerivAt (midModelHprime t ρ) _ η at hd
  convert hd using 1
  unfold midModelHsecond midModelHprime
  simp only [Pi.div_apply, K]
  field_simp [midModelZ_ne_zero η]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem continuous_midModelH (t ρ : ℝ) : Continuous (midModelH t ρ) :=
  continuous_iff_continuousAt.mpr fun η => (hasDerivAt_midModelH t ρ η).continuousAt

theorem continuous_midModelHprime (t ρ : ℝ) : Continuous (midModelHprime t ρ) :=
  continuous_iff_continuousAt.mpr fun η => (hasDerivAt_midModelHprime t ρ η).continuousAt

theorem continuous_midModelHsecond (t ρ : ℝ) : Continuous (midModelHsecond t ρ) := by
  unfold midModelHsecond
  have hZ := continuous_midModelZ
  have hH := continuous_midModelH t ρ
  exact (hH.div (hZ.pow 2) (fun x => pow_ne_zero _ (midModelZ_ne_zero x))).mul
    ((continuous_const.sub (continuous_const.div hZ midModelZ_ne_zero)).sub
      ((continuous_const.div hZ midModelZ_ne_zero).pow 2))

theorem norm_midModelSqrt (η : ℝ) : ‖(midModelZ η).sqrt‖ = Real.sqrt ‖midModelZ η‖ := by
  have hp : ‖(midModelZ η).sqrt‖ ^ 2 = ‖midModelZ η‖ := by
    rw [← norm_pow, DurfeeCCS.Step06.principalSqrt_sq]
  nlinarith [Real.sq_sqrt (norm_nonneg (midModelZ η)), Real.sqrt_nonneg ‖midModelZ η‖,
    norm_nonneg (midModelZ η).sqrt]

def midModelDecay (q η : ℝ) : ℝ := ‖midModelZ η‖ ^ (-q)

theorem midModelDecay_nonneg (q η : ℝ) : 0 ≤ midModelDecay q η :=
  Real.rpow_nonneg (norm_nonneg _) _

theorem norm_midModelZ_pos (η : ℝ) : 0 < ‖midModelZ η‖ :=
  lt_of_lt_of_le zero_lt_one (one_le_norm_midModelZ η)

theorem midModelDecay_mul_inv (q η : ℝ) :
    midModelDecay q η * ‖midModelZ η‖⁻¹ = midModelDecay (q + 1) η := by
  unfold midModelDecay
  rw [show -(q + 1) = -q + (-1) by ring, Real.rpow_add (norm_midModelZ_pos η),
    Real.rpow_neg_one]

theorem norm_midModelSqrt_div_pow (η : ℝ) (m : ℕ) :
    ‖(midModelZ η).sqrt / midModelZ η ^ m‖ = midModelDecay ((m : ℝ) - 1 / 2) η := by
  rw [midModelDecay, norm_div, norm_pow, norm_midModelSqrt, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_sub (norm_midModelZ_pos η)]
  congr 1
  ring

theorem norm_midModelHprime_le {t ρ : ℝ} (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (η : ℝ) :
    ‖midModelHprime t ρ η‖ ≤ Real.exp (midModelK t ρ / midModelZ η).re *
      ((1 / 2) * midModelDecay (1 / 2) η + 2 * t * midModelDecay (3 / 2) η) := by
  let z := midModelZ η
  let x := midModelK t ρ / z
  have hz := norm_midModelZ_pos η
  have hk : ‖midModelK t ρ‖ ≤ 2 * t := by
    rw [norm_midModelK, abs_of_nonneg ht]
    have hh : ρ ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hρ hρ' 2
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hh)]
  have hx : ‖x‖ ≤ 2 * t * ‖z‖⁻¹ := by
    rw [show x = midModelK t ρ / z by rfl, norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hk (by positivity)
  have hsub : ‖(1 / 2 : ℂ) - x‖ ≤ (1 / 2 : ℝ) + 2 * t * ‖z‖⁻¹ := by
    have h := norm_sub_le (1 / 2 : ℂ) x
    norm_num at h
    linarith
  have hpre : ‖I * midModelH t ρ η / z‖ =
      Real.exp x.re * midModelDecay (1 / 2) η := by
    rw [midModelH, norm_div, norm_mul, Complex.norm_I, one_mul, norm_mul,
      Complex.norm_exp]
    change (‖z.sqrt‖ * Real.exp x.re) / ‖z‖ = _
    rw [mul_comm ‖z.sqrt‖, mul_div_assoc, ← norm_div]
    congr 1
    simpa only [pow_one, Nat.cast_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      norm_midModelSqrt_div_pow η 1
  change ‖I * midModelH t ρ η / z * ((1 / 2 : ℂ) - x)‖ ≤
    Real.exp x.re * _
  rw [norm_mul, hpre]
  apply (mul_le_mul_of_nonneg_left hsub
    (mul_nonneg (Real.exp_nonneg _) (midModelDecay_nonneg _ _))).trans_eq
  calc
    _ = Real.exp x.re * ((1 / 2) * midModelDecay (1 / 2) η +
        (2 * t) * (midModelDecay (1 / 2) η * ‖z‖⁻¹)) := by ring
    _ = _ := by rw [midModelDecay_mul_inv]; norm_num

theorem norm_midModelHsecond_le {t ρ : ℝ} (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (η : ℝ) :
    ‖midModelHsecond t ρ η‖ ≤ Real.exp (midModelK t ρ / midModelZ η).re *
      ((1 / 4) * midModelDecay (3 / 2) η + 2 * t * midModelDecay (5 / 2) η +
        4 * t ^ 2 * midModelDecay (7 / 2) η) := by
  let z := midModelZ η
  let x := midModelK t ρ / z
  have hz := norm_midModelZ_pos η
  have hk : ‖midModelK t ρ‖ ≤ 2 * t := by
    rw [norm_midModelK, abs_of_nonneg ht]
    have hh : ρ ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hρ hρ' 2
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hh)]
  have hx : ‖x‖ ≤ 2 * t * ‖z‖⁻¹ := by
    rw [show x = midModelK t ρ / z by rfl, norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hk (by positivity)
  have hsub : ‖(1 / 4 : ℂ) - x - x ^ 2‖ ≤
      (1 / 4 : ℝ) + 2 * t * ‖z‖⁻¹ + 4 * t ^ 2 * (‖z‖⁻¹) ^ 2 := by
    have h := norm_sub_le (1 / 4 : ℂ) x
    have h' := norm_sub_le ((1 / 4 : ℂ) - x) (x ^ 2)
    have hx' := pow_le_pow_left₀ (norm_nonneg _) hx 2
    norm_num at h
    rw [norm_pow] at h'
    calc
      _ ≤ (1 / 4 : ℝ) + (2 * t * ‖z‖⁻¹) + (2 * t * ‖z‖⁻¹) ^ 2 := by linarith
      _ = _ := by ring
  have hpre : ‖midModelH t ρ η / z ^ 2‖ =
      Real.exp x.re * midModelDecay (3 / 2) η := by
    rw [midModelH, norm_div, norm_mul, Complex.norm_exp]
    change (‖z.sqrt‖ * Real.exp x.re) / ‖z ^ 2‖ = _
    rw [mul_comm ‖z.sqrt‖, mul_div_assoc, ← norm_div]
    congr 1
    simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 / 2 = 3 / 2 by norm_num] using
      norm_midModelSqrt_div_pow η 2
  change ‖midModelH t ρ η / z ^ 2 * ((1 / 4 : ℂ) - x - x ^ 2)‖ ≤ Real.exp x.re * _
  rw [norm_mul, hpre]
  apply (mul_le_mul_of_nonneg_left hsub
    (mul_nonneg (Real.exp_nonneg _) (midModelDecay_nonneg _ _))).trans_eq
  calc
    _ = Real.exp x.re * ((1 / 4) * midModelDecay (3 / 2) η +
        (2 * t) * (midModelDecay (3 / 2) η * ‖z‖⁻¹) +
        (4 * t ^ 2) * ((midModelDecay (3 / 2) η * ‖z‖⁻¹) * ‖z‖⁻¹)) := by ring
    _ = _ := by rw [midModelDecay_mul_inv, midModelDecay_mul_inv]; norm_num

end DurfeeCCS.Step09
