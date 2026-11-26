module

public import DurfeeCCS.Step09.MidModelSeries
public import DurfeeCCS.Step09.MidModelTails
public import DurfeeCCS.Step09.MidModelFourierPaper
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The model approximation with the constants and hypotheses of Lemma 3.7. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex
open DurfeeCCS.Step08 (norm_verticalPoint_sq verticalPoint_re)

private theorem norm_midModelZ (ρ : ℝ) : ‖midModelZ ρ‖ = Real.sqrt (1 + ρ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (midModelZ ρ)), norm_verticalPoint_sq, one_pow]

private theorem norm_midModelExpFactor (t ρ : ℝ) :
    ‖Complex.exp (-4 * (t : ℂ) * midModelZ ρ)‖ = Real.exp (-4 * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

private theorem midModelJInfinity_normalized {t : ℝ} (ht : 0 < t) (ρ : ℝ) :
    (Real.sqrt (t / Real.pi) : ℂ) * midModelJInfinity t ρ / midModelZ ρ - 1 =
      -(1 / (2 * (t : ℂ) * midModelZ ρ)) -
        (1 + 1 / (2 * (t : ℂ) * midModelZ ρ)) * Complex.exp (-4 * (t : ℂ) * midModelZ ρ) := by
  have hz := midModelZ_ne_zero ρ
  have hp : Real.sqrt (t / Real.pi) * Real.sqrt (Real.pi / t) = 1 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ t / Real.pi),
      show t / Real.pi * (Real.pi / t) = 1 by field_simp, Real.sqrt_one]
  have hp' : (Real.sqrt (t / Real.pi) : ℂ) * (Real.sqrt (Real.pi / t) : ℂ) = 1 := by
    exact_mod_cast hp
  rw [midModelJInfinity_eq ht, ← mul_assoc, hp', one_mul]
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  field_simp
  ring

private theorem norm_midModelJInfinity_normalized_le {t : ℝ} (ht : 0 < t) (ρ : ℝ) :
    ‖(Real.sqrt (t / Real.pi) : ℂ) * midModelJInfinity t ρ / midModelZ ρ - 1‖ ≤
      1 / (2 * t * Real.sqrt (1 + ρ ^ 2)) +
        (1 + 1 / (2 * t * Real.sqrt (1 + ρ ^ 2))) * Real.exp (-4 * t) := by
  let a : ℂ := 1 / (2 * (t : ℂ) * midModelZ ρ)
  let A : ℝ := 1 / (2 * t * Real.sqrt (1 + ρ ^ 2))
  have ha : ‖a‖ = A := by
    unfold a A
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_midModelZ]
    norm_num [abs_of_pos ht]
  have hOne : ‖1 + a‖ ≤ 1 + A := by
    simpa only [norm_one, ha] using norm_add_le (1 : ℂ) a
  rw [midModelJInfinity_normalized ht ρ]
  change ‖-a - (1 + a) * exp (-4 * (t : ℂ) * midModelZ ρ)‖ ≤ _
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, ha, norm_mul, norm_midModelExpFactor]
  exact add_le_add_right (mul_le_mul_of_nonneg_right hOne (Real.exp_nonneg _)) A

private theorem midModel_tail_normalization_le {t ρ : ℝ} (ht : 1 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) :
    ‖(Real.sqrt (t / Real.pi) : ℂ) * (midModelJ t ρ - midModelJInfinity t ρ) / midModelZ ρ‖ ≤
      8 * Real.sqrt t * (Real.exp (-(t * ρ ^ 2)) + Real.exp (-(t * (3 - 2 * ρ) ^ 2 / 13))) := by
  let T := Real.exp (-(t * ρ ^ 2)) + Real.exp (-(t * (3 - 2 * ρ) ^ 2 / 13))
  have ht' : 0 < t := zero_lt_one.trans_le ht
  have hz : 1 ≤ ‖midModelZ ρ‖ := one_le_norm_midModelZ ρ
  have hnorm : ‖midModelJ t ρ - midModelJInfinity t ρ‖ ≤ 14 * T := by
    rw [norm_sub_rev, midModelJInfinity_sub_eq_tails ht' hρ hρ', norm_mul, norm_midModelWeight]
    have h := mul_le_mul_of_nonneg_left (norm_add_le (midModelTailLeft t ρ)
      (midModelTailRight t ρ)) (Real.exp_nonneg (-t))
    rw [mul_add] at h
    have h' := add_lt_add (midModelTailLeft_bound ht hρ hρ') (midModelTailRight_bound ht hρ hρ')
    exact h.trans ((le_of_lt h').trans_eq (by unfold T; ring))
  have hp : (14 : ℝ) ≤ 8 * Real.sqrt Real.pi := by
    have hl : ((14 / 8 : ℝ) ^ 2) ≤ Real.pi := by linarith [Real.pi_gt_d2]
    linarith [Real.le_sqrt_of_sq_le hl]
  rw [norm_div, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (t / Real.pi) * ‖midModelJ t ρ - midModelJInfinity t ρ‖ :=
      div_le_self (by positivity) hz
    _ ≤ Real.sqrt (t / Real.pi) * (14 * T) :=
      mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
    _ = (14 / Real.sqrt Real.pi) * Real.sqrt t * T := by
      rw [Real.sqrt_div ht'.le]
      ring
    _ ≤ _ := by
      have he := (div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)).mpr hp
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg _))
        (by unfold T; positivity)

/-- Lemma 3.7, with the two-sided finite-interval correction and the exact half-integer model. -/
theorem lemma37 {t ρ : ℝ} (ht : 1 ≤ t) (hρ : 0 < ρ) (hρ' : ρ < 1) :
    let A := 1 / (2 * t * Real.sqrt (1 + ρ ^ 2))
    ‖(Real.sqrt (t / Real.pi) : ℂ) * midModelJ t ρ / midModelZ ρ - 1‖ ≤
      A + (1 + A) * Real.exp (-4 * t) + 8 * Real.sqrt t *
        (Real.exp (-(t * ρ ^ 2)) + Real.exp (-(t * (3 - 2 * ρ) ^ 2 / 13))) := by
  let sqrtNormalize := (Real.sqrt (t / Real.pi) : ℂ)
  have he : sqrtNormalize * midModelJ t ρ / midModelZ ρ - 1 =
      (sqrtNormalize * midModelJInfinity t ρ / midModelZ ρ - 1) +
        sqrtNormalize * (midModelJ t ρ - midModelJInfinity t ρ) / midModelZ ρ := by
    ring
  change ‖sqrtNormalize * midModelJ t ρ / midModelZ ρ - 1‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_midModelJInfinity_normalized_le (zero_lt_one.trans_le ht) ρ)
      (midModel_tail_normalization_le ht hρ.le hρ'.le))

end DurfeeCCS.Step09
