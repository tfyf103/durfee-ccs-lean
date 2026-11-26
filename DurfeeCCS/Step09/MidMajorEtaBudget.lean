module

public import DurfeeCCS.Step07.ElementaryBounds
public import DurfeeCCS.Step07.ThetaBoundsTail

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Scalar bounds for the outer angle and model contributions to Lemma 3.8. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Real Set DurfeeCCS.Step07

def midMajorGap (ρ η : ℝ) : ℝ := (η - ρ) ^ 2 / (1 + η ^ 2)

theorem midMajorGap_anti_slope {ρ ρhi η : ℝ} (hρ : ρ ≤ ρhi) (hη : ρhi ≤ η) :
    midMajorGap ρhi η ≤ midMajorGap ρ η := by
  unfold midMajorGap
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (sub_nonneg.mpr hη) (sub_le_sub_left hρ _) 2

theorem midMajorGap_monotone {ρ : ℝ} (hρ : 0 ≤ ρ) :
    MonotoneOn (midMajorGap ρ) (Ici ρ) := by
  intro x hx y _ hxy
  have hx' : ρ ≤ x := hx
  have hy' : ρ ≤ y := hx'.trans hxy
  have hxy₀ : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hfact : 0 ≤ (y - ρ) * (1 + x * ρ) + (x - ρ) * (1 + y * ρ) := by
    have hxp := mul_nonneg (hρ.trans hx') hρ
    have hyp := mul_nonneg (hρ.trans hy') hρ
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hy') (by linarith))
      (mul_nonneg (sub_nonneg.mpr hx') (by linarith))
  unfold midMajorGap
  rw [div_le_div_iff₀ (by positivity) (by positivity), ← sub_nonneg]
  convert mul_nonneg hxy₀ hfact using 1
  ring

/-- Finite-row bounds for the two tails in (59). -/
def midMajorEtaError (t d d₃ : ℝ) : ℝ :=
  96 * sqrt t * exp (-t * d) + 57000 * sqrt t * exp (-t * d₃)

theorem midSqrt_exp_decay {t T d : ℝ} (hT : 0 < T) (ht : T ≤ t)
    (hd : 0 ≤ d) (hcut : (1 / 2 : ℝ) ≤ T * d) :
    sqrt t * exp (-t * d) ≤ sqrt T * exp (-T * d) := by
  have hh := antitoneOn_rpow_mul_exp_neg (q := 1 / 2) (b := d)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hd hT (by rwa [mul_comm])
    (show T ∈ Ici T from le_rfl) (show t ∈ Ici T from ht) ht
  simpa only [sqrt_eq_rpow, mul_comm d t, mul_comm d T, neg_mul] using hh

theorem midMajor_eta_error_mono {t T d d₃ : ℝ} (hT : 0 < T) (ht : T ≤ t)
    (hd : 0 ≤ d) (hd₃ : d ≤ d₃) (hcut : (1 / 2 : ℝ) ≤ T * d) :
    midMajorEtaError t d d₃ ≤ midMajorEtaError T d d₃ := by
  have hc : (1 / 2 : ℝ) ≤ T * d₃ := hcut.trans (mul_le_mul_of_nonneg_left hd₃ hT.le)
  unfold midMajorEtaError
  have h₁ := mul_le_mul_of_nonneg_left (midSqrt_exp_decay hT ht hd hcut) (by norm_num : (0 : ℝ) ≤ 96)
  have h₂ := mul_le_mul_of_nonneg_left (midSqrt_exp_decay hT ht (hd.trans hd₃) hc)
    (by norm_num : (0 : ℝ) ≤ 57000)
  simpa only [mul_assoc] using add_le_add h₁ h₂

def midMajorJBase (t : ℝ) : ℝ :=
  (2 * t)⁻¹ + (1 + (2 * t)⁻¹) * exp (-4 * t)

def midMajorJError (a b x d : ℝ) : ℝ :=
  midMajorJBase (a * x) +
    8 * sqrt (a * x) * (exp (-(b ^ 2 * x / a)) + exp (-d * (a * x)))

theorem midMajorJBase_anti {t T : ℝ} (hT : 0 < T) (ht : T ≤ t) :
    midMajorJBase t ≤ midMajorJBase T := by
  have hInv : (2 * t)⁻¹ ≤ (2 * T)⁻¹ :=
    inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left ht (by norm_num))
  unfold midMajorJBase
  apply add_le_add hInv
  exact mul_le_mul (by linarith only [hInv]) (exp_le_exp.mpr (by linarith only [ht]))
    (exp_pos _).le (by positivity)

private theorem midSqrt_exp_decay_base {x c : ℝ} (hx : 80 ≤ x) (hc : 0 ≤ c)
    (hcut : (1 / 2 : ℝ) ≤ 80 * c) :
    sqrt x * exp (-(c * x)) ≤ sqrt 80 * exp (-(c * 80)) := by
  simpa only [mul_comm c, neg_mul] using
    midSqrt_exp_decay (by norm_num : (0 : ℝ) < 80) hx hc hcut

/-- The model error after inserting the data of any finite row on page 30. -/
theorem midMajor_J_finite_le {a aMin aMax b bMin x d : ℝ}
    (ha₀ : 0 < aMin) (ha : aMin ≤ a) (ha₁ : a ≤ aMax)
    (hb₀ : 0 ≤ bMin) (hb : bMin ≤ b) (hx : 80 ≤ x) (hd : 0 ≤ d)
    (hB : (1 / 2 : ℝ) ≤ 80 * bMin ^ 2 / aMax)
    (hD : (1 / 2 : ℝ) ≤ 80 * aMin * d) :
    midMajorJError a b x d ≤
      midMajorJBase (80 * aMin) +
        8 * sqrt (80 * aMax) * (exp (-(80 * bMin ^ 2 / aMax)) + exp (-(80 * aMin * d))) := by
  have hap := ha₀.trans_le ha
  have hmax := hap.trans_le ha₁
  have hxp : 0 ≤ x := by linarith
  have hbase : 80 * aMin ≤ a * x := by
    nlinarith only [mul_nonneg ha₀.le (sub_nonneg.mpr hx),
      mul_nonneg hxp (sub_nonneg.mpr ha)]
  have hB₀ : bMin ^ 2 / aMax ≤ b ^ 2 / a :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ hb₀ hb 2) hap ha₁
  have hD₀ : d * aMin ≤ d * a := mul_le_mul_of_nonneg_left ha hd
  have hterm {c cMin : ℝ} (hc : 0 ≤ cMin) (hcc : cMin ≤ c)
      (hc₈ : (1 / 2 : ℝ) ≤ 80 * cMin) :
      sqrt (a * x) * exp (-(c * x)) ≤ sqrt (80 * aMax) * exp (-(80 * cMin)) := by
    rw [sqrt_mul hap.le, mul_comm (80 : ℝ) aMax, sqrt_mul hmax.le, mul_assoc, mul_assoc]
    apply mul_le_mul (sqrt_le_sqrt ha₁) _ (by positivity) (sqrt_nonneg _)
    calc
      _ ≤ sqrt x * exp (-(cMin * x)) := by
        apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
        apply exp_le_exp.mpr
        exact neg_le_neg (mul_le_mul_of_nonneg_right hcc hxp)
      _ ≤ _ := by simpa only [mul_comm (80 : ℝ) cMin] using midSqrt_exp_decay_base hx hc hc₈
  have h₁ := hterm (cMin := bMin ^ 2 / aMax) (by positivity) hB₀ (by
    simpa only [← mul_div_assoc] using hB)
  have h₂ := hterm (cMin := d * aMin) (by positivity) hD₀ (by
    convert hD using 1
    ring)
  rw [show -(b ^ 2 / a * x) = -(b ^ 2 * x / a) by ring,
    show -(80 * (bMin ^ 2 / aMax)) = -(80 * bMin ^ 2 / aMax) by ring] at h₁
  rw [show -(d * a * x) = -d * (a * x) by ring,
    show -(80 * (d * aMin)) = -(80 * aMin * d) by ring] at h₂
  have hJ := midMajorJBase_anti (by positivity : 0 < 80 * aMin) hbase
  unfold midMajorJError
  have hsum := add_le_add h₁ h₂
  have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8)
  convert add_le_add hJ hmul using 1 <;> ring

/-- The model error with the growing amplitude cap on the last radius range. -/
theorem midMajor_J_tail_le {a b x d : ℝ} (hx : 80 ≤ x)
    (ha : (5.29406 : ℝ) ≤ a) (hb : (1.48481 : ℝ) ≤ b)
    (hA : a ≤ theta38Growth x) (hd : 0 ≤ d)
    (hD : (1 / 2 : ℝ) ≤ 80 * 5.29406 * d) :
    midMajorJError a b x d ≤
      midMajorJBase (80 * 5.29406) +
        8 * sqrt (theta38Growth x * x) *
          (exp (-((1.48481 : ℝ) ^ 2 * x / theta38Growth x)) +
            exp (-d * (5.29406 * x))) := by
  have hap : 0 < a := by linarith
  have hAp := hap.trans_le hA
  have hxp : 0 ≤ x := by linarith
  have hbase : 80 * (5.29406 : ℝ) ≤ a * x := by
    nlinarith only [mul_nonneg (show (0 : ℝ) ≤ 5.29406 by norm_num) (sub_nonneg.mpr hx),
      mul_nonneg hxp (sub_nonneg.mpr ha)]
  have hB₀ : (1.48481 : ℝ) ^ 2 * x / theta38Growth x ≤ b ^ 2 * x / a :=
    div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hb 2) hxp) hap hA
  have h₁ : sqrt (a * x) * exp (-(b ^ 2 * x / a)) ≤
      sqrt (theta38Growth x * x) * exp (-((1.48481 : ℝ) ^ 2 * x / theta38Growth x)) := by
    exact mul_le_mul (sqrt_le_sqrt (mul_le_mul_of_nonneg_right hA hxp))
      (exp_le_exp.mpr (neg_le_neg hB₀)) (exp_pos _).le (sqrt_nonneg _)
  have hsec : (5.29406 : ℝ) * x ≤ a * x := mul_le_mul_of_nonneg_right ha hxp
  have htail : (1 / 2 : ℝ) ≤ (5.29406 : ℝ) * x * d := by
    refine hD.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith only [hx]) hd
  have h₂ : sqrt (a * x) * exp (-d * (a * x)) ≤
      sqrt (theta38Growth x * x) * exp (-d * (5.29406 * x)) := by
    rw [show -d * (a * x) = -(a * x) * d by ring,
      show -d * (5.29406 * x) = -(5.29406 * x) * d by ring]
    refine (midSqrt_exp_decay (by positivity) hsec hd htail).trans ?_
    gcongr
    exact ha.trans hA
  have hJ := midMajorJBase_anti (by norm_num : (0 : ℝ) < 80 * 5.29406) hbase
  unfold midMajorJError
  have hsum := add_le_add h₁ h₂
  have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8)
  convert add_le_add hJ hmul using 1 <;> ring

end DurfeeCCS.Step09
