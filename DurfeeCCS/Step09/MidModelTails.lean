module

public import DurfeeCCS.Step09.MidModelParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quantitative upper bounds for the two ray remainders of the finite model. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set Filter
open DurfeeCCS.Step08 (norm_verticalPoint_sq)

private theorem sqrt_norm_midModelZ_endpoint {c : ℝ} (hc : c = 0 ∨ c = 3 / 2) :
    Real.sqrt ‖midModelZ c‖ ≤ 1.35 := by
  have hu : ‖midModelZ c‖ ^ 2 ≤ (13 / 4 : ℝ) := by
    rw [norm_verticalPoint_sq]
    rcases hc with rfl | rfl <;> norm_num
  have hn : ‖midModelZ c‖ ≤ (1.35 : ℝ) ^ 2 := by
    by_contra! h
    have hl := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1.35 : ℝ) ^ 2) h.le 2
    norm_num at hl
    linarith
  simpa only [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.35)] using Real.sqrt_le_sqrt hn

private theorem norm_midModelBoundary_le {t ρ c δ : ℝ} (ht : 1 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hc : c = 0 ∨ c = 3 / 2) (hδ : (midModelK t ρ / midModelZ c).re ≤ t - δ) :
    ‖midModelBoundary t ρ c‖ ≤
      Real.exp (t - δ) * (1.35 / t + (1 / 2 + 2 * t) / t ^ 2) := by
  have ht' : 0 ≤ t := zero_le_one.trans ht
  have he : Real.exp (midModelK t ρ / midModelZ c).re ≤ Real.exp (t - δ) :=
    Real.exp_le_exp.mpr hδ
  have hH : ‖midModelH t ρ c‖ ≤ Real.exp (t - δ) * 1.35 := by
    rw [midModelH, norm_mul, norm_midModelSqrt, Complex.norm_exp, mul_comm]
    exact mul_le_mul he (sqrt_norm_midModelZ_endpoint hc) (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  have hH' : ‖midModelHprime t ρ c‖ ≤ Real.exp (t - δ) * (1 / 2 + 2 * t) := by
    have h := norm_midModelHprime_le ht' hρ hρ' c
    refine h.trans (mul_le_mul he ?_ ?_ (Real.exp_nonneg _))
    · have h₁ := midModelDecay_le_one (q := 1 / 2) (by norm_num) c
      have h₂ := midModelDecay_le_one (q := 3 / 2) (by norm_num) c
      have h₁' := mul_le_mul_of_nonneg_left h₁ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have h₂' := mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ 2 * t)
      nlinarith only [h₁', h₂']
    · exact add_nonneg (mul_nonneg (by norm_num) (midModelDecay_nonneg _ _))
        (mul_nonneg (by positivity) (midModelDecay_nonneg _ _))
  unfold midModelBoundary
  apply (norm_sub_le _ _).trans
  simp only [norm_div, norm_mul, norm_midModelOsc, one_mul, norm_pow, norm_midModelD ht']
  calc
    _ ≤ (Real.exp (t - δ) * 1.35) / t + (Real.exp (t - δ) * (1 / 2 + 2 * t)) / t ^ 2 :=
      add_le_add (div_le_div_of_nonneg_right hH ht')
        (div_le_div_of_nonneg_right hH' (sq_nonneg _))
    _ = _ := by ring

private theorem norm_midModelSecond_integral_le {t ρ δ : ℝ} (ht : 1 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hδ : ∀ η ∈ S, (midModelK t ρ / midModelZ η).re ≤ t - δ)
    (hMass : ∀ q : ℝ, 1 < q → (∫ η in S, midModelDecay q η) ≤ 1 + 1 / (q - 1)) :
    ‖∫ η in S, midModelOsc t η * midModelHsecond t ρ η‖ ≤
      Real.exp (t - δ) * (3 / 4 + (10 / 3) * t + (28 / 5) * t ^ 2) := by
  have ht' : 0 ≤ t := zero_le_one.trans ht
  let A := fun η : ℝ => midModelOsc t η * midModelHsecond t ρ η
  let F₃ := fun η : ℝ => (1 / 4 : ℝ) * midModelDecay (3 / 2) η
  let F₅ := fun η : ℝ => (2 * t) * midModelDecay (5 / 2) η
  let F₇ := fun η : ℝ => (4 * t ^ 2) * midModelDecay (7 / 2) η
  let F := fun η : ℝ => F₃ η + F₅ η + F₇ η
  have h₃ : IntegrableOn F₃ S := ((integrable_midModelDecay (by norm_num)).const_mul _).integrableOn
  have h₅ : IntegrableOn F₅ S := ((integrable_midModelDecay (by norm_num)).const_mul _).integrableOn
  have h₇ : IntegrableOn F₇ S := ((integrable_midModelDecay (by norm_num)).const_mul _).integrableOn
  have hi : IntegrableOn F S := (h₃.add h₅).add h₇
  have hb : ∀ η ∈ S, ‖A η‖ ≤ Real.exp (t - δ) * F η := by
    intro η hη
    change ‖midModelOsc t η * midModelHsecond t ρ η‖ ≤ _
    rw [norm_mul, norm_midModelOsc, one_mul]
    refine (norm_midModelHsecond_le ht' hρ hρ' η).trans ?_
    change Real.exp (midModelK t ρ / midModelZ η).re * F η ≤ _
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hδ η hη)) ?_
    dsimp [F, F₃, F₅, F₇]
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (midModelDecay_nonneg _ _))
        (mul_nonneg (by positivity) (midModelDecay_nonneg _ _)))
      (mul_nonneg (by positivity) (midModelDecay_nonneg _ _))
  have htI : IntegrableOn (fun η => Real.exp (t - δ) * F η) S := hi.const_mul _
  have hn : ‖∫ η in S, A η‖ ≤ ∫ η in S, Real.exp (t - δ) * F η := by
    refine norm_integral_le_of_norm_le htI ?_
    filter_upwards [ae_restrict_mem hS] with η hη
    exact hb η hη
  have hm₃ := hMass (3 / 2) (by norm_num)
  have hm₅ := hMass (5 / 2) (by norm_num)
  have hm₇ := hMass (7 / 2) (by norm_num)
  refine hn.trans ?_
  rw [integral_const_mul, show (∫ η in S, F η) =
    (∫ η in S, F₃ η) + (∫ η in S, F₅ η) + (∫ η in S, F₇ η) by
      change (∫ η in S, (F₃ η + F₅ η) + F₇ η) = _
      have h₃₅ : IntegrableOn (fun η => F₃ η + F₅ η) S := h₃.add h₅
      rw [integral_add h₃₅ h₇, integral_add h₃ h₅]]
  unfold F₃ F₅ F₇
  simp_rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  have h₁ := mul_le_mul_of_nonneg_left hm₃ (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  have h₂ := mul_le_mul_of_nonneg_left hm₅ (show 0 ≤ 2 * t by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hm₇ (show 0 ≤ 4 * t ^ 2 by positivity)
  linarith

private theorem midModel_tail_prefactor_lt {t : ℝ} (ht : 1 ≤ t) :
    1.35 / t + (1 / 2 + 2 * t) / t ^ 2 +
      (3 / 4 + (10 / 3) * t + (28 / 5) * t ^ 2) / t ^ 2 < 14 := by
  have hp : 0 < t := zero_lt_one.trans_le ht
  have hq : (1 : ℝ) ≤ t ^ 2 := by
    simpa using pow_le_pow_left₀ zero_le_one ht 2
  have hs : t ≤ t ^ 2 := by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr ht)]
  have he :
      1.35 / t + (1 / 2 + 2 * t) / t ^ 2 +
        (3 / 4 + (10 / 3) * t + (28 / 5) * t ^ 2) / t ^ 2 =
        (1.35 * t + (1 / 2 + 2 * t) + (3 / 4 + (10 / 3) * t + (28 / 5) * t ^ 2)) /
          t ^ 2 := by field_simp
  rw [he, div_lt_iff₀ (sq_pos_of_pos hp)]
  linarith

private theorem midModel_tail_bound {t ρ c δ : ℝ} (ht : 1 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hc : c = 0 ∨ c = 3 / 2) (hδc : (midModelK t ρ / midModelZ c).re ≤ t - δ)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hδ : ∀ η ∈ S, (midModelK t ρ / midModelZ η).re ≤ t - δ)
    (hMass : ∀ q : ℝ, 1 < q → (∫ η in S, midModelDecay q η) ≤ 1 + 1 / (q - 1))
    {sgn : ℂ} (hsgn : ‖sgn‖ = 1) :
    Real.exp (-t) *
      ‖sgn * midModelBoundary t ρ c +
        (∫ η in S, midModelOsc t η * midModelHsecond t ρ η) / midModelD t ^ 2‖ <
        14 * Real.exp (-δ) := by
  have ht' : 0 ≤ t := zero_le_one.trans ht
  have hB := norm_midModelBoundary_le ht hρ hρ' hc hδc
  have hI := norm_midModelSecond_integral_le ht hρ hρ' hS hδ hMass
  have hN := norm_add_le (sgn * midModelBoundary t ρ c)
    ((∫ η in S, midModelOsc t η * midModelHsecond t ρ η) / midModelD t ^ 2)
  simp only [norm_mul, hsgn, one_mul, norm_div, norm_pow, norm_midModelD ht'] at hN
  calc
    _ ≤ Real.exp (-t) *
        (Real.exp (t - δ) * (1.35 / t + (1 / 2 + 2 * t) / t ^ 2) +
          (Real.exp (t - δ) * (3 / 4 + (10 / 3) * t + (28 / 5) * t ^ 2)) / t ^ 2) :=
      mul_le_mul_of_nonneg_left
        (hN.trans (add_le_add hB (div_le_div_of_nonneg_right hI (sq_nonneg _)))) (Real.exp_nonneg _)
    _ = Real.exp (-δ) *
        (1.35 / t + (1 / 2 + 2 * t) / t ^ 2 +
          (3 / 4 + (10 / 3) * t + (28 / 5) * t ^ 2) / t ^ 2) := by
      have he : Real.exp (-t) * Real.exp (t - δ) = Real.exp (-δ) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← he]
      ring
    _ < _ := by
      rw [mul_comm (14 : ℝ)]
      exact mul_lt_mul_of_pos_left (midModel_tail_prefactor_lt ht) (Real.exp_pos _)

theorem midModelTailLeft_bound {t ρ : ℝ} (ht : 1 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) :
    Real.exp (-t) * ‖midModelTailLeft t ρ‖ < 14 * Real.exp (-(t * ρ ^ 2)) := by
  have he (η : ℝ) (hη : η ≤ 0) : (midModelK t ρ / midModelZ η).re ≤ t - t * ρ ^ 2 := by
    rw [re_midModelK_div]
    have h := mul_le_mul_of_nonneg_left (midModel_gap_left hρ hρ' hη) (zero_le_one.trans ht)
    linarith
  have h := midModel_tail_bound ht hρ hρ' (c := 0) (Or.inl rfl) (he 0 le_rfl)
    measurableSet_Iic (fun η hη => he η hη) (fun q hq => integral_midModelDecay_Iic_le hq)
    (sgn := 1) norm_one
  simpa only [one_mul, midModelTailLeft] using h

theorem midModelTailRight_bound {t ρ : ℝ} (ht : 1 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) :
    Real.exp (-t) * ‖midModelTailRight t ρ‖ < 14 * Real.exp (-(t * (3 - 2 * ρ) ^ 2 / 13)) := by
  have he (η : ℝ) (hη : 3 / 2 ≤ η) :
      (midModelK t ρ / midModelZ η).re ≤ t - t * (3 - 2 * ρ) ^ 2 / 13 := by
    rw [re_midModelK_div]
    have h := mul_le_mul_of_nonneg_left (midModel_gap_right hρ hρ' hη) (zero_le_one.trans ht)
    linarith
  have h := midModel_tail_bound ht hρ hρ' (c := 3 / 2) (Or.inr rfl) (he (3 / 2) le_rfl)
    measurableSet_Ioi (fun η hη => he η hη.le) (fun q hq => integral_midModelDecay_shift_le hq)
    (sgn := -1) (by simp)
  simpa only [neg_one_mul, midModelTailRight] using h

end DurfeeCCS.Step09
