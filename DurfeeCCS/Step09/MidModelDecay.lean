module

public import DurfeeCCS.Step09.MidModelDerivative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integrable majorants on the real line for the differentiated model. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set Filter
open DurfeeCCS.Step08 (norm_verticalPoint_sq)

theorem continuous_midModelDecay (q : ℝ) : Continuous (midModelDecay q) := by
  exact continuous_midModelZ.norm.rpow_const (fun x => Or.inl (norm_midModelZ_pos x).ne')

theorem midModelDecay_even (q : ℝ) : Function.Even (midModelDecay q) := by
  intro x
  have e : ‖midModelZ (-x)‖ = ‖midModelZ x‖ := by
    have h : ‖midModelZ (-x)‖ ^ 2 = ‖midModelZ x‖ ^ 2 := by
      rw [norm_verticalPoint_sq, norm_verticalPoint_sq, neg_sq]
    nlinarith [norm_nonneg (midModelZ (-x)), norm_nonneg (midModelZ x)]
  rw [midModelDecay, midModelDecay, e]

theorem midModelDecay_le_one {q : ℝ} (hq : 0 ≤ q) (η : ℝ) : midModelDecay q η ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_norm_midModelZ η) (neg_nonpos.mpr hq)

theorem midModelDecay_mono {q q' : ℝ} (h : q ≤ q') (η : ℝ) :
    midModelDecay q' η ≤ midModelDecay q η :=
  Real.rpow_le_rpow_of_exponent_le (one_le_norm_midModelZ η) (neg_le_neg h)

private theorem midModelDecay_le_rpow {q : ℝ} (hq : 0 ≤ q) {η : ℝ} (hη : 0 < η) :
    midModelDecay q η ≤ η ^ (-q) := by
  have hz := abs_le_norm_midModelZ η
  rw [abs_of_pos hη] at hz
  exact Real.rpow_le_rpow_of_nonpos hη hz (neg_nonpos.mpr hq)

private theorem integrableOn_midModelDecay_Ioi {q : ℝ} (hq : 1 < q) :
    IntegrableOn (midModelDecay q) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  refine (continuous_midModelDecay q).continuousOn.integrableOn_Icc |>.mono_set
    (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1) |>.union ?_
  refine (integrableOn_Ioi_rpow_of_lt (by linarith : -q < -1) zero_lt_one).mono'
    (continuous_midModelDecay q).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with x hx
  rw [Real.norm_of_nonneg (midModelDecay_nonneg q x)]
  exact midModelDecay_le_rpow (by linarith) (zero_lt_one.trans hx)

theorem integrable_midModelDecay {q : ℝ} (hq : 1 < q) : Integrable (midModelDecay q) := by
  have hpos := integrableOn_midModelDecay_Ioi hq
  have hneg : IntegrableOn (midModelDecay q) (Iic 0) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    have hp : IntegrableOn (midModelDecay q) (Ioi (-(0 : ℝ))) := by simpa using hpos
    have h := hp.comp_neg_Iio
    have he : (fun x : ℝ => midModelDecay q (-x)) = midModelDecay q :=
      funext (midModelDecay_even q)
    simpa only [he] using h
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hneg.union hpos

theorem integral_midModelDecay_Ioi_le {q : ℝ} (hq : 1 < q) :
    (∫ η in Ioi (0 : ℝ), midModelDecay q η) ≤ 1 + 1 / (q - 1) := by
  have hInt := integrable_midModelDecay hq
  have h₁ : (∫ η in Ioc (0 : ℝ) 1, midModelDecay q η) ≤ 1 := by
    calc
      _ ≤ ∫ _ : ℝ in Ioc (0 : ℝ) 1, (1 : ℝ) :=
        setIntegral_mono_on hInt.integrableOn (by simp) measurableSet_Ioc
          (fun x _ => midModelDecay_le_one (by linarith) x)
      _ = _ := by simp
  have h₂ : (∫ η in Ioi (1 : ℝ), midModelDecay q η) ≤ 1 / (q - 1) := by
    calc
      _ ≤ ∫ η in Ioi (1 : ℝ), η ^ (-q) :=
        setIntegral_mono_on hInt.integrableOn
          (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one) measurableSet_Ioi
          (fun _ hx => midModelDecay_le_rpow (by linarith) (zero_lt_one.trans hx))
      _ = _ := by
        rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow, neg_div, ← div_neg]
        congr 1
        ring
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hInt.integrableOn hInt.integrableOn]
  exact add_le_add h₁ h₂

theorem integral_midModelDecay_Iic_le {q : ℝ} (hq : 1 < q) :
    (∫ η in Iic (0 : ℝ), midModelDecay q η) ≤ 1 + 1 / (q - 1) := by
  rw [← neg_zero, ← integral_comp_neg_Ioi]
  have he : (fun x : ℝ => midModelDecay q (-x)) = midModelDecay q :=
    funext (midModelDecay_even q)
  rw [he]
  exact integral_midModelDecay_Ioi_le hq

theorem integral_midModelDecay_shift_le {q : ℝ} (hq : 1 < q) :
    (∫ η in Ioi (3 / 2 : ℝ), midModelDecay q η) ≤ 1 + 1 / (q - 1) := by
  refine (setIntegral_mono_set (integrable_midModelDecay hq).integrableOn
    (Filter.Eventually.of_forall (midModelDecay_nonneg q))
    (Filter.Eventually.of_forall (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 3 / 2)))).trans
      (integral_midModelDecay_Ioi_le hq)

theorem integrable_midModelHsecond {t ρ : ℝ} (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) :
    Integrable (midModelHsecond t ρ) := by
  let B := Real.exp t * ((1 / 4 : ℝ) + 2 * t + 4 * t ^ 2)
  have hInt := (integrable_midModelDecay (q := 3 / 2) (by norm_num)).const_mul B
  refine hInt.mono' (continuous_midModelHsecond t ρ).aestronglyMeasurable ?_
  filter_upwards with η
  have e : (midModelK t ρ / midModelZ η).re ≤ t := by
    rw [re_midModelK_div]
    have hp : 0 ≤ (η - ρ) ^ 2 / (1 + η ^ 2) := by positivity
    nlinarith [mul_nonneg ht hp]
  calc
    _ ≤ Real.exp (midModelK t ρ / midModelZ η).re *
        ((1 / 4) * midModelDecay (3 / 2) η + 2 * t * midModelDecay (5 / 2) η +
          4 * t ^ 2 * midModelDecay (7 / 2) η) := norm_midModelHsecond_le ht hρ hρ' η
    _ ≤ Real.exp t * ((1 / 4) * midModelDecay (3 / 2) η + 2 * t * midModelDecay (3 / 2) η +
          4 * t ^ 2 * midModelDecay (3 / 2) η) := by
        refine mul_le_mul (Real.exp_le_exp.2 e) ?_ ?_ (Real.exp_nonneg _)
        swap
        · obtain h₃ := midModelDecay_nonneg (3 / 2) η
          obtain h₅ := midModelDecay_nonneg (5 / 2) η
          obtain h₇ := midModelDecay_nonneg (7 / 2) η
          positivity
        gcongr
        · exact midModelDecay_mono (by norm_num) η
        · exact midModelDecay_mono (by norm_num) η
    _ = B * midModelDecay (3 / 2) η := by unfold B; ring

theorem integrable_midModelOsc_Hsecond {t ρ : ℝ} (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) :
    Integrable (fun η => midModelOsc t η * midModelHsecond t ρ η) := by
  refine (integrable_midModelHsecond ht hρ hρ').norm.mono'
    ((continuous_midModelOsc t).mul (continuous_midModelHsecond t ρ)).aestronglyMeasurable ?_
  filter_upwards with η
  rw [norm_mul, norm_midModelOsc, one_mul]

end DurfeeCCS.Step09
