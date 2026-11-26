module

public import DurfeeCCS.Step09.MidModelDecay
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Finite integration by parts and the two discarded rays in Lemma 3.7. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set

def midModelD (t : ℝ) : ℂ := (t : ℂ) * I

theorem midModelD_ne_zero {t : ℝ} (ht : t ≠ 0) : midModelD t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero

theorem norm_midModelD {t : ℝ} (ht : 0 ≤ t) : ‖midModelD t‖ = t := by
  rw [midModelD, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht]

def midModelBoundary (t ρ η : ℝ) : ℂ :=
  midModelOsc t η * midModelH t ρ η / midModelD t -
    midModelOsc t η * midModelHprime t ρ η / midModelD t ^ 2

/-- The full-line model is defined using only the absolutely integrable second derivative. -/
def midModelJInfinity (t ρ : ℝ) : ℂ :=
  midModelWeight t ρ *
    ((∫ η : ℝ, midModelOsc t η * midModelHsecond t ρ η) / midModelD t ^ 2)

def midModelTailLeft (t ρ : ℝ) : ℂ :=
  midModelBoundary t ρ 0 +
    (∫ η in Iic (0 : ℝ), midModelOsc t η * midModelHsecond t ρ η) / midModelD t ^ 2

def midModelTailRight (t ρ : ℝ) : ℂ :=
  -midModelBoundary t ρ (3 / 2) +
    (∫ η in Ioi (3 / 2 : ℝ), midModelOsc t η * midModelHsecond t ρ η) / midModelD t ^ 2

theorem hasDerivAt_midModelOsc (t η : ℝ) :
    HasDerivAt (midModelOsc t) (midModelD t * midModelOsc t η) η := by
  have h := ((((hasDerivAt_id (η : ℂ)).const_mul (t : ℂ)).mul_const I).cexp).comp_ofReal
  change HasDerivAt (midModelOsc t) _ η at h
  convert h using 1
  change midModelD t * midModelOsc t η = midModelOsc t η * ((t : ℂ) * 1 * I)
  rw [midModelD, mul_one, mul_comm]

private theorem hasDerivAt_midModelBoundary {t : ℝ} (ht : t ≠ 0) (ρ η : ℝ) :
    HasDerivAt (midModelBoundary t ρ)
      (midModelOsc t η * midModelH t ρ η -
        midModelOsc t η * midModelHsecond t ρ η / midModelD t ^ 2) η := by
  have hosc := hasDerivAt_midModelOsc t η
  have hH := hasDerivAt_midModelH t ρ η
  have hH' := hasDerivAt_midModelHprime t ρ η
  have h := ((hosc.mul hH).div_const (midModelD t)).sub
    ((hosc.mul hH').div_const (midModelD t ^ 2))
  change HasDerivAt (midModelBoundary t ρ) _ η at h
  convert h using 1
  field_simp [midModelD_ne_zero ht]
  ring

theorem midModelJ_eq_boundary {t : ℝ} (ht : t ≠ 0) (ρ : ℝ) :
    midModelJ t ρ =
      midModelWeight t ρ * (midModelBoundary t ρ (3 / 2) - midModelBoundary t ρ 0 +
        (∫ η in (0 : ℝ)..(3 / 2), midModelOsc t η * midModelHsecond t ρ η) / midModelD t ^ 2) := by
  have hA : Continuous (fun η => midModelOsc t η * midModelH t ρ η) :=
    (continuous_midModelOsc t).mul (continuous_midModelH t ρ)
  have hB : Continuous (fun η => midModelOsc t η * midModelHsecond t ρ η) :=
    (continuous_midModelOsc t).mul (continuous_midModelHsecond t ρ)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 3 / 2) (fun x _ => hasDerivAt_midModelBoundary ht ρ x)
    ((hA.sub (hB.div_const _)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_sub (hA.intervalIntegrable _ _) ((hB.div_const _).intervalIntegrable _ _),
    intervalIntegral.integral_div] at hi
  rw [midModelJ]
  simp_rw [midModelIntegrand_eq, intervalIntegral.integral_const_mul]
  apply congrArg (midModelWeight t ρ * ·)
  linear_combination hi

theorem midModelJInfinity_sub_eq_tails {t ρ : ℝ} (ht : 0 < t) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) :
    midModelJInfinity t ρ - midModelJ t ρ =
      midModelWeight t ρ * (midModelTailLeft t ρ + midModelTailRight t ρ) := by
  let f := fun η : ℝ => midModelOsc t η * midModelHsecond t ρ η
  have hf : Integrable f := integrable_midModelOsc_Hsecond ht.le hρ hρ'
  have hi : (∫ x in Iic (0 : ℝ), f x) + (∫ x in (0 : ℝ)..(3 / 2), f x) +
      (∫ x in Ioi (3 / 2 : ℝ), f x) = ∫ x : ℝ, f x := by
    have hset : Iic (3 / 2 : ℝ) = Iic 0 ∪ Ioc 0 (3 / 2) := by
      ext x
      simp only [mem_Iic, mem_union, mem_Ioc]
      constructor
      · intro h
        exact (le_or_gt x 0).imp_right (fun h' => ⟨h', h⟩)
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdis : Disjoint (Iic (0 : ℝ)) (Ioc 0 (3 / 2)) := by
      rw [Set.disjoint_left]
      exact fun x hx hy => (not_lt_of_ge hx) hy.1
    rw [intervalIntegral.integral_of_le (by norm_num), ← setIntegral_union hdis
      measurableSet_Ioc hf.integrableOn hf.integrableOn, ← hset]
    exact intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn
  rw [midModelJ_eq_boundary ht.ne', midModelJInfinity, midModelTailLeft, midModelTailRight, ← hi]
  ring

end DurfeeCCS.Step09
