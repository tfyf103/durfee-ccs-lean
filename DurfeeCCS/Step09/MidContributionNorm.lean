module

public import DurfeeCCS.Step09.MidPhase
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Norm comparison and subdivision of a single frequency integral on the central arc. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step08

private theorem mid_integrableOn_slices {n : ℕ} {r : ℝ} {p : ℤ}
    (hp : IntegrableOn (Function.uncurry (midIntegrand n r p))
      (Icc (-8) 8 ×ˢ (univ : Set ℝ)) (volume.prod volume)) :
    IntegrableOn (fun η : ℝ => ∫ χ : ℝ, midIntegrand n r p η χ) (Icc (-8) 8) ∧
      IntegrableOn (fun η : ℝ => ∫ χ : ℝ, ‖midIntegrand n r p η χ‖) (Icc (-8) 8) := by
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at hp
  exact ⟨hp.integral_prod_left, hp.norm.integral_prod_left⟩

theorem mid_intervalIntegrable_of_integrableOn {n : ℕ} {r : ℝ} {p : ℤ} {l h : ℝ}
    (hl : -8 ≤ l) (hh : h ≤ 8) (hab : l ≤ h)
    (hp : IntegrableOn (Function.uncurry (midIntegrand n r p))
      (Icc (-8) 8 ×ˢ (univ : Set ℝ)) (volume.prod volume)) :
    IntervalIntegrable (fun η : ℝ => ∫ χ : ℝ, midIntegrand n r p η χ) volume l h := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((mid_integrableOn_slices hp).1.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc hl hh)))

theorem norm_midContribution_le {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    {p : ℤ} {l h : ℝ} (hl : -8 ≤ l) (hh : h ≤ 8) (hab : l ≤ h)
    (hp : IntegrableOn (Function.uncurry (midIntegrand n r p))
      (Icc (-8) 8 ×ˢ (univ : Set ℝ)) (volume.prod volume)) :
    ‖midContribution n r p l h‖ ≤ midU n r / (4 * Real.pi ^ 2) *
      (∫ η in l..h, ∫ χ : ℝ, ‖midIntegrand n r p η χ‖) := by
  have hu := saddleU_pos hn hr
  have hf : 0 ≤ midU n r / (4 * Real.pi ^ 2) := by positivity
  rw [midContribution, norm_mul, Complex.norm_of_nonneg hf]
  apply mul_le_mul_of_nonneg_left _ hf
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hb := (mid_integrableOn_slices hp).2.mono_set
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc hl hh))
  exact norm_integral_le_of_norm_le hb (Filter.Eventually.of_forall fun η =>
    norm_integral_le_integral_norm (fun χ : ℝ => midIntegrand n r p η χ))

theorem midContribution_split_at_zero {n : ℕ} {r : ℝ} {p : ℤ}
    (hp : IntegrableOn (Function.uncurry (midIntegrand n r p))
      (Icc (-8) 8 ×ˢ (univ : Set ℝ)) (volume.prod volume)) :
    midContribution n r p (-8) 8 =
      midContribution n r p (-8) 0 + midContribution n r p 0 8 := by
  have hleft := mid_intervalIntegrable_of_integrableOn (l := -8) (h := 0) le_rfl
    (by norm_num) (by norm_num) hp
  have hright := mid_intervalIntegrable_of_integrableOn (l := 0) (h := 8)
    (by norm_num) le_rfl (by norm_num) hp
  unfold midContribution
  rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals hleft hright]

end DurfeeCCS.Step09
