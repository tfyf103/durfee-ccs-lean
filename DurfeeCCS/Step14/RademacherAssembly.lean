module

public import DurfeeCCS.Step14.RademacherCuspSplit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Summing the analytic errors of the finite Ford dissection. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step14

open Complex MeasureTheory
open DurfeeCCS.Step06 DurfeeCCS.Step08

/-- The difference between the full and polar parts of one Ford integral
has the denominator-scaled uniform bound used in the finite sum. -/
theorem norm_fordCoefficient_sub_polar_le {n h k N : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hg : h.Coprime k) (hN : 0 < N)
    {left right : ℝ} (hl : 0 ≤ left) (hr : 0 ≤ right)
    (hlN : (N : ℝ) ≤ (k : ℝ) * (left + 1)) (hrN : (N : ℝ) ≤ (k : ℝ) * (right + 1)) :
    ‖(∫ v in -left..right, fordCoefficientIntegrand n h k v) -
      twoColourPhase n h k * (∫ v in -left..right, fordPolarIntegrand n k v)‖ ≤
      4 * Real.exp (Real.pi + 2 * Real.pi * n) / ((k : ℝ) * (N : ℝ) ^ 2) := by
  obtain ⟨a, ha⟩ := integral_fordCoefficientIntegrand_split hn hk hg
  let b := fordPolarB n k
  let θ := 2 * Real.pi * (a : ℝ) / k
  have hb : 0 < b := fordPolarB_pos hn hk
  have hb' : b ≤ 2 * Real.pi * n := fordPolarB_le hn hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hleft : (N : ℝ) ≤ (k : ℝ) + (k : ℝ) * left := by
    simpa only [mul_add, mul_one, add_comm] using hlN
  have hright : (N : ℝ) ≤ (k : ℝ) + (k : ℝ) * right := by
    simpa only [mul_add, mul_one, add_comm] using hrN
  have he := norm_weighted_fordNonpolar_segment_le θ b
    (ω := twoColourPhase n h k) (by simp) hN' hk'
    (mul_nonneg hk'.le hl) (mul_nonneg hk'.le hr) hleft hright
  rw [mul_div_cancel_left₀ _ hk'.ne', mul_div_cancel_left₀ _ hk'.ne', Complex.ofReal_natCast] at he
  rw [ha, mul_add, add_sub_cancel_left, ← mul_div_assoc]
  refine (by simpa only [div_mul_eq_mul_div] using he :
    ‖(twoColourPhase n h k * ∫ v in -left..right,
      fordNonpolarKernel θ b (verticalPoint 1 v)) / (k : ℂ) ^ 3‖ ≤
      4 * Real.exp (Real.pi + |b|) / ((k : ℝ) * (N : ℝ) ^ 2)).trans ?_
  rw [abs_of_pos hb]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (add_le_add le_rfl hb')) (by norm_num)) (by positivity)

/-- A complete, denominator-indexed Ford path dissection gives the absolute
Rademacher expansion. The local polar and nonpolar limits are unconditional. -/
theorem twoColourRademacherIdentity_of_ford_integrals
    (decompose : ∀ n N : ℕ, 0 < n → 0 < N →
      ∃ left right : ℕ → ℕ → ℝ,
        (∀ k ∈ Finset.Icc 1 N, ∀ h ∈ (Finset.range k).filter (fun h => h.Coprime k),
          0 ≤ left h k ∧ 0 ≤ right h k ∧
          (N : ℝ) ≤ (k : ℝ) * (left h k + 1) ∧
          (N : ℝ) ≤ (k : ℝ) * (right h k + 1)) ∧
        (twoColourPartitionCount n : ℂ) =
          ∑ k ∈ Finset.Icc 1 N, ∑ h ∈ (Finset.range k).filter (fun h => h.Coprime k),
            ∫ v in -(left h k)..right h k, fordCoefficientIntegrand n h k v) :
    TwoColourRademacherIdentity := by
  apply twoColourRademacherIdentity_of_truncated_error
  intro n hn
  let C := 4 * Real.exp (Real.pi + 2 * Real.pi * n)
  refine ⟨8 * Real.exp (Real.pi / 6 + 2 * Real.pi * n) + C, fun N hN => ?_⟩
  obtain ⟨left, right, hsize, heq⟩ := decompose n N hn hN
  let err := fun h k => (∫ v in -(left h k)..right h k, fordCoefficientIntegrand n h k v) -
    twoColourPhase n h k * (∫ v in -(left h k)..right h k, fordPolarIntegrand n k v)
  apply norm_twoColour_truncated_error hn hN (by positivity : 0 ≤ C) left right err hsize
  · intro k hk h hh
    obtain ⟨hl, hr, hlN, hrN⟩ := hsize k hk h hh
    exact norm_fordCoefficient_sub_polar_le hn (Finset.mem_Icc.mp hk).1
      (Finset.mem_filter.mp hh).2 hN hl hr hlN hrN
  · simpa only [err, add_sub_cancel] using heq

end DurfeeCCS.Step14
