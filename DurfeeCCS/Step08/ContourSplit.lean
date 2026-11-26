module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Complex.Norm

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Splitting the error between two contour integrals into a common arc and two tails. -/

public section

namespace DurfeeCCS.Step08

open MeasureTheory Set

theorem norm_contour_difference_le {A B : ℝ → ℂ} {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t)
    (hA : IntegrableOn A t) (hB : Integrable B) :
    ‖(∫ v in t, A v) - ∫ v, B v‖ ≤
      (∫ v in s, ‖A v - B v‖) + (∫ v in t \ s, ‖A v‖) + ∫ v in sᶜ, ‖B v‖ := by
  have hAs : IntegrableOn A s := hA.mono_set hst
  have hAt : IntegrableOn A (t \ s) := hA.mono_set sdiff_subset
  have hdis : Disjoint s (t \ s) := Set.disjoint_left.mpr (fun _ ha hb => hb.2 ha)
  have hUnion : s ∪ (t \ s) = t := by
    ext v
    constructor
    · rintro (hv | hv)
      · exact hst hv
      · exact hv.1
    · intro hv
      by_cases hv' : v ∈ s
      · exact Or.inl hv'
      · exact Or.inr ⟨hv,hv'⟩
  have hsplitA : (∫ v in t, A v) = (∫ v in s, A v) + ∫ v in t \ s, A v := by
    calc
      _ = ∫ v in s ∪ (t \ s), A v := congrArg (fun q => ∫ v in q, A v) hUnion.symm
      _ = _ := setIntegral_union hdis (ht.diff hs) hAs hAt
  have hsplitB := integral_add_compl hs hB
  rw [hsplitA, ← hsplitB]
  have heq : ((∫ v in s, A v) + ∫ v in t \ s, A v) -
      ((∫ v in s, B v) + ∫ v in sᶜ, B v) =
      ((∫ v in s, A v - B v) + ∫ v in t \ s, A v) - ∫ v in sᶜ, B v := by
    rw [integral_sub hAs hB.integrableOn]
    abel
  rw [heq]
  have h1 := norm_sub_le ((∫ v in s, A v - B v) + ∫ v in t \ s, A v) (∫ v in sᶜ, B v)
  have h2 := norm_add_le (∫ v in s, A v - B v) (∫ v in t \ s, A v)
  have h3 := norm_integral_le_integral_norm (μ := volume.restrict s) (fun v => A v - B v)
  have h4 := norm_integral_le_integral_norm (μ := volume.restrict (t \ s)) A
  have h5 := norm_integral_le_integral_norm (μ := volume.restrict sᶜ) B
  linarith only [h1,h2,h3,h4,h5]

end DurfeeCCS.Step08
