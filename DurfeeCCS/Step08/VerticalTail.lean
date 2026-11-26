module

public import DurfeeCCS.Step08.NearOriginLaplace

/-! A common tail bound for the vertical contours. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Set MeasureTheory

theorem integral_cauchy_density_tail_le {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    (∫ v in (Icc (-b) b)ᶜ, (u ^ 2 + v ^ 2)⁻¹) ≤ 2 / b := by
  let f := fun v : ℝ => (u ^ 2 + v ^ 2)⁻¹
  have hI := integrable_cauchy_density hu
  have hs : (Icc (-b) b)ᶜ = Iio (-b) ∪ Ioi b := by
    ext v
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  have hd : Disjoint (Iio (-b)) (Ioi b) := by
    refine Set.disjoint_left.mpr (fun v hv hv' => ?_)
    simp only [mem_Iio, mem_Ioi] at hv hv'
    linarith
  change (∫ v in (Icc (-b) b)ᶜ, f v) ≤ _
  rw [hs, setIntegral_union hd measurableSet_Ioi hI.integrableOn hI.integrableOn]
  have hneg : (∫ v in Iio (-b), f v) = ∫ v in Ioi b, f v := by
    rw [← integral_Iic_eq_integral_Iio]
    simpa only [neg_neg, f, neg_sq] using (integral_comp_neg_Iic (-b) f)
  rw [hneg]
  have hg := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hb
  have hpos : (∫ v in Ioi b, f v) ≤ 1 / b := by
    calc
      _ ≤ ∫ v in Ioi b, v ^ (-2 : ℝ) := by
        refine setIntegral_mono_on hI.integrableOn hg measurableSet_Ioi (fun v hv => ?_)
        have hv' : 0 < v := hb.trans hv
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hv'.le, Real.rpow_natCast]
        exact inv_anti₀ (by positivity) (le_add_of_nonneg_left (sq_nonneg u))
      _ = _ := by
        rw [integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hb]
        norm_num [Real.rpow_neg_one]
  calc
    _ ≤ 1 / b + 1 / b := add_le_add hpos hpos
    _ = _ := by ring

end DurfeeCCS.Step08
