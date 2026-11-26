module

public import DurfeeCCS.Step07.ThetaRadiusRows
public import DurfeeCCS.Step07.SaddleEndpointGrid

import Mathlib.Tactic.FinCases

/-! Uniform enclosures for all finite radius rows of Lemma 3.8. -/

@[expose] public section

namespace DurfeeCCS.Step07

open Set DurfeeCCS.Step06

theorem theta38_rows_enclose (i : Fin 9) {r : ℝ} (hr : 0 < r)
    (hlog : Real.log r ∈ Icc (theta38Row i).ell (theta38Row i).hi) :
    (theta38Row i).encloses r := by
  fin_cases i
  · exact theta38_first_row_encloses hr hlog
  · refine theta38_encloses_of_endpoints 1 hr hlog ?_ ?_ ?_ ?_
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 1).re_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 1).im_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 4).re_upper
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 4).im_upper
  · refine theta38_encloses_of_endpoints 2 hr hlog ?_ ?_ ?_ ?_
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 4).re_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 4).im_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 7).re_upper
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 7).im_upper
  · refine theta38_encloses_of_endpoints 3 hr hlog ?_ ?_ ?_ ?_
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 7).re_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 7).im_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 10).re_upper
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 10).im_upper
  · refine theta38_encloses_of_endpoints 4 hr hlog ?_ ?_ ?_ ?_
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 10).re_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 10).im_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 13).re_upper
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 13).im_upper
  · refine theta38_encloses_of_endpoints 5 hr hlog ?_ ?_ ?_ ?_
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 13).re_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 13).im_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 15).re_upper
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 15).im_upper
  · refine theta38_encloses_of_endpoints 6 hr hlog ?_ ?_ ?_ ?_
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 15).re_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 15).im_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 17).re_upper
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 17).im_upper
  · refine theta38_encloses_of_endpoints 7 hr hlog ?_ ?_ ?_ ?_
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 17).re_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 17).im_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 18).re_upper
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 18).im_upper
  · refine theta38_encloses_of_endpoints 8 hr hlog ?_ ?_ ?_ ?_
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 18).re_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 18).im_lower
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 19).re_upper
    · simpa [theta38Row, saddleEndpointData, Rat.cast_ofScientific] using
        (saddleEndpointData_bounds 19).im_upper

/-- For every logarithmic radius through five, some certified finite row applies. -/
theorem theta38_finite_rows_verified {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 0 < r)
    (hl : 0 ≤ Real.log r) (hu : Real.log r ≤ 5) :
    ∃ i : Fin 9, let row := theta38Row i
      Real.log r ∈ Icc row.ell row.hi ∧ row.encloses r ∧
      r⁻¹ ≤ Real.exp (-row.ell) ∧ (saddleS r).re / Real.sqrt (n : ℝ) ≤ row.aMax / 80 ∧
      (saddleS r).im / (saddleS r).re ≤ theta38Rho row.aMin row.bMax ∧
      row.error < row.target := by
  obtain ⟨i, hi⟩ := theta38_rows_cover hl hu
  have hs := theta38_rows_enclose i hr hi
  exact ⟨i, hi, hs, theta38_finite_budget_at i hn hr hi hs⟩

end DurfeeCCS.Step07
