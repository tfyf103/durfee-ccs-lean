module

public import DurfeeCCS.Step07.SaddleEndpoints
public import DurfeeCCS.Step07.SaddleGlobalMonotone
public import DurfeeCCS.Step07.ThetaFinite

import Mathlib.Tactic.NormNum

/-! Applying the finite error budgets to the actual saddles. -/

@[expose] public section

namespace DurfeeCCS.Step07

open Set DurfeeCCS.Step06

/-- The saddle enclosures at the ends of a row extend to the entire logarithmic interval. -/
theorem theta38_encloses_of_endpoints (i : Fin 9) {r : ℝ} (hr : 0 < r)
    (hlog : Real.log r ∈ Icc (theta38Row i).ell (theta38Row i).hi)
    (ha₀ : (theta38Row i).aMin ≤ (saddleS (Real.exp (theta38Row i).ell)).re)
    (hb₀ : (theta38Row i).bMin ≤ (saddleS (Real.exp (theta38Row i).ell)).im)
    (ha₁ : (saddleS (Real.exp (theta38Row i).hi)).re ≤ (theta38Row i).aMax)
    (hb₁ : (saddleS (Real.exp (theta38Row i).hi)).im ≤ (theta38Row i).bMax) :
    (theta38Row i).encloses r := by
  have hl : Real.exp (theta38Row i).ell ≤ r := by
    simpa only [Real.exp_log hr] using Real.exp_le_exp.mpr hlog.1
  have hu : r ≤ Real.exp (theta38Row i).hi := by
    simpa only [Real.exp_log hr] using Real.exp_le_exp.mpr hlog.2
  have hB := strictMonoOn_saddleS_im.monotoneOn
  exact ⟨ha₀.trans (monotoneOn_saddleS_re (Real.exp_pos _) hr hl),
    (monotoneOn_saddleS_re hr (Real.exp_pos _) hu).trans ha₁,
    hb₀.trans (hB (Real.exp_pos _) hr hl), (hB hr (Real.exp_pos _) hu).trans hb₁⟩

/-- Every radius in the first row satisfies the stated saddle-component bounds. -/
theorem theta38_first_row_encloses {r : ℝ} (hr : 0 < r)
    (hlog : Real.log r ∈ Icc 0 0.0625) : (theta38Row 0).encloses r := by
  refine theta38_encloses_of_endpoints 0 hr hlog ?_ ?_ ?_ ?_
  · simpa [theta38Row] using saddle_at_one_lower.1
  · simpa [theta38Row] using saddle_at_one_lower.2
  · simpa [theta38Row, show (0.0625 : ℝ) = 1 / 16 by norm_num] using
      saddle_at_exp_one_sixteenth_upper.1
  · simpa [theta38Row, show (0.0625 : ℝ) = 1 / 16 by norm_num] using
      saddle_at_exp_one_sixteenth_upper.2

/-- The first-row error budget applies throughout (0≤\log r≤0.0625). -/
theorem theta38_first_row_verified {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 0 < r)
    (hlog : Real.log r ∈ Icc 0 0.0625) :
    (theta38Row 0).encloses r ∧
      r⁻¹ ≤ 1 ∧ (saddleS r).re / Real.sqrt (n : ℝ) ≤ 1.10495 / 80 ∧
      (saddleS r).im / (saddleS r).re ≤ theta38Rho 1.06975 0.87428 ∧
      (theta38Row 0).error < 0.876 := by
  have hs := theta38_first_row_encloses hr hlog
  exact ⟨hs, by simpa [theta38Row, theta38Rho] using theta38_finite_budget_at 0 hn hr hlog hs⟩

end DurfeeCCS.Step07
