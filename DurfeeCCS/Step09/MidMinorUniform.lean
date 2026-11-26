module

public import DurfeeCCS.Step09.MidMinorGrid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The exact conditional-on-the-sine formulation of (63). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open DurfeeCCS.Step07

/-- The two entries of (63), using the first alone when the sine vanishes. -/
theorem midMinor_mode_bound_63 {j : ℕ} (hj : 0 < j) {u t v y eₗ eᵤ : ℝ}
    (hu : 0 < u) (ht : 0 ≤ t) (hy : u ≤ y)
    (heₗ : 0 ≤ eₗ) (heₗ' : eₗ ≤ Real.exp (-t)) (heᵤ : Real.exp (-t) ≤ eᵤ) :
    let z := |Real.sin ((j : ℝ) * v / 2)|
    u * ‖midMinorMode j u t v‖ ≤ minorArcCReal eₗ y j ∧
      (0 < z → u * ‖midMinorMode j u t v‖ ≤ minorArcBReal eᵤ y z j) := by
  dsimp only
  constructor
  · by_cases hc : ((j : ℝ) * y) ^ 2 ≤ 24
    · exact (scaled_mode_le_c hj hu ht).trans (minorArc_c_increases j hu.le hy heₗ heₗ' hc)
    · let a := (j : ℝ) * u / 2
      have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
      have ha : 0 < a := by dsimp [a]; positivity
      have hs := Real.sinh_pos_iff.mpr ha
      have hMode := norm_midMinorMode_le_positive hj hu ht v
      change ‖midMinorMode j u t v‖ ≤ Real.cosh a / Real.sinh a -
        Real.exp (-(j : ℝ) * t) / (2 * Real.sinh a) at hMode
      have hDen : 0 ≤ Real.exp (-(j : ℝ) * t) / (2 * Real.sinh a) := by positivity
      have hr : u * (1/a + a/3) = 2 / (j:ℝ) + j*u^2/6 := by
        dsimp [a]
        field_simp
        ring
      calc
        _ ≤ u * (Real.cosh a / Real.sinh a) :=
          mul_le_mul_of_nonneg_left (hMode.trans (sub_le_self _ hDen)) hu.le
        _ ≤ u * (1/a + a/3) := mul_le_mul_of_nonneg_left (midMinor_coth_le ha) hu.le
        _ = _ := hr
        _ ≤ 2 / (j:ℝ) + j*y^2/6 := by gcongr
        _ ≤ _ := by
          unfold minorArcCReal
          have hsign : 0 ≤ (eₗ ^ j / (j : ℝ)) := by positivity
          have hterm : (eₗ ^ j / (j:ℝ)) * (1 - ((j:ℝ)*y)^2/24) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hsign (by linarith only [lt_of_not_ge hc])
          linarith only [hterm]
  · intro hz
    exact (scaled_mode_le_b hj hu ht hz).trans
      (minorArcBReal_compare hj (Real.exp_nonneg _) heᵤ hu hy hz le_rfl)

end DurfeeCCS.Step09
