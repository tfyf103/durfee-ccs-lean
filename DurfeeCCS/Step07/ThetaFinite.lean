module

public import DurfeeCCS.Step06.Saddle
public import DurfeeCCS.Step07.ThetaBounds
public import DurfeeCCS.Step07.PowerDecay

/-! Admissibility of the finite-row numerical parameters when the saddle components
lie within the stated endpoint enclosures. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open DurfeeCCS.Step06 Real

/-- The component enclosures listed on a finite row of page 30. -/
def Theta38Row.encloses (row : Theta38Row) (r : ℝ) : Prop :=
  row.aMin ≤ (saddleS r).re ∧ (saddleS r).re ≤ row.aMax ∧
    row.bMin ≤ (saddleS r).im ∧ (saddleS r).im ≤ row.bMax

theorem theta38_rows_b_pos (i : Fin 9) : 0 < (theta38Row i).bMin := by
  fin_cases i <;> norm_num [theta38Row]

theorem theta38_rows_delta_le_three (i : Fin 9) :
    theta38Delta (theta38Row i).aMin (theta38Row i).bMax ≤
      theta38DeltaThree (theta38Row i).aMin (theta38Row i).bMax := by
  fin_cases i <;> norm_num [theta38Row, theta38Delta, theta38DeltaThree, theta38Rho]

/-- From a row's logarithmic-radius and saddle-component enclosures, the choices of
`ε₊`, `q₊` and `ϱ₊` in the manuscript dominate the analytic values. -/
theorem theta38_row_admissible_at (i : Fin 9) {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 0 < r)
    (hlog : log r ∈ Set.Icc (theta38Row i).ell (theta38Row i).hi)
    (hs : (theta38Row i).encloses r) :
    let row := theta38Row i
    let a := (saddleS r).re
    let b := (saddleS r).im
    80 ≤ √(n : ℝ) ∧ 0 < a ∧ 0 < b ∧
      r⁻¹ ≤ exp (-row.ell) ∧ a / √(n : ℝ) ≤ row.aMax / 80 ∧
      b / a ≤ theta38Rho row.aMin row.bMax := by
  let row := theta38Row i
  obtain ⟨haMin, haMax, _, _, _⟩ := theta38_rows_admissible i
  obtain ⟨hal, hau, hbl, hbu⟩ := hs
  have hsqrt : 80 ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have ha := haMin.trans_le hal
  have hb := (theta38_rows_b_pos i).trans_le hbl
  have heps : r⁻¹ ≤ exp (-row.ell) := by
    rw [← Real.exp_log hr, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (neg_le_neg hlog.1)
  refine ⟨hsqrt, ha, hb, heps, ?_, ?_⟩
  · exact div_le_div₀ haMax.le hau (by norm_num) hsqrt
  · exact div_le_div₀ (hb.le.trans hbu) hbu haMin hal

/-- The two Gaussian exponents in (60) are already past the turnover point at
`√n = 80` for every admissible finite row. -/
theorem theta38_row_gaussian_admissible (i : Fin 9) {r : ℝ}
    (hs : (theta38Row i).encloses r) :
    let row := theta38Row i
    let a := (saddleS r).re
    let b := (saddleS r).im
    (1 / 2 : ℝ) ≤ (b ^ 2 / a) * 80 ∧
      (1 / 2 : ℝ) ≤ theta38Delta row.aMin row.bMax * (80 * a) := by
  let row := theta38Row i
  obtain ⟨haMin, haMax, hρ, hd, hb⟩ := theta38_rows_admissible i
  obtain ⟨hal, hau, hbl, _⟩ := hs
  have ha := haMin.trans_le hal
  have hbl₀ := (theta38_rows_b_pos i).le
  have hδ : 0 ≤ theta38Delta row.aMin row.bMax := by unfold theta38Delta; positivity
  constructor
  · have hrate : row.bMin ^ 2 / row.aMax ≤ (saddleS r).im ^ 2 / (saddleS r).re :=
      div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ hbl₀ hbl 2) ha hau
    have hb' : (1 / 2 : ℝ) ≤ (row.bMin ^ 2 / row.aMax) * 80 := by
      exact hb.le.trans_eq (by ring)
    exact hb'.trans (mul_le_mul_of_nonneg_right hrate (by norm_num))
  · have hd' : (1 / 2 : ℝ) ≤ theta38Delta row.aMin row.bMax * (80 * row.aMin) :=
      hd.le.trans_eq (by ring)
    exact hd'.trans (mul_le_mul_of_nonneg_left (by gcongr) hδ)

/-- The initial inequality comparing the manuscript's Gaussian cutoff to the row value of δ. -/
theorem theta38_row_delta_le {i : Fin 9} {a b : ℝ}
    (ha : (theta38Row i).aMin ≤ a) (hb : b ≤ (theta38Row i).bMax)
    (hb₀ : 0 ≤ b) :
    theta38Delta (theta38Row i).aMin (theta38Row i).bMax ≤ (3 - 2 * (b / a)) ^ 2 / 13 := by
  let row := theta38Row i
  obtain ⟨haMin, _, hρ, _, _⟩ := theta38_rows_admissible i
  have h := div_le_div₀ (hb₀.trans hb) hb haMin ha
  have hρ' : 0 ≤ 3 / 2 - theta38Rho row.aMin row.bMax := by linarith
  have hpow : (3 / 2 - theta38Rho row.aMin row.bMax) ^ 2 ≤ (3 / 2 - b / a) ^ 2 :=
    pow_le_pow_left₀ hρ' (sub_le_sub_left h _) 2
  unfold theta38Delta
  refine (div_le_div_of_nonneg_right hpow (by norm_num : 0 ≤ (13 / 4 : ℝ))).trans_eq ?_
  ring

/-- The row data guarantee a strict error bound once the analytic inputs satisfy
the row's enclosing inequalities. This concerns the numerical budget itself. -/
theorem theta38_finite_budget_at (i : Fin 9) {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 0 < r)
    (hlog : log r ∈ Set.Icc (theta38Row i).ell (theta38Row i).hi)
    (hs : (theta38Row i).encloses r) :
    let row := theta38Row i
    let a := (saddleS r).re
    let b := (saddleS r).im
    r⁻¹ ≤ exp (-row.ell) ∧ a / √(n : ℝ) ≤ row.aMax / 80 ∧
      b / a ≤ theta38Rho row.aMin row.bMax ∧ row.error < row.target := by
  obtain ⟨_, _, _, heps, hq, hρ⟩ := theta38_row_admissible_at i hn hr hlog hs
  exact ⟨heps, hq, hρ, theta38_error_rows i⟩

end DurfeeCCS.Step07
