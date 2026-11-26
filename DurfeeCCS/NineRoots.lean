module

public import DurfeeCCS.RootAssembly
public import DurfeeCCS.Samples
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The `n = 9` sample, evaluated using the partition-derived coefficients. -/

public section

namespace DurfeeCCS

open Polynomial

theorem durfeeQuotient_nine : durfeeQuotient 9 = C 9 + C 20 * X + X ^ 2 := by
  apply mul_left_cancel₀ (X_ne_zero : (X : ℤ[X]) ≠ 0)
  rw [← durfeePolynomial_eq_X_mul_quotient (by decide), durfeePolynomial_nine]
  ring

theorem durfeeQuotientReal_nine : durfeeQuotientReal 9 = C 9 + C 20 * X + X ^ 2 := by
  have h₉ : C (9 : ℝ) = (9 : ℝ[X]) := C_eq_natCast 9
  have h₂₀ : C (20 : ℝ) = (20 : ℝ[X]) := C_eq_natCast 20
  simp [durfeeQuotientReal, durfeeQuotient_nine, h₉, h₂₀]

theorem durfeeQuotientReal_nine_eval (x : ℝ) :
    (durfeeQuotientReal 9).eval x = 9 + 20 * x + x ^ 2 := by
  simp [durfeeQuotientReal_nine]

theorem durfeeQuotientReal_nine_trial_values :
    (durfeeQuotientReal 9).eval (-20) = 9 ∧
    (durfeeQuotientReal 9).eval (-1) = -10 ∧
    (durfeeQuotientReal 9).eval 0 = 9 := by
  norm_num [durfeeQuotientReal_nine_eval]

private theorem sqrt_nine : (9 : ℕ).sqrt = 3 := Nat.sqrt_eq 3

theorem durfeeQuotientReal_nine_tendsto_atBot :
    Filter.Tendsto (durfeeQuotientReal 9).eval Filter.atBot Filter.atTop := by
  have hdeg : (durfeeQuotientReal 9).natDegree = 2 :=
    (natDegree_durfeeQuotientReal (by decide : 0 < 9)).trans (by rw [sqrt_nine])
  apply tendsto_eval_atBot_atTop_of_even_degree _ (leadingCoeff_durfeeQuotientReal_pos (by decide))
  · rw [hdeg]
    decide
  · rw [hdeg]
    exact ⟨1, rfl⟩

private noncomputable def nineTrialPoints : Fin 3 → ℝ := ![-20, -1, 0]

/-- One negative root lies in each displayed interval. Together with zero they exhaust both
the real and complex roots, all with multiplicity one. -/
theorem durfeePolynomial_nine_rootCompletion :
    ∃ r : Fin 2 ↪ ℝ, r 0 ∈ Set.Ioo (-20 : ℝ) (-1) ∧ r 1 ∈ Set.Ioo (-1 : ℝ) 0 ∧
      RootCompletion (durfeePolynomialReal 9) r := by
  have hm : (9 : ℕ).sqrt = 2 + 1 := sqrt_nine
  have hmono : StrictMono nineTrialPoints := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [nineTrialPoints, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
  have hneg (i : Fin 3) : nineTrialPoints i ≤ 0 := by
    fin_cases i <;> norm_num [nineTrialPoints]
  have hsign (i : Fin 2) : (durfeeQuotientReal 9).eval (nineTrialPoints i.castSucc) *
      (durfeeQuotientReal 9).eval (nineTrialPoints i.succ) < 0 := by
    fin_cases i <;>
      norm_num [nineTrialPoints, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ,
        durfeeQuotientReal_nine_eval]
  obtain ⟨r, hr, hcomplete⟩ :=
    durfeeRootCompletion_of_alternating (by decide) hm nineTrialPoints hmono hneg hsign
  refine ⟨r, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hcomplete⟩
  · simpa [nineTrialPoints] using (hr 0).1
  · simpa [nineTrialPoints] using (hr 0).2.1
  · simpa [nineTrialPoints] using (hr 1).1
  · simpa [nineTrialPoints] using (hr 1).2.1

/-- The complex Durfee polynomial of size nine has precisely three simple roots. -/
theorem durfeePolynomialComplex_nine_threeSimpleRoots :
    ∃ a b : ℝ, a ∈ Set.Ioo (-20 : ℝ) (-1) ∧ b ∈ Set.Ioo (-1 : ℝ) 0 ∧
      (durfeePolynomialComplex 9).roots.card = 3 ∧
      (∀ z : ℂ, (durfeePolynomialComplex 9).IsRoot z ↔ z = 0 ∨ z = (a : ℂ) ∨ z = (b : ℂ)) ∧
      (∀ z : ℂ, (durfeePolynomialComplex 9).IsRoot z →
        rootMultiplicity z (durfeePolynomialComplex 9) = 1) := by
  obtain ⟨r, ha, hb, hcomplete⟩ := durfeePolynomial_nine_rootCompletion
  refine ⟨r 0, r 1, ha, hb, ?_, ?_, ?_⟩
  · rw [durfeePolynomialComplex_eq_map_real]
    exact hcomplete.complex_card
  · intro z
    rw [durfeePolynomialComplex_eq_map_real, hcomplete.complex_root_iff z]
    constructor
    · rintro (hz | ⟨i, hi⟩)
      · exact Or.inl hz
      · fin_cases i
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr hi)
    · rintro (hz | ha' | hb')
      · exact Or.inl hz
      · exact Or.inr ⟨0, ha'⟩
      · exact Or.inr ⟨1, hb'⟩
  · rw [durfeePolynomialComplex_eq_map_real]
    exact hcomplete.complex_simple

end DurfeeCCS
