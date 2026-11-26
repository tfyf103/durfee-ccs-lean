module

public import Mathlib.Topology.Algebra.Order.Polynomial
public import Mathlib.Basic.Real.Basic

/-! The sign of a real polynomial on the negative tail is determined by its leading term. -/

public section

namespace DurfeeCCS

open Filter Polynomial

/-- Multiplying by the parity of the degree makes a polynomial with positive leading
coefficient and positive degree tend to positive infinity at the negative end. -/
theorem tendsto_signed_eval_atBot_atTop (P : Polynomial ℝ) (h : 0 < P.leadingCoeff)
    (hdeg : 0 < P.natDegree) :
    Tendsto (fun x : ℝ => (-1 : ℝ) ^ P.natDegree * P.eval x) atBot atTop := by
  let a : ℝ := (-1) ^ P.natDegree
  let R : Polynomial ℝ := C a * P.comp (-X)
  have ha : a ≠ 0 := pow_ne_zero _ (by simp)
  have haa : a * a = 1 := by
    dsimp [a]
    rw [← mul_pow]
    simp
  have hRdeg : 0 < R.degree := by
    change 0 < (C a * P.comp (-X)).degree
    rw [degree_C_mul ha, degree_comp_neg_X]
    exact natDegree_pos_iff_degree_pos.mp hdeg
  have hRlead : 0 ≤ R.leadingCoeff := by
    change 0 ≤ (C a * P.comp (-X)).leadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C, comp_neg_X_leadingCoeff_eq]
    change 0 ≤ a * (a * P.leadingCoeff)
    rw [← mul_assoc, haa, one_mul]
    exact h.le
  simpa [R, a, Function.comp_def, eval_comp] using
    (tendsto_atTop_of_leadingCoeff_nonneg hRdeg hRlead).comp tendsto_neg_atBot_atTop

/-- On the negative tail the sign agrees strictly with `(-1)^natDegree`. -/
theorem eventually_pos_negOnePow_mul_eval_atBot (P : Polynomial ℝ) (h : 0 < P.leadingCoeff) :
    ∀ᶠ x : ℝ in atBot, 0 < (-1 : ℝ) ^ P.natDegree * P.eval x := by
  by_cases hdeg : 0 < P.natDegree
  · exact (tendsto_signed_eval_atBot_atTop P h hdeg).eventually_gt_atTop 0
  · have hzero : P.natDegree = 0 := Nat.eq_zero_of_not_pos hdeg
    refine Eventually.of_forall (fun x => ?_)
    rw [hzero, pow_zero, one_mul, eq_C_of_natDegree_eq_zero hzero, eval_C]
    simpa [leadingCoeff, hzero] using h

/-- Positive leading coefficient and positive even degree give the positive infinite limit. -/
theorem tendsto_eval_atBot_atTop_of_even_degree (P : Polynomial ℝ) (h : 0 < P.leadingCoeff)
    (hdeg : 0 < P.natDegree) (heven : Even P.natDegree) : Tendsto P.eval atBot atTop := by
  simpa only [heven.neg_one_pow, one_mul] using tendsto_signed_eval_atBot_atTop P h hdeg

end DurfeeCCS
