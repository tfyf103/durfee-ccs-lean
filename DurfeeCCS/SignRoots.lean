module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fin.SuccPred
import Mathlib.Topology.Algebra.Monoid

public section

namespace DurfeeCCS

/-- Strict sign changes on consecutive intervals give distinct negative roots, one in each
interval. Allowing the final endpoint to be zero keeps the roots strictly negative. -/
theorem negativeRoots_of_alternating {k : ℕ} (P : Polynomial ℝ)
    (x : Fin (k + 1) → ℝ) (hx : StrictMono x) (hn : ∀ i, x i ≤ 0)
    (hs : ∀ i : Fin k, P.eval (x i.castSucc) * P.eval (x i.succ) < 0) :
    ∃ r : Fin k ↪ ℝ, ∀ i, x i.castSucc < r i ∧ r i < x i.succ ∧ r i < 0 ∧ P.IsRoot (r i) := by
  have hc : Continuous fun y => P.eval y := by
    simp only [Polynomial.eval_eq_sum, Polynomial.sum]
    exact continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_pow _)
  have each (i : Fin k) : ∃ r ∈ Set.Ioo (x i.castSucc) (x i.succ), P.IsRoot r := by
    have hlt : x i.castSucc < x i.succ := hx Fin.castSucc_lt_succ
    rcases mul_neg_iff.mp (hs i) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact intermediate_value_Ioo' hlt.le hc.continuousOn ⟨hb, ha⟩
    · exact intermediate_value_Ioo hlt.le hc.continuousOn ⟨ha, hb⟩
  choose r hr hroot using each
  have hmono : StrictMono r := by
    intro i j hij
    have hsep : x i.succ ≤ x j.castSucc := hx.monotone (Fin.succ_le_castSucc_iff.mpr hij)
    exact (hr i).2.trans_le (hsep.trans (hr j).1.le)
  exact ⟨⟨r, hmono.injective⟩, fun i =>
    ⟨(hr i).1, (hr i).2, (hr i).2.trans_le (hn i.succ), hroot i⟩⟩

end DurfeeCCS
