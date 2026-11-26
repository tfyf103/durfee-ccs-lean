module

public import DurfeeCCS.NegativeTail
public import DurfeeCCS.Quotient
public import DurfeeCCS.RootCompletion
public import DurfeeCCS.SignRoots

/-! The root-counting argument shared by the finite certificates and the main proof. -/

public section

namespace DurfeeCCS

open Filter

/-- The sign at the negative endpoint in the finite-size argument is determined by the
degree `⌊√n⌋ - 1`. -/
theorem eventually_signed_durfeeQuotientReal_atBot {n : ℕ} (hn : 0 < n) :
    ∀ᶠ x : ℝ in atBot, 0 < (-1 : ℝ) ^ (n.sqrt - 1) * (durfeeQuotientReal n).eval x := by
  simpa only [natDegree_durfeeQuotientReal hn] using
    eventually_pos_negOnePow_mul_eval_atBot _ (leadingCoeff_durfeeQuotientReal_pos hn)

/-- The negative roots of the quotient and the root at zero exhaust the Durfee polynomial
when their count is the degree. The same list describes the roots after scalar extension. -/
theorem durfeeRootCompletion_of_quotientRoots {n k : ℕ} (hn : 0 < n)
    (hm : n.sqrt = k + 1) (r : Fin k ↪ ℝ)
    (hr : ∀ i, r i < 0 ∧ (durfeeQuotientReal n).IsRoot (r i)) :
    RootCompletion (durfeePolynomialReal n) r := by
  apply completeRoots_of_degree ((natDegree_durfeePolynomialReal n).trans hm) ?_ r ?_
  · simp [Polynomial.IsRoot, durfeePolynomialReal_eq_X_mul_quotient hn]
  · intro i
    refine ⟨(hr i).1, ?_⟩
    have hroot : (durfeeQuotientReal n).eval (r i) = 0 := (hr i).2
    simp [Polynomial.IsRoot, durfeePolynomialReal_eq_X_mul_quotient hn, hroot]

/-- A chain of `k + 1` nonpositive points with strictly alternating signs of `Qₙ`
certifies `k` distinct negative roots and a simple root at zero. -/
theorem durfeeRootCompletion_of_alternating {n k : ℕ} (hn : 0 < n)
    (hm : n.sqrt = k + 1) (x : Fin (k + 1) → ℝ) (hmono : StrictMono x)
    (hneg : ∀ i, x i ≤ 0)
    (hsign : ∀ i : Fin k,
      (durfeeQuotientReal n).eval (x i.castSucc) * (durfeeQuotientReal n).eval (x i.succ) < 0) :
    ∃ r : Fin k ↪ ℝ,
      (∀ i, x i.castSucc < r i ∧ r i < x i.succ ∧
        r i < 0 ∧ (durfeeQuotientReal n).IsRoot (r i)) ∧
      RootCompletion (durfeePolynomialReal n) r := by
  obtain ⟨r, hr⟩ := negativeRoots_of_alternating (durfeeQuotientReal n) x hmono hneg hsign
  exact ⟨r, hr, durfeeRootCompletion_of_quotientRoots hn hm r (fun i => (hr i).2.2)⟩

end DurfeeCCS
