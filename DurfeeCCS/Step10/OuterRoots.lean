module

public import DurfeeCCS.NegativeTail
public import DurfeeCCS.Quotient
public import DurfeeCCS.SignRoots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public noncomputable section

namespace DurfeeCCS.Step10

open Filter Polynomial

theorem leadingCoeff_durfeePolynomialReal_pos {n : ℕ} (hn : 0 < n) :
    0 < (durfeePolynomialReal n).leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_durfeePolynomialReal, coeff_durfeePolynomialReal]
  exact_mod_cast p_pos_of_square_le (Nat.sqrt_pos.mpr hn) (Nat.sqrt_le n)

theorem eventually_signed_durfeePolynomialReal_atBot {n : ℕ} (hn : 0 < n) :
    ∀ᶠ x : ℝ in atBot, 0 < (-1 : ℝ) ^ n.sqrt * (durfeePolynomialReal n).eval x := by
  simpa only [natDegree_durfeePolynomialReal] using
    eventually_pos_negOnePow_mul_eval_atBot _ (leadingCoeff_durfeePolynomialReal_pos hn)

/-- The negative tail supplies the final interval beyond the last sampled radius. -/
theorem outerRoots_of_alternating {n d₀ : ℕ} (hn : 0 < n) (hd₀ : d₀ < n.sqrt)
    (x : ℕ → ℝ) (hpos : ∀ d, d₀ ≤ d → d < n.sqrt → 0 < x d)
    (hmono : StrictMonoOn x (Set.Ico d₀ n.sqrt))
    (hsign : ∀ d, d₀ ≤ d → d < n.sqrt →
      0 < (-1 : ℝ) ^ d * (durfeePolynomialReal n).eval (-x d)) :
    ∃ r : Fin (n.sqrt - d₀) ↪ ℝ, ∀ i,
      r i < -x d₀ ∧ (durfeePolynomialReal n).IsRoot (r i) := by
  let m := n.sqrt
  let k := m - d₀
  have hk : 0 < k := Nat.sub_pos_of_lt hd₀
  obtain ⟨a, ha, hap⟩ : ∃ a : ℝ, a < -x (m - 1) ∧
      0 < (-1 : ℝ) ^ m * (durfeePolynomialReal n).eval a := by
    have he := (eventually_signed_durfeePolynomialReal_atBot hn).and
      (eventually_lt_atBot (-x (m - 1)))
    obtain ⟨a, hp, ha⟩ := he.exists
    exact ⟨a, ha, hp⟩
  let z (i : Fin (k + 1)) := if i.val = 0 then a else -x (m - i.val)
  have hzSign (i : Fin (k + 1)) :
      0 < (-1 : ℝ) ^ (m - i.val) * (durfeePolynomialReal n).eval (z i) := by
    by_cases hi : i.val = 0
    · simpa only [z, ite_eq_left hi, hi, Nat.sub_zero] using hap
    · rw [show z i = -x (m - i.val) by simp only [z, ite_eq_right hi]]
      apply hsign <;> have := i.isLt <;> dsimp [k] at * <;> omega
  have hzm : StrictMono z := by
    intro i j hij
    have hv : i.val < j.val := hij
    have hj := j.isLt
    have hj₀ : j.val ≠ 0 := by omega
    by_cases hi₀ : i.val = 0
    · simp only [z, hi₀, hj₀, ite_true, ite_false]
      refine ha.trans_le (neg_le_neg (hmono.monotoneOn ?_ ?_ (by omega)))
      all_goals dsimp [k] at *; exact ⟨by omega, by omega⟩
    · simp only [z, hi₀, hj₀, ite_false, neg_lt_neg_iff]
      apply hmono _ _ (by dsimp [k] at *; omega)
      all_goals
        have hi := i.isLt
        dsimp [k] at *
        exact ⟨by omega, by omega⟩
  have hzNeg (i : Fin (k + 1)) : z i ≤ 0 := by
    have hi := i.isLt
    dsimp [k] at hi
    by_cases hi₀ : i.val = 0
    · simpa only [z, ite_eq_left hi₀] using ha.le.trans (neg_nonpos.mpr (hpos (m - 1) (by omega) (by omega)).le)
    · simpa only [z, ite_eq_right hi₀] using (neg_nonpos.mpr (hpos (m - i.val) (by omega) (by omega)).le)
  have hprod (i : Fin k) :
      (durfeePolynomialReal n).eval (z i.castSucc) *
        (durfeePolynomialReal n).eval (z i.succ) < 0 := by
    have hp := mul_pos (hzSign i.castSucc) (hzSign i.succ)
    have hi := i.isLt
    change i.val < m - d₀ at hi
    have heq : m - (i.val + 1) + 1 = m - i.val := by omega
    change 0 < ((-1 : ℝ) ^ (m - i.val) * _) *
      ((-1 : ℝ) ^ (m - (i.val + 1)) * _) at hp
    rw [← heq, pow_succ] at hp
    have hassoc :
        ((-1 : ℝ) ^ (m - (i.val + 1)) * -1 * (durfeePolynomialReal n).eval (z i.castSucc)) *
        ((-1 : ℝ) ^ (m - (i.val + 1)) * (durfeePolynomialReal n).eval (z i.succ)) =
        ((-1 : ℝ) ^ (m - (i.val + 1)) * (-1 : ℝ) ^ (m - (i.val + 1))) *
        (-((durfeePolynomialReal n).eval (z i.castSucc) *
          (durfeePolynomialReal n).eval (z i.succ))) := by ring
    rw [hassoc, ← mul_pow] at hp
    norm_num at hp
    exact hp
  obtain ⟨r, hr⟩ := negativeRoots_of_alternating _ z hzm hzNeg hprod
  refine ⟨r, fun i => ⟨(hr i).2.1.trans_le ?_, (hr i).2.2.2⟩⟩
  have hi := i.isLt
  change i.val < m - d₀ at hi
  have hend : Fin.last k = ⟨k, by omega⟩ := rfl
  have hzEnd : z (Fin.last k) = -x d₀ := by
    have hid : m - k = d₀ := by dsimp [k]; omega
    simp [z, hend, hk.ne', hid]
  rw [← hzEnd]
  exact hzm.monotone (Fin.le_last i.succ)

end DurfeeCCS.Step10
