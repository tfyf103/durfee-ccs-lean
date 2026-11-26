module

public import DurfeeCCS.Step10.OuterComplete
public import Mathlib.Basic.Real.Sign
import Mathlib.Tactic

/-! The outer endpoint for the last part of the proof of Theorem 1.2. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step11

open Real

private theorem realSign_eq_signType (x : ℝ) : Real.sign x = (SignType.sign x : ℝ) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, _root_.sign_neg hx]
    rfl
  · simp
  · rw [Real.sign_of_pos hx, _root_.sign_pos hx]
    rfl

/-- Corollary 4.4 supplies the right-hand phase endpoint of the saddle interval. The
corresponding outer zeros lie strictly to its left in the polynomial variable. -/
theorem outerEndpoint {n : ℕ} (hn : 6401 ≤ n) :
    ∃ d₀ : ℕ, ∃ rPlus : ℝ,
      10 ≤ d₀ ∧ d₀ < n.sqrt ∧ 1 < rPlus ∧ rPlus < Real.exp 1 * Real.sqrt (n : ℝ) ∧
      Real.sign ((durfeePolynomialReal n).eval (-(rPlus ^ 2))) = (-1 : ℝ) ^ d₀ ∧
      ((d₀ : ℝ) - 1) * π < Step06.saddlePhase n rPlus ∧
      ∃ root : Fin (n.sqrt - d₀) ↪ ℝ, ∀ i,
        root i < -(rPlus ^ 2) ∧ (durfeePolynomialReal n).IsRoot (root i) := by
  obtain ⟨d, x, ⟨hd, hdm⟩, hsign, _, ⟨hlog₁, hlog₂⟩, hphase, roots, hroots⟩ :=
    Step10.corollary44 hn
  have hn₁ : 0 < n := by omega
  have hm : 0 < n.sqrt := Nat.sqrt_pos.mpr hn₁
  have hdm' : d < n.sqrt := by omega
  have hd₉ : (9 : ℝ) < d := by
    linarith only [hd, Step10.eighty_lt_outerY hn]
  have hd₁₀ : 10 ≤ d := by
    exact_mod_cast hd₉
  have hx₀ : 0 < x d := (hsign d le_rfl hdm').1
  have hsize : (6401 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n := by linarith only [hsize]
  have hnshift : 1 < (n : ℝ) - 1 / 12 := by linarith only [hsize]
  have hstart : 0 < Step10.outerStart n := Real.log_pos hnshift
  have hlow : log 1 < log (x d) := by
    simpa only [log_one] using hstart.trans_le hlog₁
  have hx₁ : 1 < x d := (log_lt_log_iff zero_lt_one hx₀).mp hlow
  let rPlus := sqrt (x d)
  have hsq : rPlus ^ 2 = x d := sq_sqrt hx₀.le
  have hr₁ : 1 < rPlus := (lt_sqrt (by norm_num : 0 ≤ (1 : ℝ))).mpr (by simpa using hx₁)
  have hshiftlog : Step10.outerStart n < log (n : ℝ) :=
    log_lt_log (zero_lt_one.trans hnshift) (by linarith)
  have hrUpperLog : log rPlus < log (exp 1 * sqrt (n : ℝ)) := by
    have hloglt : log (x d) < log (n : ℝ) + 2 := by
      linarith only [hlog₂, hshiftlog]
    dsimp [rPlus]
    rw [log_sqrt hx₀.le, log_mul (exp_ne_zero 1) (sqrt_pos.2 hn').ne',
      log_exp, log_sqrt hn'.le]
    linarith only [hloglt]
  have hrUpper : rPlus < exp 1 * sqrt (n : ℝ) :=
    (log_lt_log_iff (zero_lt_one.trans hr₁) (by positivity)).mp hrUpperLog
  have hπ : (0.48 : ℝ) < π := by linarith only [pi_gt_three]
  have hphase' : ((d : ℝ) - 1) * π < Step06.saddlePhase n rPlus := by
    have hlowPhase : -0.48 < Step06.saddlePhase n rPlus - π * d := (abs_lt.mp hphase).1
    linarith only [hlowPhase, hπ]
  refine ⟨d, rPlus, hd₁₀, hdm', hr₁, hrUpper, ?_, hphase', roots, ?_⟩
  · rw [hsq, realSign_eq_signType]
    exact (hsign d le_rfl hdm').2
  · simpa only [hsq] using hroots

end DurfeeCCS.Step11
