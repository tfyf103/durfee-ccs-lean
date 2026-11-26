module

public import DurfeeCCS.Step07.ElementaryBounds

meta import DurfeeCCS.Step07.SqrtInterval
meta import DurfeeCCS.Step07.ThetaBoundsIntervals
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-! The explicit error functions for pages 14 and 18–23 and their numerical certificates. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open Real

/-- Integrating the three terms on page 16 against the half-integer Gamma density. -/
def firstSaddleC (γ : ℝ) : ℝ :=
  √1.5 * (1.845 / γ ^ 2 + 0.435 / γ + 2.7742) / √γ

/-- The error majorant in Lemma 3.4. -/
def firstSaddleE (ω γ : ℝ) : ℝ :=
  firstSaddleC γ / ω + (11.1 / γ + 2.4) / √ω * exp (-0.3 * γ * ω) +
    19 * ω ^ 2 * exp (-ω)

/-- The bound on the last term of (40) after division by `Mₙ(r)`. -/
def firstSaddleL16 (ω : ℝ) : ℝ := 0.102 * ω ^ 3 * exp (-0.873 * ω)

/-- Upper bound on the real part of the saddle coordinate (\zeta). -/
def firstSaddleU0 (r : ℝ) : ℝ := √(r * (1 + 0.282 * r) / 6400)

def firstSaddleB (r ω : ℝ) : ℝ :=
  let d := 5 * r * firstSaddleU0 r / (2 * (1 - r))
  let e := 257 * r * firstSaddleU0 r / (4 * (1 - r))
  0.75 * π * √(20 / 0.55) * (exp d - 1) +
    2.25 * ω * (exp d - 1) * exp (-(1 - r / 2) * ω) +
    19.5 * ω * (exp e - 1) * exp (-0.4 * ω)

def firstSaddleU (r ω : ℝ) : ℝ :=
  3 * π * ω ^ 3 / (4 * (1 - r ^ 2)) *
    exp (-(1 - π / 16 - r / (2 * (1 - r))) * ω)

theorem antitoneOn_firstSaddleE {γ m : ℝ} (hγ : 0 < γ) (hm : 2 ≤ m) :
    AntitoneOn (fun ω => firstSaddleE ω γ) (Set.Ici m) := by
  intro x hx y hy hxy
  have hx₀ : 0 < x := (by linarith : 0 < m).trans_le hx
  have hC : 0 ≤ firstSaddleC γ := by unfold firstSaddleC; positivity
  have h₀ := div_le_div_of_nonneg_left hC hx₀ hxy
  have hs := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 11.1 / γ + 2.4) (Real.sqrt_pos.2 hx₀) (Real.sqrt_le_sqrt hxy)
  have he : exp (-0.3 * γ * y) ≤ exp (-0.3 * γ * x) := by
    rw [exp_le_exp]
    nlinarith [mul_nonneg hγ.le (sub_nonneg.mpr hxy)]
  have h₁ := mul_le_mul hs he (Real.exp_nonneg _) (by positivity)
  have h₂ := antitoneOn_pow_mul_exp_neg 2 (b := 1) (m := m) (by norm_num)
    (by linarith) (by simpa using hm) hx hy hxy
  simp only [neg_mul, one_mul] at h₂
  change firstSaddleE y γ ≤ firstSaddleE x γ
  unfold firstSaddleE
  nlinarith

theorem antitoneOn_firstSaddleL16 :
    AntitoneOn firstSaddleL16 (Set.Ici 12) := by
  intro x hx y hy hxy
  have h := antitoneOn_pow_mul_exp_neg 3 (b := 0.873) (m := 12)
    (by norm_num) (by norm_num) (by norm_num) hx hy hxy
  change firstSaddleL16 y ≤ firstSaddleL16 x
  unfold firstSaddleL16
  linarith

theorem antitoneOn_firstSaddleB {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 0.25) :
    AntitoneOn (firstSaddleB r) (Set.Ici 12) := by
  intro x hx y hy hxy
  let d := 5 * r * firstSaddleU0 r / (2 * (1 - r))
  let e := 257 * r * firstSaddleU0 r / (4 * (1 - r))
  have hr₁ : 0 < 1 - r := by linarith
  have hd : 0 ≤ d := by dsimp [d, firstSaddleU0]; positivity
  have he : 0 ≤ e := by dsimp [e, firstSaddleU0]; positivity
  have hdp := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hd)
  have hep := sub_nonneg.mpr (Real.one_le_exp_iff.mpr he)
  have h₁ := antitoneOn_pow_mul_exp_neg 1 (b := 1 - r / 2) (m := 12)
    (by linarith) (by norm_num) (by norm_num; linarith) hx hy hxy
  have h₂ := antitoneOn_pow_mul_exp_neg 1 (b := 0.4) (m := 12)
    (by norm_num) (by norm_num) (by norm_num) hx hy hxy
  simp only [pow_one] at h₁ h₂
  have h₁' := mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ 2.25 * (exp d - 1))
  have h₂' := mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ 19.5 * (exp e - 1))
  change 0.75 * π * √(20 / 0.55) * (exp d - 1) +
      2.25 * y * (exp d - 1) * exp (-(1 - r / 2) * y) +
      19.5 * y * (exp e - 1) * exp (-0.4 * y) ≤
    0.75 * π * √(20 / 0.55) * (exp d - 1) +
      2.25 * x * (exp d - 1) * exp (-(1 - r / 2) * x) +
      19.5 * x * (exp e - 1) * exp (-0.4 * x)
  linarith only [h₁', h₂']

theorem antitoneOn_firstSaddleU {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 0.25) :
    AntitoneOn (firstSaddleU r) (Set.Ici 12) := by
  intro x hx y hy hxy
  let b := 1 - π / 16 - r / (2 * (1 - r))
  have hr₁ : 0 < 1 - r := by linarith
  have hd : r / (2 * (1 - r)) ≤ 1 / 6 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hb : 0.63 ≤ b := by dsimp [b]; linarith [Real.pi_lt_d2]
  have hm : 0 < 1 - r ^ 2 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr')]
  have hmono := antitoneOn_pow_mul_exp_neg 3 (b := b) (m := 12)
    (by linarith) (by norm_num) (by norm_num; linarith) hx hy hxy
  have h := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 3 * π / (4 * (1 - r ^ 2)))
  simpa only [firstSaddleU, b, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

theorem firstSaddleE_40 : firstSaddleE 40 0.55 < 0.404 := by
  unfold firstSaddleE firstSaddleC
  dyadic_interval +kernel [prec := 40]

theorem firstSaddleE_sqrt3840 : firstSaddleE (√3840) 0.55 < 0.258 := by
  unfold firstSaddleE firstSaddleC
  dyadic_interval +kernel [prec := 40]

theorem firstSaddleE_sqrt32256div5 : firstSaddleE (√(32256 / 5)) 0.55 < 0.199 := by
  unfold firstSaddleE firstSaddleC
  dyadic_interval +kernel [prec := 40]

theorem firstSaddleL16_40 : firstSaddleL16 40 < 0.001 := by
  unfold firstSaddleL16
  dyadic_interval +kernel [prec := 40]

theorem firstSaddleTable_row1 :
    firstSaddleB 0.03 (4 * π) < 0.0094 ∧
      firstSaddleU 0.03 (4 * π) < 0.234 ∧
      firstSaddleL16 (4 * π) < 0.0035 ∧ firstSaddleE (4 * π) 0.99 < 0.602 := by
  have hlo := pi_gt_d20
  have hhi := pi_lt_d20
  unfold firstSaddleB firstSaddleU firstSaddleU0 firstSaddleL16 firstSaddleE firstSaddleC
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dyadic_interval +kernel [prec := 40]

theorem firstSaddleTable_row2 :
    firstSaddleB 0.1 (√192) < 0.047 ∧
      firstSaddleU 0.1 (√192) < 0.200 ∧
      firstSaddleL16 (√192) < 0.0016 ∧ firstSaddleE (√192) 0.99 < 0.516 := by
  have hlo := pi_gt_d20
  have hhi := pi_lt_d20
  unfold firstSaddleB firstSaddleU firstSaddleU0 firstSaddleL16 firstSaddleE firstSaddleC
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dyadic_interval +kernel [prec := 40]

theorem firstSaddleTable_row3 :
    firstSaddleB 0.25 (√640) < 0.080 ∧
      firstSaddleU 0.25 (√640) < 0.0041 ∧
      firstSaddleL16 (√640) < 0.000001 ∧ firstSaddleE (√640) 0.55 < 0.700 := by
  have hlo := pi_gt_d20
  have hhi := pi_lt_d20
  unfold firstSaddleB firstSaddleU firstSaddleU0 firstSaddleL16 firstSaddleE firstSaddleC
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dyadic_interval +kernel [prec := 40]

def firstSaddleTableSum (r ω γ : ℝ) : ℝ :=
  firstSaddleB r ω + firstSaddleU r ω + firstSaddleL16 ω + firstSaddleE ω γ

theorem antitoneOn_firstSaddleTableSum {r γ : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 0.25)
    (hγ : 0 < γ) : AntitoneOn (fun ω => firstSaddleTableSum r ω γ) (Set.Ici 12) := by
  intro x hx y hy hxy
  have hB := antitoneOn_firstSaddleB hr hr' hx hy hxy
  have hU := antitoneOn_firstSaddleU hr hr' hx hy hxy
  have hL := antitoneOn_firstSaddleL16 hx hy hxy
  have hE := antitoneOn_firstSaddleE hγ (m := 12) (by norm_num) hx hy hxy
  unfold firstSaddleTableSum
  linarith only [hB, hU, hL, hE]

theorem firstSaddleTable_row1_sum {ω : ℝ} (hω : 4 * π ≤ ω) :
    firstSaddleTableSum 0.03 ω 0.99 < 0.849 := by
  have h₀ : (12 : ℝ) ≤ 4 * π := by linarith [pi_gt_d2]
  refine (antitoneOn_firstSaddleTableSum (by norm_num) (by norm_num) (by norm_num)
    h₀ (h₀.trans hω) hω).trans_lt ?_
  obtain ⟨hB, hU, hL, hE⟩ := firstSaddleTable_row1
  unfold firstSaddleTableSum
  linarith only [hB, hU, hL, hE]

theorem firstSaddleTable_row2_sum {ω : ℝ} (hω : √192 ≤ ω) :
    firstSaddleTableSum 0.1 ω 0.99 < 0.765 := by
  have h₀ : (12 : ℝ) ≤ √192 := le_sqrt_of_sq_le (by norm_num)
  refine (antitoneOn_firstSaddleTableSum (by norm_num) (by norm_num) (by norm_num)
    h₀ (h₀.trans hω) hω).trans_lt ?_
  obtain ⟨hB, hU, hL, hE⟩ := firstSaddleTable_row2
  unfold firstSaddleTableSum
  linarith only [hB, hU, hL, hE]

theorem firstSaddleTable_row3_sum {ω : ℝ} (hω : √640 ≤ ω) :
    firstSaddleTableSum 0.25 ω 0.55 < 0.785 := by
  have h₀ : (12 : ℝ) ≤ √640 := le_sqrt_of_sq_le (by norm_num)
  refine (antitoneOn_firstSaddleTableSum (by norm_num) (by norm_num) (by norm_num)
    h₀ (h₀.trans hω) hω).trans_lt ?_
  obtain ⟨hB, hU, hL, hE⟩ := firstSaddleTable_row3
  unfold firstSaddleTableSum
  linarith only [hB, hU, hL, hE]

end DurfeeCCS.Step07
