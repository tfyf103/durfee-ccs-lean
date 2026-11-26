module

public import DurfeeCCS.Step09.MidMinorGeometric
public import DurfeeCCS.Step07.MidSaddleTailRows
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! From the elementary mode bounds to the estimates in (63). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Set DurfeeCCS.Step07

private theorem x_mul_cosh_sub_sinh_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * Real.cosh x - Real.sinh x := by
  let f : ℝ → ℝ := fun y => y * Real.cosh y - Real.sinh y
  have hd (y : ℝ) : HasDerivAt f (y * Real.sinh y) y := by
    convert ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
      (Real.hasDerivAt_sinh y) using 1
    · rfl
    · simp
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hd y).deriv]
    exact mul_nonneg (interior_subset hy) (Real.sinh_nonneg_iff.mpr (interior_subset hy))
  have h := hm (show (0:ℝ) ∈ Ici 0 from le_rfl) (show x ∈ Ici 0 from hx) hx
  simpa [f] using h

theorem midMinor_coth_le {x : ℝ} (hx : 0 < x) :
    Real.cosh x / Real.sinh x ≤ 1 / x + x / 3 := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  let f : ℝ → ℝ := fun y => (1 + y ^ 2 / 3) * Real.sinh y - y * Real.cosh y
  have hd (y : ℝ) : HasDerivAt f (y / 3 * (y * Real.cosh y - Real.sinh y)) y := by
    have hb := (((hasDerivAt_id y).pow 2).div_const 3).const_add 1
    convert (hb.mul (Real.hasDerivAt_sinh y)).sub ((hasDerivAt_id y).mul
      (Real.hasDerivAt_cosh y)) using 1
    · funext z
      simp [f, div_eq_mul_inv]
    · simp only [id_eq, Pi.pow_apply]
      norm_num
      ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hd y).deriv]
    have hy₀ : 0 ≤ y := interior_subset hy
    exact mul_nonneg (by positivity) (x_mul_cosh_sub_sinh_nonneg hy₀)
  have h : 0 ≤ f x := by
    simpa [f] using hm (show (0:ℝ) ∈ Ici 0 from le_rfl) (show x ∈ Ici 0 from hx.le) hx.le
  rw [div_le_iff₀ hs]
  calc
    _ = (x * Real.cosh x) / x := by field_simp
    _ ≤ ((1 + x ^ 2 / 3) * Real.sinh x) / x :=
      div_le_div_of_nonneg_right (sub_nonneg.mp h) hx.le
    _ = _ := by field_simp

theorem midMinor_coth_le_one {x : ℝ} (hx : 0 < x) :
    Real.cosh x / Real.sinh x ≤ 1 / x + 1 := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have h : Real.exp (2*x) - 1 ≥ 2*x := by linarith [Real.add_one_le_exp (2 * x)]
  have he : Real.exp (2*x) - 1 > 0 := by linarith
  have hf : Real.cosh x / Real.sinh x = 1 + 2 / (Real.exp (2*x) - 1) := by
    have h₀ : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h₁ : Real.exp x * Real.exp x = Real.exp (2*x) := by
      rw [← Real.exp_add, two_mul]
    have hn : Real.exp x - Real.exp (-x) ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_exp.mpr (by linarith)))
    calc
      _ = (Real.exp x + Real.exp (-x)) / (Real.exp x - Real.exp (-x)) := by
        rw [Real.cosh_eq, Real.sinh_eq]
        field_simp
      _ = (Real.exp x * (Real.exp x + Real.exp (-x))) /
          (Real.exp x * (Real.exp x - Real.exp (-x))) := by
        field_simp
      _ = _ := by
        rw [mul_add, mul_sub, h₁, h₀]
        field_simp
        ring
  rw [hf, add_comm]
  apply add_le_add_left
  apply (div_le_div_iff₀ he hx).mpr
  linarith

theorem midMinor_x_div_sinh_lower {x : ℝ} (hx : 0 < x) :
    1 - x ^ 2 / 6 ≤ x / Real.sinh x := by
  by_cases h : x ^ 2 < 6
  · have h₀ : 0 < 1 - x ^ 2 / 6 := by linarith
    rw [le_div_iff₀ (Real.sinh_pos_iff.mpr hx)]
    exact (mul_comm _ _).le.trans ((le_div_iff₀ h₀).mp (minorArc_sinh_upper hx.le h))
  · exact (show 1 - x ^ 2 / 6 ≤ 0 by linarith).trans (by positivity)

theorem midMinor_x_div_sinh_antitone :
    AntitoneOn (fun x : ℝ => x / Real.sinh x) (Ioi 0) := by
  let f : ℝ → ℝ := fun x => x / Real.sinh x
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt f
      ((Real.sinh x - x * Real.cosh x) / Real.sinh x ^ 2) x := by
    convert (hasDerivAt_id x).div (Real.hasDerivAt_sinh x) (Real.sinh_pos_iff.mpr hx).ne' using 1
    · rfl
    · simp
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx₀ : 0 < x := interior_subset hx
  rw [(hd x hx₀).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (sub_nonneg.mp
    (x_mul_cosh_sub_sinh_nonneg hx₀.le))) (sq_nonneg _)

private theorem midMinor_eps_exp (j : ℕ) (t : ℝ) :
    Real.exp (-(j : ℝ) * t) = (Real.exp (-t)) ^ j := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem sinh_split (a : ℝ) :
    Real.sinh a = 2 * Real.sinh (a / 2) * Real.cosh (a / 2) := by
  calc
    _ = Real.sinh (a / 2 + a / 2) := by rw [show a/2+a/2=a by ring]
    _ = _ := by rw [Real.sinh_add]; ring

private theorem sinh_div_denominator {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.sinh a / (Real.cosh a - Real.cos b) =
      (Real.cosh (a/2) / Real.sinh (a/2)) /
        (1 + (|Real.sin (b/2)| / Real.sinh (a/2)) ^ 2) := by
  have hs : 0 < Real.sinh (a/2) := Real.sinh_pos_iff.mpr (by positivity)
  have hD : 0 < Real.cosh a - Real.cos b := midMinor_denominator_pos ha b
  rw [sinh_split,midMinor_denominator,div_pow,sq_abs]
  field_simp

theorem scaled_mode_le_c {j : ℕ} (hj : 0 < j) {u t v : ℝ} (hu : 0 < u) (ht : 0 ≤ t) :
    u * ‖midMinorMode j u t v‖ ≤ minorArcCReal (Real.exp (-t)) u j := by
  let a := (j : ℝ) * u / 2
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hC := midMinor_coth_le ha
  have hS := midMinor_x_div_sinh_lower ha
  have hN := mul_le_mul_of_nonneg_left (norm_midMinorMode_le_positive hj hu ht v) hu.le
  change u * ‖midMinorMode j u t v‖ ≤ u * (Real.cosh a / Real.sinh a -
    Real.exp (-(j : ℝ) * t) / (2 * Real.sinh a)) at hN
  apply hN.trans
  have h₁ : u * (1 / a + a / 3) = 2 / j + j * u ^ 2 / 6 := by
    dsimp [a]; field_simp; ring
  have h₂ : u * (Real.exp (-(j : ℝ) * t) / (2 * Real.sinh a)) =
      (Real.exp (-t)) ^ j / (j : ℝ) * (a / Real.sinh a) := by
    rw [midMinor_eps_exp]
    dsimp [a]
    field_simp
  unfold minorArcCReal
  rw [mul_sub, h₂]
  refine sub_le_sub ?_ ?_
  · exact (mul_le_mul_of_nonneg_left hC hu.le).trans_eq h₁
  · have hh : 1 - a^2/6 = 1 - ((j : ℝ) * u)^2/24 := by dsimp [a]; ring
    rw [← hh]
    exact mul_le_mul_of_nonneg_left hS (by positivity)

theorem scaled_mode_le_b {j : ℕ} (hj : 0 < j) {u t v : ℝ} (hu : 0 < u) (ht : 0 ≤ t)
    (hz : 0 < |Real.sin ((j : ℝ) * v / 2)|) :
    u * ‖midMinorMode j u t v‖ ≤ minorArcBReal (Real.exp (-t)) u |Real.sin ((j : ℝ) * v / 2)| j := by
  let a := (j : ℝ) * u
  let b := (j : ℝ) * v
  let z := |Real.sin (b / 2)|
  let D := Real.cosh a - Real.cos b
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : 0 < Real.sinh (a/2) := Real.sinh_pos_iff.mpr (by positivity)
  have hD : 0 < D := midMinor_denominator_pos ha b
  have hz₀ : 0 < z := hz
  have hC := midMinor_coth_le (show 0 < a/2 by positivity)
  have hN := mul_le_mul_of_nonneg_left (norm_midMinorMode_le_oscillatory hj hu ht v) hu.le
  change u * ‖midMinorMode j u t v‖ ≤ u * (Real.sinh a / D +
    Real.exp (-(j : ℝ) * t) / Real.sqrt (2 * D)) at hN
  have h₁ : u * (1 / (a/2) + (a/2) / 3) = 2 / j + j * u ^ 2 / 6 := by
    dsimp [a]; field_simp; ring
  have h₂ : 2*z ≤ Real.sqrt (2*D) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    rw [show D = _ from midMinor_denominator a b, mul_pow, show z^2 = Real.sin (b/2)^2 by simp [z,sq_abs]]
    nlinarith only [sq_nonneg (Real.sinh (a/2))]
  apply hN.trans
  unfold minorArcBReal
  change _ ≤ (2/j+j*u^2/6)/(1+(z/Real.sinh (a/2))^2)+u * (Real.exp (-t))^j/(2*z)
  rw [show D = Real.cosh a - Real.cos b from rfl, sinh_div_denominator ha b, mul_add,
    ← mul_div_assoc, ← mul_div_assoc, midMinor_eps_exp]
  refine add_le_add ?_ ?_
  · rw [mul_div_assoc]
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left hC hu.le).trans_eq h₁)
      (by positivity)
  · rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_left
      (mul_nonneg hu.le (pow_nonneg (Real.exp_nonneg _) j)) (by positivity) h₂

theorem scaled_mode_le_tail {j : ℕ} (hj : 0 < j) {u t v : ℝ} (hu : 0 < u) (ht : 0 ≤ t) :
    u * ‖midMinorMode j u t v‖ ≤ 2 / (j : ℝ) + u := by
  let a := (j : ℝ) * u / 2
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hN := mul_le_mul_of_nonneg_left (norm_midMinorMode_le_positive hj hu ht v) hu.le
  change u * ‖midMinorMode j u t v‖ ≤ u * (Real.cosh a / Real.sinh a -
    Real.exp (-(j : ℝ) * t) / (2 * Real.sinh a)) at hN
  calc
    _ ≤ _ := hN
    _ ≤ u * (Real.cosh a / Real.sinh a) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) hu.le
    _ ≤ u * (1 / a + 1) := mul_le_mul_of_nonneg_left (midMinor_coth_le_one ha) hu.le
    _ = _ := by dsimp [a]; field_simp

end DurfeeCCS.Step09
