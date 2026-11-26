module

public import DurfeeCCS.Step10.OuterErrorModes
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! The positive product and its logarithmic bound on page 46. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real

/-- The logarithmic decay rate in the correction weight on page 46. -/
def outerWeightSigma (Y h : ℝ) : ℝ := ((outerRho h π).re - 4 / Y) / (2 * Y)

/-- The argument w q^(m+1/2) in a factor of the correction product. -/
def outerWeightArgument (w σ : ℝ) (m : ℕ) : ℝ := w * Real.exp (-σ * ((m : ℝ) + 1 / 2))

/-- The product summing the majorants of the correction weights. -/
def outerWeightProduct (w σ : ℝ) : ℝ :=
  ∏' m : ℕ, ((1 - outerWeightArgument w σ m)⁻¹) ^ 2

/-- The positive dilogarithm series at w. -/
def outerWeightDilog (w : ℝ) : ℝ := ∑' l : ℕ, w ^ (l + 1) / ((l : ℝ) + 1) ^ 2

private theorem outerWeightDilog_summable {w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 1) :
    Summable (fun l : ℕ => w ^ (l + 1) / ((l : ℝ) + 1) ^ 2) := by
  apply ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hw₀ hw)).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    apply div_le_self (by positivity)
    have hn := Nat.cast_nonneg (α := ℝ) n
    nlinarith

private theorem outerWeightDilog_le {w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 1) :
    outerWeightDilog w ≤ w * (1 + w / (4 * (1 - w))) := by
  let f (n : ℕ) := w ^ (n + 1) / ((n : ℝ) + 1) ^ 2
  have hf : Summable f := outerWeightDilog_summable hw₀ hw
  have ht : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).2 hf
  have hgeom := (summable_geometric_of_lt_one hw₀ hw).mul_left (w ^ 2 / 4)
  have hpoint (n : ℕ) : f (n + 1) ≤ (w ^ 2 / 4) * w ^ n := by
    dsimp [f]
    rw [show n + 1 + 1 = 2 + n by omega, pow_add]
    push_cast
    have hp : (4 : ℝ) ≤ ((n : ℝ) + 1 + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    rw [show w ^ 2 / 4 * w ^ n = (w ^ 2 * w ^ n) / 4 by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hp
  have hsum := ht.tsum_le_tsum hpoint hgeom
  rw [tsum_mul_left, tsum_geometric_of_lt_one hw₀ hw] at hsum
  unfold outerWeightDilog
  change (∑' n, f n) ≤ _
  rw [← ht.sum_add_tsum_nat_add', Finset.sum_range_one]
  calc
    _ ≤ f 0 + (w ^ 2 / 4 * (1 - w)⁻¹) := add_le_add le_rfl hsum
    _ = _ := by simp [f]; field_simp

private theorem outerWeightArgument_nonneg_lt_one {w σ : ℝ} (hw₀ : 0 ≤ w) (hw : w < 1)
    (hσ : 0 < σ) (m : ℕ) : 0 ≤ outerWeightArgument w σ m ∧ outerWeightArgument w σ m < 1 := by
  have hex : Real.exp (-σ * ((m : ℝ) + 1 / 2)) ≤ 1 :=
    exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ.le) (by positivity))
  exact ⟨by unfold outerWeightArgument; positivity, (mul_le_of_le_one_right hw₀ hex).trans_lt hw⟩

private theorem outerWeightLogMode {w σ : ℝ} (hσ : 0 < σ) (l : ℕ) :
    HasSum (fun m : ℕ => 2 * outerWeightArgument w σ m ^ (l + 1) / ((l : ℝ) + 1))
      (w ^ (l + 1) / (((l : ℝ) + 1) * Real.sinh (σ * ((l : ℝ) + 1) / 2))) := by
  let d := (l : ℝ) + 1
  let x := σ * d / 2
  let a := Real.exp (-x)
  have hd : 0 < d := by dsimp [d]; positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have ha₀ : 0 < a := exp_pos _
  have ha₁ : a < 1 := exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  have ha₂ : a ^ 2 < 1 := pow_lt_one₀ ha₀.le ha₁ two_ne_zero
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg a) ha₂).mul_left
    (2 * w ^ (l + 1) * a / d)
  have hterms (m : ℕ) :
      2 * w ^ (l + 1) * a / d * (a ^ 2) ^ m =
        2 * outerWeightArgument w σ m ^ (l + 1) / d := by
    have he : (a ^ 2) ^ m = exp (-(m : ℝ) * (2 * x)) := by
      dsimp [a]
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he, outerWeightArgument, mul_pow, ← Real.exp_nat_mul]
    calc
      _ = 2 * w ^ (l + 1) * (exp (-x) * exp (-(m : ℝ) * (2 * x))) / d := by
        dsimp [a]
        ring
      _ = _ := by
        rw [← Real.exp_add]
        rw [show -x + -(m : ℝ) * (2 * x) = ((l + 1 : ℕ) : ℝ) * (-σ * ((m : ℝ) + 1 / 2)) by
          dsimp [x, d]
          push_cast
          ring]
        ring
  have hS : Real.sinh x = (1 - a ^ 2) / (2 * a) := by
    rw [Real.sinh_eq, ← show a = exp (-x) from rfl, show exp x = a⁻¹ by simp [a, Real.exp_neg]]
    field_simp [ha₀.ne']
  convert hgeom.congr_fun (fun m => (hterms m).symm) using 1
  change w ^ (l + 1) / (d * Real.sinh x) = 2 * w ^ (l + 1) * a / d * (1 - a ^ 2)⁻¹
  rw [hS]
  field_simp [ha₀.ne', hd.ne', (sub_pos.mpr ha₂).ne']

/-- The exact logarithmic series and the dilogarithm majorant on page 46. -/
theorem outerWeightProduct_log {w σ : ℝ} (hw₀ : 0 ≤ w) (hw : w < 1) (hσ : 0 < σ) :
    0 < outerWeightProduct w σ ∧
    Real.log (outerWeightProduct w σ) =
      ∑' l : ℕ, w ^ (l + 1) / (((l : ℝ) + 1) * Real.sinh (σ * ((l : ℝ) + 1) / 2)) ∧
    Real.log (outerWeightProduct w σ) ≤ (2 / σ) * outerWeightDilog w := by
  let L (l : ℕ) := w ^ (l + 1) / (((l : ℝ) + 1) * Real.sinh (σ * ((l : ℝ) + 1) / 2))
  let D (l : ℕ) := w ^ (l + 1) / ((l : ℝ) + 1) ^ 2
  let F (l m : ℕ) := 2 * outerWeightArgument w σ m ^ (l + 1) / ((l : ℝ) + 1)
  let P (m : ℕ) := ((1 - outerWeightArgument w σ m)⁻¹) ^ 2
  have hL₀ (l : ℕ) : 0 ≤ L l := by
    dsimp [L]
    exact div_nonneg (by positivity) (mul_nonneg (by positivity)
      (Real.sinh_nonneg_iff.mpr (by positivity)))
  have hmain (l : ℕ) : L l ≤ (2 / σ) * D l := by
    have hd : 0 < (l : ℝ) + 1 := by positivity
    have hs := Real.self_le_sinh_iff.mpr (show 0 ≤ σ * ((l : ℝ) + 1) / 2 by positivity)
    dsimp [L, D]
    calc
      _ ≤ w ^ (l + 1) / (((l : ℝ) + 1) * (σ * ((l : ℝ) + 1) / 2)) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hs hd.le)
      _ = _ := by field_simp
  have hD : Summable D := outerWeightDilog_summable hw₀ hw
  have hL : Summable L := (hD.mul_left (2 / σ)).of_nonneg_of_le hL₀ hmain
  have hFm (l : ℕ) : HasSum (F l) (L l) := outerWeightLogMode hσ l
  have hFl (m : ℕ) : HasSum (fun l => F l m) (Real.log (P m)) := by
    have hp := outerWeightArgument_nonneg_lt_one hw₀ hw hσ m
    have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one
      (show |outerWeightArgument w σ m| < 1 by rw [abs_of_nonneg hp.1]; exact hp.2)).mul_left 2
    have hlogval : Real.log (P m) = 2 * (-log (1 - outerWeightArgument w σ m)) := by
      unfold P
      rw [Real.log_pow, Real.log_inv]
      norm_num
    rw [hlogval]
    convert hlog using 1
    funext l
    dsimp [F]
    ring
  have hF : Summable (fun p : ℕ × ℕ => F p.1 p.2) := by
    refine (summable_prod_of_nonneg (fun p => ?_)).2 ⟨fun l => (hFm l).summable, ?_⟩
    · have hp := (outerWeightArgument_nonneg_lt_one hw₀ hw hσ p.2).1
      dsimp [F]
      positivity
    · exact hL.congr (fun l => (hFm l).tsum_eq.symm)
  have hLogs : Summable (fun m => Real.log (P m)) :=
    (hF.prod_symm.prod).congr (fun m => (hFl m).tsum_eq)
  have hAll : (∑' m, Real.log (P m)) = ∑' l, L l := by
    simp_rw [← (hFl _).tsum_eq, ← (hFm _).tsum_eq]
    exact hF.tsum_comm
  have hpos (m : ℕ) : 0 < P m := by
    dsimp only [P]
    have hp := (outerWeightArgument_nonneg_lt_one hw₀ hw hσ m).2
    positivity
  have hprod := Real.rexp_tsum_eq_tprod hpos hLogs
  change Real.exp (∑' m, Real.log (P m)) = outerWeightProduct w σ at hprod
  refine ⟨hprod ▸ exp_pos _, ?_, ?_⟩
  · rw [← hprod, log_exp]
    exact hAll
  · rw [← hprod, log_exp, hAll]
    have H := hL.tsum_le_tsum hmain (hD.mul_left (2 / σ))
    rwa [tsum_mul_left] at H

theorem outerWeightSigma_pos {Y h : ℝ} (hY : 80 ≤ Y) (hh : 2 * log Y ≤ h) :
    0 < outerWeightSigma Y h := by
  have hY₀ : 0 < Y := by linarith
  have hh₀ : 8.76 < h := by
    have H := DurfeeCCS.Step07.outerEightyLog_gt.trans_le (Real.log_le_log (by norm_num) hY)
    linarith
  have hR := outerRho_re_gt (t := π) (show 0 < h by linarith)
  have hdiv : 4 / Y ≤ (4 : ℝ) / 80 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hY
  unfold outerWeightSigma
  exact div_pos (by linarith) (by positivity)

/-- The correction product has strict logarithmic bound 0.461. -/
theorem outerWeightProduct_cap {Y h : ℝ} (hY : 80 ≤ Y) (hh : 2 * log Y ≤ h) :
    outerWeightProduct (Real.exp (-h / 2)) (outerWeightSigma Y h) < Real.exp 0.461 := by
  let w := Real.exp (-h / 2)
  let σ := outerWeightSigma Y h
  have hY₀ : 0 < Y := by linarith
  have hh₀ : 8.76 < h := by
    have H := DurfeeCCS.Step07.outerEightyLog_gt.trans_le (Real.log_le_log (by norm_num) hY)
    linarith
  have hw : w ≤ 1 / Y := by
    have H := Real.exp_le_exp.mpr (show -h / 2 ≤ -Real.log Y by linarith)
    rwa [Real.exp_neg, Real.exp_log hY₀, ← one_div] at H
  have hw₀ : 0 < w := exp_pos _
  have hw₁ : w < 1 := hw.trans_lt ((div_lt_one hY₀).2 (by linarith))
  have hσ : 0 < σ := outerWeightSigma_pos hY hh
  have hR := outerRho_re_gt (t := π) (show 0 < h by linarith)
  have hd : 4 / Y ≤ (4 : ℝ) / 80 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hY
  have hσY : (8.71 : ℝ) < σ * (2 * Y) := by
    dsimp [σ, outerWeightSigma]
    rw [div_mul_cancel₀ _ (by positivity : (2 * Y : ℝ) ≠ 0)]
    linarith
  have hbase := (outerWeightProduct_log hw₀.le hw₁ hσ)
  rw [← Real.exp_log hbase.1, Real.exp_lt_exp]
  calc
    _ ≤ (2 / σ) * outerWeightDilog w := hbase.2.2
    _ ≤ (2 / σ) * (w * (1 + w / (4 * (1 - w)))) := by
      gcongr
      exact outerWeightDilog_le hw₀.le hw₁
    _ ≤ 4 / 8.71 * (1 + 1 / (4 * 79)) := by
      have h1 : 2 / σ * w ≤ 4 / 8.71 := by
        calc
          _ ≤ 2 / σ * (1 / Y) := by gcongr
          _ = 4 / (σ * (2 * Y)) := by ring
          _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hσY.le
      have h2 : w / (4 * (1 - w)) ≤ 1 / (4 * 79) := by
        have hw' := hw.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num : (0 : ℝ) < 80) hY)
        calc
          _ ≤ (1 / 80 : ℝ) / (4 * (1 - 1 / 80)) :=
            div_le_div₀ (by norm_num) hw' (by norm_num) (by linarith)
          _ = _ := by norm_num
      rw [← mul_assoc]
      exact mul_le_mul h1 (add_le_add le_rfl h2) (by positivity) (by norm_num)
    _ < _ := by norm_num

end DurfeeCCS.Step10
