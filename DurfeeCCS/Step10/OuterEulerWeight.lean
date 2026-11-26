module

public import DurfeeCCS.Step10.OuterEulerWeightLog
public import DurfeeCCS.Step06.GeneratingAnalytic
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-! Euler's reciprocal-product identity for the positive correction weights. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset Filter
open scoped Topology

/-- The finite real product (q;q)_n in the reciprocal Euler series. -/
def outerWeightQFactorial (q : ℝ) (n : ℕ) : ℝ :=
  ∏ m ∈ range n, (1 - q ^ (m + 1))

theorem outerWeightQFactorial_cast (q : ℝ) (n : ℕ) :
    (outerWeightQFactorial q n : ℂ) = DurfeeCCS.qPochhammer q q n := by
  rw [DurfeeCCS.qPochhammer_self_eq_prod]
  simp [outerWeightQFactorial]

theorem outerWeightQFactorial_pos {q : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1) (n : ℕ) :
    0 < outerWeightQFactorial q n := by
  unfold outerWeightQFactorial
  apply Finset.prod_pos
  intro m hm
  exact sub_pos.mpr (pow_lt_one₀ hq₀ hq (by omega))

private theorem outerWeightQFactorial_succ (q : ℝ) (n : ℕ) :
    outerWeightQFactorial q (n + 1) = outerWeightQFactorial q n * (1 - q ^ (n + 1)) := by
  unfold outerWeightQFactorial
  rw [prod_range_succ]

private theorem outerEuler_prod_converges {q x : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1)
    (hx₀ : 0 ≤ x) (hx : x < 1) :
    let f (n : ℕ) := 1 - x * q ^ n
    Multipliable f ∧ (∏' n, f n) ≠ 0 := by
  dsimp only
  have hS : Summable (fun n : ℕ => ‖x * q ^ n‖) := by
    simp_rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hx₀, abs_of_nonneg hq₀]
    exact (summable_geometric_of_lt_one hq₀ hq).mul_left x
  have hpos (n : ℕ) : 0 < 1 - x * q ^ n :=
    sub_pos.mpr ((mul_le_of_le_one_right hx₀ (pow_le_one₀ hq₀ hq.le)).trans_lt hx)
  refine ⟨multipliable_one_sub_of_summable hS, ?_⟩
  simpa only [← sub_eq_add_neg] using
    (tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(x * q ^ n))
      (by simpa only [← sub_eq_add_neg] using fun n => (hpos n).ne')
      (by simpa only [norm_neg] using hS))

/-- The reciprocals of the real finite products share a uniform bound. -/
theorem outerWeightInvQFactorial_bounded {q : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, (outerWeightQFactorial q n)⁻¹ ≤ C := by
  have H := outerEuler_prod_converges hq₀ hq hq₀ hq
  have hprod : Tendsto (outerWeightQFactorial q) atTop (𝓝 (∏' n : ℕ, (1 - q * q ^ n))) := by
    change Tendsto (fun n => ∏ i ∈ range n, (1 - q ^ (i + 1))) atTop _
    simpa only [pow_succ'] using H.1.hasProd.tendsto_prod_nat
  have hi := hprod.inv₀ H.2
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hi)
  refine ⟨C, (norm_nonneg _).trans (hC _ ⟨0, rfl⟩), ?_⟩
  intro n
  simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (outerWeightQFactorial_pos hq₀ hq n))] using
    hC ((outerWeightQFactorial q n)⁻¹) ⟨n, rfl⟩

/-- The coefficients of the unilateral reciprocal Euler series. -/
def outerEulerTerm (q x : ℝ) (n : ℕ) : ℝ := x ^ n / outerWeightQFactorial q n

/-- The unilateral reciprocal Euler series. -/
def outerEulerSeries (q x : ℝ) : ℝ := ∑' n : ℕ, outerEulerTerm q x n

theorem outerEulerTerm_summable {q x : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1)
    (hx₀ : 0 ≤ x) (hx : x < 1) : Summable (outerEulerTerm q x) := by
  obtain ⟨C, hC, hB⟩ := outerWeightInvQFactorial_bounded hq₀ hq
  apply ((summable_geometric_of_lt_one hx₀ hx).mul_right C).of_nonneg_of_le
  · intro n
    exact div_nonneg (pow_nonneg hx₀ _) (outerWeightQFactorial_pos hq₀ hq _).le
  · intro n
    exact mul_le_mul_of_nonneg_left (hB n) (pow_nonneg hx₀ _)

private theorem outerEuler_term_difference {q x : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1) (n : ℕ) :
    outerEulerTerm q x (n + 1) - outerEulerTerm q (x * q) (n + 1) =
      x * outerEulerTerm q x n := by
  have hQ := outerWeightQFactorial_pos hq₀ hq n
  have hP : 0 < 1 - q ^ (n + 1) := sub_pos.mpr (pow_lt_one₀ hq₀ hq (by omega))
  unfold outerEulerTerm
  rw [mul_pow, outerWeightQFactorial_succ, pow_succ x]
  field_simp [hQ.ne', hP.ne']

@[simp] theorem outerEulerTerm_zero (q x : ℝ) : outerEulerTerm q x 0 = 1 := by
  simp [outerEulerTerm, outerWeightQFactorial]

private theorem outerEuler_step {q x : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1)
    (hx₀ : 0 ≤ x) (hx : x < 1) :
    (1 - x) * outerEulerSeries q x = outerEulerSeries q (x * q) := by
  have hqx₀ : 0 ≤ x * q := by positivity
  have hqx : x * q < 1 := (mul_le_of_le_one_right hx₀ hq.le).trans_lt hx
  have h₁ := outerEulerTerm_summable hq₀ hq hx₀ hx
  have h₂ := outerEulerTerm_summable hq₀ hq hqx₀ hqx
  have hs₁ := (summable_nat_add_iff 1).2 h₁
  have hs₂ := (summable_nat_add_iff 1).2 h₂
  have e₁ : outerEulerSeries q x = 1 + ∑' n, outerEulerTerm q x (n + 1) := by
    rw [outerEulerSeries, ← hs₁.sum_add_tsum_nat_add', Finset.sum_range_one, outerEulerTerm_zero]
  have e₂ : outerEulerSeries q (x * q) = 1 + ∑' n, outerEulerTerm q (x * q) (n + 1) := by
    rw [outerEulerSeries, ← hs₂.sum_add_tsum_nat_add', Finset.sum_range_one, outerEulerTerm_zero]
  have H : outerEulerSeries q x - outerEulerSeries q (x * q) = x * outerEulerSeries q x := by
    conv_lhs => rw [e₁, e₂, add_sub_add_left_eq_sub, ← hs₁.tsum_sub hs₂]
    simp_rw [outerEuler_term_difference hq₀ hq, tsum_mul_left]
    rfl
  linarith

/-- Euler's reciprocal-product formula for nonnegative q and x below one. -/
theorem outerEulerSeries_eq_inv_tprod {q x : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1)
    (hx₀ : 0 ≤ x) (hx : x < 1) :
    outerEulerSeries q x = (∏' m : ℕ, (1 - x * q ^ m))⁻¹ := by
  let f (n : ℕ) := 1 - x * q ^ n
  let P := ∏' n, f n
  have hprod := outerEuler_prod_converges hq₀ hq hx₀ hx
  have hfin (n : ℕ) :
      (∏ m ∈ Finset.range n, f m) * outerEulerSeries q x = outerEulerSeries q (x * q ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, mul_right_comm, ih, pow_succ q]
      change (outerEulerSeries q (x * q ^ n)) * (1 - x * q ^ n) =
        outerEulerSeries q (x * (q ^ n * q))
      rw [← mul_assoc, mul_comm (outerEulerSeries q (x * q ^ n))]
      exact outerEuler_step hq₀ hq (mul_nonneg hx₀ (pow_nonneg hq₀ _))
        ((mul_le_of_le_one_right hx₀ (pow_le_one₀ hq₀ hq.le)).trans_lt hx)
  let F (n : ℕ) : ℝ := if n = 0 then 1 else 0
  have htq : Tendsto (fun n : ℕ => x * q ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq).const_mul x
  have hpoint (n : ℕ) : Tendsto (fun m => outerEulerTerm q (x * q ^ m) n) atTop (𝓝 (F n)) := by
    by_cases hn : n = 0
    · simp [hn, F]
    · simpa only [outerEulerTerm, F, ite_eq_right hn, zero_pow hn, zero_div] using
        (htq.pow n).div_const (outerWeightQFactorial q n)
  obtain ⟨C, hC, hB⟩ := outerWeightInvQFactorial_bounded hq₀ hq
  have hdom (m n : ℕ) : ‖outerEulerTerm q (x * q ^ m) n‖ ≤ x ^ n * C := by
    have hqpow := pow_nonneg hq₀ m
    have hP := outerWeightQFactorial_pos hq₀ hq n
    have hQ : 0 ≤ (x * q ^ m) ^ n := by positivity
    rw [outerEulerTerm, Real.norm_of_nonneg (div_nonneg hQ hP.le), div_eq_mul_inv]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity)
      (mul_le_of_le_one_right hx₀ (pow_le_one₀ hq₀ hq.le)) _) (hB n) (by positivity) (by positivity)
  have htS := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one hx₀ hx).mul_right C)
    hpoint (Eventually.of_forall hdom)
  have hF : (∑' n, F n) = 1 := by
    rw [tsum_eq_single 0]
    · simp [F]
    · intro n hn
      simp [F, hn]
  rw [hF] at htS
  have htP : Tendsto (fun n => (∏ m ∈ Finset.range n, f m) * outerEulerSeries q x)
      atTop (𝓝 (P * outerEulerSeries q x)) :=
    hprod.1.hasProd.tendsto_prod_nat.mul_const _
  have H : P * outerEulerSeries q x = 1 := tendsto_nhds_unique htP (htS.congr (fun n => (hfin n).symm))
  have hP : P ≠ 0 := hprod.2
  change outerEulerSeries q x = P⁻¹
  apply mul_left_cancel₀ hP
  rw [H, mul_inv_cancel₀ hP]

/-- The square of the reciprocal Euler series is the page 46 product. -/
theorem outerEulerSeries_sq_eq_weightProduct {w σ : ℝ} (hw₀ : 0 ≤ w) (hw : w < 1) (hσ : 0 < σ) :
    let q := Real.exp (-σ)
    let x := w * Real.exp (-σ / 2)
    outerEulerSeries q x ^ 2 = outerWeightProduct w σ := by
  dsimp only
  let q := Real.exp (-σ)
  let x := w * Real.exp (-σ / 2)
  have hq₀ : 0 ≤ q := exp_nonneg _
  have hq : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have hx₀ : 0 ≤ x := mul_nonneg hw₀ (exp_nonneg _)
  have hx : x < 1 := (mul_le_of_le_one_right hw₀ (exp_le_one_iff.mpr (by linarith))).trans_lt hw
  have ht (n : ℕ) : x * q ^ n = outerWeightArgument w σ n := by
    unfold outerWeightArgument
    dsimp only [q, x]
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hp := outerEuler_prod_converges hq₀ hq hx₀ hx
  rw [outerEulerSeries_eq_inv_tprod hq₀ hq hx₀ hx]
  change _ = ∏' n, ((1 - outerWeightArgument w σ n)⁻¹) ^ 2
  simp_rw [← ht]
  rw [(hp.1.inv₀ hp.2).tprod_pow, hp.1.tprod_inv₀ hp.2]

end DurfeeCCS.Step10
