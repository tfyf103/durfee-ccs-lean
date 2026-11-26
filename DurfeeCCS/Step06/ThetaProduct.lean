module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Analytic q-product identities used in the triple product. -/

@[expose] public section

namespace DurfeeCCS.Step06

open Filter Finset
open scoped Topology

/-- The finite product `(r; r)_n`. -/
noncomputable def qFactorial (r : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ range n, (1 - r ^ (k + 1))

private theorem qFactorial_zero (r : ℂ) : qFactorial r 0 = 1 := by
  simp [qFactorial]

private theorem qFactorial_succ (r : ℂ) (n : ℕ) :
    qFactorial r (n + 1) = qFactorial r n * (1 - r ^ (n + 1)) :=
  prod_range_succ ..

private theorem one_sub_pow_succ_ne_zero {r : ℂ} (hr : ‖r‖ < 1) (n : ℕ) :
    1 - r ^ (n + 1) ≠ 0 := by
  have h : ‖r ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hr (by omega)
  intro he
  have he' : r ^ (n + 1) = 1 := (sub_eq_zero.mp he).symm
  simp [he'] at h

private theorem qFactorial_ne_zero {r : ℂ} (hr : ‖r‖ < 1) (n : ℕ) :
    qFactorial r n ≠ 0 := by
  exact prod_ne_zero_iff.mpr fun k _ => one_sub_pow_succ_ne_zero hr k

private noncomputable def qEuler (r : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - r ^ (k + 1))

private theorem qEuler_multipliable {r : ℂ} (hr : ‖r‖ < 1) :
    Multipliable fun k : ℕ => 1 - r ^ (k + 1) := by
  refine multipliable_one_sub_of_summable ?_
  simpa only [norm_pow] using
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg r) hr)

private theorem qEuler_ne_zero {r : ℂ} (hr : ‖r‖ < 1) : qEuler r ≠ 0 := by
  unfold qEuler
  simpa only [← sub_eq_add_neg] using
    (tprod_one_add_ne_zero_of_summable (f := fun k : ℕ => -(r ^ (k + 1)))
      (by simpa only [← sub_eq_add_neg] using one_sub_pow_succ_ne_zero hr)
      (by simpa only [norm_neg, norm_pow] using
        (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg r) hr)))

private theorem tendsto_qFactorial {r : ℂ} (hr : ‖r‖ < 1) :
    Tendsto (qFactorial r) atTop (𝓝 (qEuler r)) := by
  exact (qEuler_multipliable hr).hasProd.tendsto_prod_nat

private theorem tendsto_inv_qFactorial {r : ℂ} (hr : ‖r‖ < 1) :
    Tendsto (fun n => (qFactorial r n)⁻¹) atTop (𝓝 (qEuler r)⁻¹) :=
  (tendsto_qFactorial hr).inv₀ (qEuler_ne_zero hr)

private theorem inv_qFactorial_bounded {r : ℂ} (hr : ‖r‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖(qFactorial r n)⁻¹‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ (tendsto_inv_qFactorial hr))
  exact ⟨C, (norm_nonneg _).trans (hC _ ⟨0, rfl⟩), fun n => hC _ ⟨n, rfl⟩⟩

private noncomputable def rectangleTerm (r : ℂ) (m n : ℕ) : ℂ :=
  r ^ (n * (n + m)) * (qFactorial r n)⁻¹ * (qFactorial r (n + m))⁻¹

private theorem norm_rectangleTerm_le {r : ℂ} (hr : ‖r‖ < 1) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ n, ‖(qFactorial r n)⁻¹‖ ≤ C) (m n : ℕ) :
    ‖rectangleTerm r m n‖ ≤ C ^ 2 * ‖r‖ ^ n := by
  have hn : n ≤ n * (n + m) := by
    rcases n with _ | n
    · simp
    · conv_lhs => rw [← mul_one (n + 1)]
      exact Nat.mul_le_mul_left _ (by omega)
  have hp := pow_le_pow_of_le_one (norm_nonneg r) hr.le hn
  calc
    ‖rectangleTerm r m n‖ ≤ ‖r‖ ^ n * C * C := by
      simp only [rectangleTerm, norm_mul, norm_pow]
      exact mul_le_mul (mul_le_mul hp (hbound n) (norm_nonneg _) (by positivity))
        (hbound _) (norm_nonneg _) (by positivity)
    _ = C ^ 2 * ‖r‖ ^ n := by ring

private theorem rectangleTerm_summable {r : ℂ} (hr : ‖r‖ < 1) (m : ℕ) :
    Summable (rectangleTerm r m) := by
  obtain ⟨C, hC, hbound⟩ := inv_qFactorial_bounded hr
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg r) hr).mul_left (C ^ 2))
    (fun n => norm_rectangleTerm_le hr hC hbound m n)

private theorem rectangleTerm_telescopes {r : ℂ} (hr : ‖r‖ < 1) (m n : ℕ) :
    rectangleTerm r m n - rectangleTerm r (m + 1) n =
      rectangleTerm r m n * (1 - r ^ n) -
        rectangleTerm r m (n + 1) * (1 - r ^ (n + 1)) := by
  have h1 : n * (n + (m + 1)) = n * (n + m) + n := by ring
  have h2 : (n + 1) * (n + 1 + m) = n * (n + m) + n + (n + m + 1) := by ring
  have h3 : n + (m + 1) = (n + m) + 1 := by omega
  have h4 : n + 1 + m = (n + m) + 1 := by omega
  unfold rectangleTerm
  rw [h1, h2, h3, h4, qFactorial_succ r (n + m), qFactorial_succ r n]
  simp only [pow_add r (n * (n + m) + n) (n + m + 1), pow_add r (n * (n + m)) n]
  field_simp [qFactorial_ne_zero hr, one_sub_pow_succ_ne_zero hr]
  ring

private theorem rectangleTerm_tsum_succ {r : ℂ} (hr : ‖r‖ < 1) (m : ℕ) :
    ∑' n, rectangleTerm r m n = ∑' n, rectangleTerm r (m + 1) n := by
  let h := fun n => rectangleTerm r m n * (1 - r ^ n)
  have hzero : h 0 = 0 := by simp [h]
  have ht : Tendsto h atTop (𝓝 0) := by
    simpa only [zero_mul, sub_zero] using
      (rectangleTerm_summable hr m).tendsto_atTop_zero.mul
        (tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr))
  have hs : HasSum (fun n => rectangleTerm r m n - rectangleTerm r (m+1) n)
      ((∑' n, rectangleTerm r m n) - (∑' n, rectangleTerm r (m+1) n)) :=
    (rectangleTerm_summable hr m).hasSum.sub (rectangleTerm_summable hr (m+1)).hasSum
  have hfinite : ∀ N, (∑ n ∈ range N, (rectangleTerm r m n - rectangleTerm r (m+1) n)) = -h N := by
    intro N
    simp_rw [rectangleTerm_telescopes hr]
    change (∑ n ∈ range N, (h n - h (n+1))) = -h N
    simp_rw [show ∀ n, h n - h (n + 1) = -(h (n + 1) - h n) from fun n => by ring]
    rw [sum_neg_distrib, sum_range_sub, hzero, sub_zero]
  have hlim := ht.neg
  simp only [neg_zero] at hlim
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique hs.tendsto_sum_nat (hlim.congr (fun N => (hfinite N).symm))

private theorem rectangleTerm_tsum {r : ℂ} (hr : ‖r‖ < 1) (m : ℕ) :
    ∑' n, rectangleTerm r m n = (qEuler r)⁻¹ := by
  let g : ℕ → ℂ := fun n => if n = 0 then (qEuler r)⁻¹ else 0
  have hpoint (n : ℕ) : Tendsto (fun m => rectangleTerm r m n) atTop (𝓝 (g n)) := by
    by_cases hn : n = 0
    · subst n
      simpa [rectangleTerm, g, qFactorial_zero] using tendsto_inv_qFactorial hr
    · have ha : Tendsto (fun m : ℕ => n + m) atTop atTop := by
        exact tendsto_atTop_mono (fun k => by change k ≤ n + k; omega) tendsto_id
      have hb : Tendsto (fun m : ℕ => n * (n + m)) atTop atTop := by
        apply tendsto_atTop_mono (fun k => ?_) ha
        conv_lhs => rw [← one_mul (n + k)]
        exact Nat.mul_le_mul_right _ (by omega)
      have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).comp hb
      have hq := (tendsto_inv_qFactorial hr).comp ha
      simpa [rectangleTerm, Function.comp_def, g, hn] using
        (hp.mul_const (qFactorial r n)⁻¹).mul hq
  obtain ⟨C, hC, hbound⟩ := inv_qFactorial_bounded hr
  have hs := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (norm_nonneg r) hr).mul_left (C ^ 2))
    hpoint (Eventually.of_forall (norm_rectangleTerm_le hr hC hbound))
  have hg : (∑' n, g n) = (qEuler r)⁻¹ := by
    rw [tsum_eq_single 0]
    · simp [g]
    · intro n hn
      simp [g, hn]
  rw [hg] at hs
  have hconst (n : ℕ) : (∑' k, rectangleTerm r n k) = ∑' k, rectangleTerm r 0 k := by
    induction n with
    | zero => rfl
    | succ n ih => exact (rectangleTerm_tsum_succ hr n).symm.trans ih
  exact (hconst m).trans (tendsto_nhds_unique tendsto_const_nhds
    (hs.congr fun n => hconst n))

private theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.add_one, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

private noncomputable def qProductTerm (r z : ℂ) (n : ℕ) : ℂ :=
  z ^ n * r ^ (n.choose 2) * (qFactorial r n)⁻¹

private noncomputable def qProductMajorant (r z : ℂ) (n : ℕ) : ℝ :=
  ‖z‖ ^ n * ‖r‖ ^ (n.choose 2)

private theorem qProductMajorant_summable {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) :
    Summable (qProductMajorant r z) := by
  have hr' := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg r) hr
  have hlim : Tendsto (fun n : ℕ => ‖z‖ * ‖r‖ ^ n) atTop (𝓝 0) := by
    simpa using hr'.const_mul ‖z‖
  have he := hlim.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)
  refine summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : ℝ) < 1) ?_
  filter_upwards [he] with n hn
  simp only [qProductMajorant, Real.norm_eq_abs, pow_succ ‖z‖, choose_two_succ, pow_add]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc
    ‖z‖ ^ n * ‖z‖ * (‖r‖ ^ (n.choose 2) * ‖r‖ ^ n) =
        (‖z‖ ^ n * ‖r‖ ^ (n.choose 2)) * (‖z‖ * ‖r‖ ^ n) := by ring
    _ ≤ (‖z‖ ^ n * ‖r‖ ^ (n.choose 2)) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hn.le (by positivity)
    _ = 1 / 2 * (‖z‖ ^ n * ‖r‖ ^ (n.choose 2)) := mul_comm _ _

private theorem qProductTerm_bound {r : ℂ} {C : ℝ}
    (hbound : ∀ n, ‖(qFactorial r n)⁻¹‖ ≤ C) (z : ℂ) (n : ℕ) :
    ‖qProductTerm r z n‖ ≤ qProductMajorant r z n * C := by
  simp only [qProductTerm, qProductMajorant, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hbound n) (by positivity)

private theorem qProductTerm_summable_norm {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) :
    Summable fun n => ‖qProductTerm r z n‖ := by
  obtain ⟨C, _, hbound⟩ := inv_qFactorial_bounded hr
  exact ((qProductMajorant_summable hr z).mul_right C).of_nonneg_of_le
    (fun _ => norm_nonneg _) (qProductTerm_bound hbound z)

private theorem qProductTerm_summable {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) :
    Summable (qProductTerm r z) :=
  (qProductTerm_summable_norm hr z).of_norm

private noncomputable def qProductSeries (r z : ℂ) : ℂ :=
  ∑' n, qProductTerm r z n

private theorem qProductTerm_zero (r z : ℂ) : qProductTerm r z 0 = 1 := by
  simp [qProductTerm, Nat.choose, qFactorial_zero]

private theorem qProductTerm_shift {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) (n : ℕ) :
    qProductTerm r z (n + 1) - qProductTerm r (z * r) (n + 1) =
      z * qProductTerm r (z * r) n := by
  unfold qProductTerm
  simp only [qFactorial_succ r n, choose_two_succ, mul_pow, pow_succ z n,
    pow_add r (n.choose 2) n]
  have hd : 1 - r ^ (n + 1) ≠ 0 := one_sub_pow_succ_ne_zero hr n
  field_simp [qFactorial_ne_zero hr, hd]

private theorem qProductSeries_shift {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) :
    qProductSeries r z = (1 + z) * qProductSeries r (z * r) := by
  have hz := qProductTerm_summable hr z
  have hzr := qProductTerm_summable hr (z * r)
  have hdiff := hz.sub hzr
  have h := hdiff.tsum_eq_zero_add
  change (∑' n, (qProductTerm r z n - qProductTerm r (z * r) n)) =
    (qProductTerm r z 0 - qProductTerm r (z * r) 0) +
      (∑' n, (qProductTerm r z (n + 1) - qProductTerm r (z * r) (n + 1))) at h
  rw [hz.tsum_sub hzr, qProductTerm_zero, qProductTerm_zero, sub_self, zero_add] at h
  simp_rw [qProductTerm_shift hr, tsum_mul_left] at h
  unfold qProductSeries
  rw [add_mul, one_mul, ← h]
  ring

private theorem qProductSeries_finite {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) (N : ℕ) :
    qProductSeries r z = (∏ j ∈ range N, (1 + z * r ^ j)) * qProductSeries r (z * r ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      conv_lhs => rw [ih, qProductSeries_shift hr]
      rw [prod_range_succ, pow_succ, mul_assoc]
      rw [← mul_assoc]

private theorem tendsto_qProductSeries {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) :
    Tendsto (fun N : ℕ => qProductSeries r (z * r ^ N)) atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ => z * r ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).const_mul z
  let g : ℕ → ℂ := fun n => if n = 0 then 1 else 0
  have hpoint (n : ℕ) : Tendsto (fun N : ℕ => qProductTerm r (z * r ^ N) n) atTop (𝓝 (g n)) := by
    rcases n with _ | n
    · simp [qProductTerm_zero, g]
    · simpa [qProductTerm, g] using
        (((hz.pow (n + 1)).mul_const (r ^ ((n + 1).choose 2))).mul_const
          (qFactorial r (n + 1))⁻¹)
  obtain ⟨C, hC, hbound⟩ := inv_qFactorial_bounded hr
  have hmajor (N n : ℕ) : qProductMajorant r (z * r ^ N) n ≤ qProductMajorant r z n := by
    have hp : ‖r‖ ^ N ≤ 1 := pow_le_one₀ (norm_nonneg _) hr.le
    have hn : ‖z * r ^ N‖ ≤ ‖z‖ := by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) hp
    simp only [qProductMajorant]
    gcongr
  have hdecay := tendsto_tsum_of_dominated_convergence
    ((qProductMajorant_summable hr z).mul_right C) hpoint
    (Eventually.of_forall fun N n =>
      (qProductTerm_bound hbound _ n).trans
        (mul_le_mul_of_nonneg_right (hmajor N n) hC))
  have hg : (∑' n, g n) = 1 := by
    rw [tsum_eq_single 0]
    · simp [g]
    · intro n hn
      simp [g, hn]
  rwa [hg] at hdecay

/-- The factors in Euler's unilateral product are multipliable. -/
theorem qProduct_multipliable {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) :
    Multipliable fun j : ℕ => 1 + z * r ^ j := by
  apply multipliable_one_add_of_summable
  simp only [norm_mul, norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg r) hr).mul_left ‖z‖

/-- Euler's unilateral series for the convergent plus product. -/
theorem qProductSeries_eq_tprod {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) :
    (∑' n : ℕ, z ^ n * r ^ (n.choose 2) / qFactorial r n) =
      (∏' j : ℕ, (1 + z * r ^ j)) := by
  have hlim := (qProduct_multipliable hr z).hasProd.tendsto_prod_nat.mul (tendsto_qProductSeries hr z)
  simp only [mul_one] at hlim
  have h := tendsto_nhds_unique tendsto_const_nhds
    (hlim.congr fun n => (qProductSeries_finite hr z n).symm)
  simpa only [qProductSeries, qProductTerm, div_eq_mul_inv] using h

/-- Absolute convergence of the unilateral series in Euler's identity. -/
theorem qProductSeries_summable_norm {r : ℂ} (hr : ‖r‖ < 1) (z : ℂ) :
    Summable fun n : ℕ => ‖z ^ n * r ^ (n.choose 2) / qFactorial r n‖ := by
  simpa only [qProductTerm, div_eq_mul_inv] using qProductTerm_summable_norm hr z

private theorem norm_sq_lt_one {q : ℂ} (hq : ‖q‖ < 1) : ‖q ^ 2‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq (by decide)

private theorem two_mul_choose_two_add_self (n : ℕ) : n + 2 * n.choose 2 = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [choose_two_succ]
      calc
        n + 1 + 2 * (n.choose 2 + n) = (n + 2 * n.choose 2) + 2 * n + 1 := by ring
        _ = (n + 1) ^ 2 := by rw [ih]; ring

private theorem qProductTerm_square (q z : ℂ) (n : ℕ) :
    qProductTerm (q ^ 2) (z * q) n = z ^ n * q ^ (n ^ 2) / qFactorial (q ^ 2) n := by
  rw [qProductTerm, mul_pow, ← pow_mul, mul_assoc (z ^ n), ← pow_add,
    two_mul_choose_two_add_self, div_eq_mul_inv, mul_assoc]

/-- Euler's identity in the square-exponent normalization of the manuscript. -/
theorem qProductSquare_eq_tprod {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) :
    (∑' n : ℕ, z ^ n * q ^ (n ^ 2) / qFactorial (q ^ 2) n) =
      (∏' j : ℕ, (1 + z * q * (q ^ 2) ^ j)) := by
  calc
    _ = ∑' n : ℕ, qProductTerm (q ^ 2) (z * q) n := by simp_rw [qProductTerm_square]
    _ = _ := by
      simpa only [div_eq_mul_inv, qProductTerm] using
        qProductSeries_eq_tprod (norm_sq_lt_one hq) (z * q)

/-- Absolute convergence in the square-exponent normalization. -/
theorem qProductSquare_summable_norm {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) :
    Summable fun n : ℕ => ‖z ^ n * q ^ (n ^ 2) / qFactorial (q ^ 2) n‖ := by
  simpa only [qProductTerm_square] using
    qProductTerm_summable_norm (norm_sq_lt_one hq) (z * q)

/-- A pair of natural numbers is determined by its signed difference and its smaller entry. -/
private def diagonalEquiv : ℤ × ℕ ≃ ℕ × ℕ where
  toFun p := (p.1.toNat + p.2, (-p.1).toNat + p.2)
  invFun p := ((p.1 : ℤ) - p.2, min p.1 p.2)
  left_inv := by
    rintro ⟨m, n⟩
    ext <;> dsimp
    · omega
    · omega
  right_inv := by
    rintro ⟨a, b⟩
    ext <;> dsimp <;> omega

private theorem diagonalTerm (q : ℂ) {z : ℂ} (hz : z ≠ 0) (m : ℤ) (n : ℕ) :
    qProductTerm (q ^ 2) (z * q) (diagonalEquiv (m, n)).1 *
        qProductTerm (q ^ 2) (z⁻¹ * q) (diagonalEquiv (m, n)).2 =
      (z ^ m * q ^ (m.natAbs ^ 2)) * rectangleTerm (q ^ 2) m.natAbs n := by
  let a := (diagonalEquiv (m, n)).1
  let b := (diagonalEquiv (m, n)).2
  have hab : (a : ℤ) - b = m := congrArg Prod.fst (diagonalEquiv.left_inv (m, n))
  have hzpow : z ^ a * (z⁻¹) ^ b = z ^ m := by
    rw [← hab, zpow_sub₀ hz, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]
  have hpair : (a = m.natAbs + n ∧ b = n) ∨ (a = n ∧ b = m.natAbs + n) := by
    dsimp [a, b, diagonalEquiv]
    by_cases hm : 0 ≤ m
    · left
      omega
    · right
      omega
  have hqp : q ^ (a ^ 2) * q ^ (b ^ 2) = q ^ (m.natAbs ^ 2) * (q ^ 2) ^ (n * (n + m.natAbs)) := by
    rw [← pow_add, ← pow_mul, ← pow_add]
    congr 1
    rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> ring
  have hd : (qFactorial (q ^ 2) a)⁻¹ * (qFactorial (q ^ 2) b)⁻¹ =
      (qFactorial (q ^ 2) n)⁻¹ * (qFactorial (q ^ 2) (n + m.natAbs))⁻¹ := by
    rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [ha, hb, add_comm, mul_comm]
  change qProductTerm (q ^ 2) (z * q) a * qProductTerm (q ^ 2) (z⁻¹ * q) b = _
  rw [qProductTerm_square, qProductTerm_square, div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = (z ^ a * (z⁻¹) ^ b) * (q ^ (a ^ 2) * q ^ (b ^ 2)) *
        ((qFactorial (q ^ 2) a)⁻¹ * (qFactorial (q ^ 2) b)⁻¹) := by ring
    _ = _ := by rw [hzpow, hqp, hd, rectangleTerm]; ring

/-- Jacobi's triple product at `q`, before converting to exponential coordinates. -/
theorem jacobi_triple_product {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    (∑' m : ℤ, z ^ m * q ^ (m.natAbs ^ 2)) =
      (∏' j : ℕ, (1 - (q ^ 2) ^ (j + 1))) *
        (∏' j : ℕ, (1 + z * q * (q ^ 2) ^ j)) *
        (∏' j : ℕ, (1 + z⁻¹ * q * (q ^ 2) ^ j)) := by
  have hr := norm_sq_lt_one hq
  let f := qProductTerm (q ^ 2) (z * q)
  let g := qProductTerm (q ^ 2) (z⁻¹ * q)
  let v := fun p : ℕ × ℕ => f p.1 * g p.2
  have hf : Summable fun n => ‖f n‖ := qProductTerm_summable_norm hr (z * q)
  have hg : Summable fun n => ‖g n‖ := qProductTerm_summable_norm hr (z⁻¹ * q)
  have hv : Summable v := summable_mul_of_summable_norm hf hg
  have hv' : Summable (v ∘ diagonalEquiv) := (diagonalEquiv.summable_iff).mpr hv
  have hinner (m : ℤ) : (∑' n : ℕ, v (diagonalEquiv (m, n))) =
      (z ^ m * q ^ (m.natAbs ^ 2)) * (qEuler (q ^ 2))⁻¹ := by
    simp_rw [show ∀ n, v (diagonalEquiv (m, n)) = _ from diagonalTerm q hz m]
    rw [tsum_mul_left, rectangleTerm_tsum hr]
  have hprod (w : ℂ) : (∑' n, qProductTerm (q ^ 2) (w * q) n) =
      (∏' j : ℕ, (1 + w * q * (q ^ 2) ^ j)) := by
    simp_rw [qProductTerm_square]
    exact qProductSquare_eq_tprod hq w
  have hEq := tsum_mul_tsum_of_summable_norm hf hg
  change ((∑' n, f n) * ∑' n, g n) = ∑' p, v p at hEq
  rw [← diagonalEquiv.tsum_eq v] at hEq
  change _ = (∑' p : ℤ × ℕ, (v ∘ diagonalEquiv) p) at hEq
  rw [hv'.tsum_prod] at hEq
  simp_rw [Function.comp_apply, hinner, tsum_mul_right] at hEq
  have hfinal : (qEuler (q ^ 2)) * ((∑' n, f n) * ∑' n, g n) = _ := congrArg (fun x => qEuler (q ^ 2) * x) hEq
  rw [show (∑' n, f n) = _ from hprod z, show (∑' n, g n) = _ from hprod z⁻¹] at hfinal
  have hcancel (x : ℂ) : qEuler (q ^ 2) * (x * (qEuler (q ^ 2))⁻¹) = x := by
    rw [mul_left_comm, mul_inv_cancel₀ (qEuler_ne_zero hr), mul_one]
  rw [hcancel] at hfinal
  simpa only [qEuler, mul_assoc] using hfinal.symm

end DurfeeCCS.Step06
