module

public import DurfeeCCS.Step06.RademacherGenerating
import Mathlib.Tactic

/-! The convergent ordinary partition series on the open unit disc. -/

@[expose] public section
namespace DurfeeCCS.Step14

open Filter Finset PowerSeries Step06
open scoped Topology

private theorem coeff_ordinary_le_twoColour (n : ℕ) :
    coeff n ordinaryPartitionSeries ≤ twoColourPartitionCount n := by
  rw [ordinaryPartitionSeries, coeff_mk, twoColourPartitionCount_eq_convolution]
  have h := sum_le_sum_of_subset_of_nonneg (s := {(0, n)}) (t := antidiagonal n)
    (f := fun ab : ℕ × ℕ => (Fintype.card (Nat.Partition ab.1) : ℤ) *
      (Fintype.card (Nat.Partition ab.2) : ℤ)) (by simp) (fun a _ _ => by positivity)
  simpa only [sum_singleton, Fintype.card_unique, Nat.cast_one, one_mul] using h

private theorem coeff_restricted_le_ordinary (d n : ℕ) :
    coeff n (restrictedPartitionSeries d) ≤ coeff n ordinaryPartitionSeries := by
  rw [coeff_restrictedPartitionSeries, ordinaryPartitionSeries, coeff_mk]
  exact_mod_cast Finset.card_le_univ (Nat.Partition.restricted n (· ≤ d))

private theorem coeff_restricted_eq_ordinary {d n : ℕ} (hd : n ≤ d) :
    coeff n (restrictedPartitionSeries d) = coeff n ordinaryPartitionSeries := by
  rw [coeff_restrictedPartitionSeries, ordinaryPartitionSeries, coeff_mk]
  have h : Nat.Partition.restricted n (· ≤ d) = Finset.univ := by
    ext P
    simp only [Nat.Partition.restricted, mem_filter, mem_univ, true_and, iff_true]
    exact fun a ha => (Nat.Partition.le_of_mem_parts ha).trans hd
  rw [h, card_univ]

private theorem norm_int_mul_pow_le (q : ℂ) (n : ℕ) {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖(a : ℂ) * q ^ n‖ ≤ ‖(b : ℂ) * q ^ n‖ := by
  rw [norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_intCast,
    abs_of_nonneg (by exact_mod_cast ha), abs_of_nonneg (by exact_mod_cast ha.trans hab)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (norm_nonneg _)

theorem summable_norm_ordinaryPartitionSeries {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖((coeff n ordinaryPartitionSeries : ℤ) : ℂ) * q ^ n‖) := by
  refine (summable_norm_twoColourGenerating hq).of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  exact norm_int_mul_pow_le q n (by simp [ordinaryPartitionSeries]) (coeff_ordinary_le_twoColour n)

theorem partitionEulerFactors_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' j : ℕ, (1 - q ^ (j + 1))) ≠ 0 := by
  have hsum : Summable (fun j : ℕ => ‖-(q ^ (j + 1))‖) := by
    simp_rw [norm_neg, norm_pow]
    exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)
  have hne (j : ℕ) : 1 + -(q ^ (j + 1)) ≠ 0 := by
    intro hj
    have hqj : ‖q ^ (j + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero j)
    have hj' : q ^ (j + 1) = 1 := (sub_eq_zero.mp (by simpa only [← sub_eq_add_neg] using hj)).symm
    simp [hj'] at hqj
  simpa only [← sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable hne hsum

/-- The formal partition coefficients sum to the reciprocal of the full Euler product. -/
theorem hasSum_ordinaryPartitionSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => ((coeff n ordinaryPartitionSeries : ℤ) : ℂ) * q ^ n)
      (∏' j : ℕ, (1 - q ^ (j + 1)))⁻¹ := by
  let f (d n : ℕ) := ((coeff n (restrictedPartitionSeries d) : ℤ) : ℂ) * q ^ n
  let g (n : ℕ) := ((coeff n ordinaryPartitionSeries : ℤ) : ℂ) * q ^ n
  have hs : Summable (fun n => ‖g n‖) := summable_norm_ordinaryPartitionSeries hq
  have hlim (n : ℕ) : Tendsto (f · n) atTop (𝓝 (g n)) := by
    apply tendsto_atTop_of_eventually_const (i₀ := n)
    intro d hd
    simp only [f, g, coeff_restricted_eq_ordinary hd]
  have hdom (d n : ℕ) : ‖f d n‖ ≤ ‖g n‖ :=
    norm_int_mul_pow_le q n (by simp) (coeff_restricted_le_ordinary d n)
  have h := tendsto_tsum_of_dominated_convergence hs hlim (Eventually.of_forall hdom)
  have he (d : ℕ) : (∑' n, f d n) = (qPochhammer q q d)⁻¹ := by
    have hd := (hasSum_coeff_restrictedMixedSeries hq d 0).1.tsum_eq
    simpa only [restrictedPartitionSeries_zero, mul_one, qPochhammer_zero, inv_one] using hd
  simp_rw [he] at h
  have hp := (ModularForm.multipliable_one_sub_pow hq).hasProd.tendsto_prod_nat.inv₀
    (partitionEulerFactors_ne_zero hq)
  simp_rw [← qPochhammer_self_eq_prod] at hp
  exact tendsto_nhds_unique h hp ▸ hs.of_norm.hasSum

end DurfeeCCS.Step14
