module

public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.NormNum

/-! # The bounded partition generating functions in equation (1) -/

@[expose] public section

open PowerSeries
open scoped BigOperators PowerSeries.WithPiTopology

namespace DurfeeCCS

/-- The generating series for partitions with no part larger than `d`. -/
noncomputable def restrictedPartitionSeries (d : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n (· ≤ d)).card : ℤ)

@[simp] theorem coeff_restrictedPartitionSeries (d n : ℕ) :
    coeff n (restrictedPartitionSeries d) = ((Nat.Partition.restricted n (· ≤ d)).card : ℤ) :=
  PowerSeries.coeff_mk _ _

/-- The formal inverse of `1 - X^j`, for positive `j`. -/
noncomputable def durfeeGeometricFactor (j : ℕ) : ℤ⟦X⟧ :=
  letI : TopologicalSpace ℤ := ⊥
  ∑' k : ℕ, (X : ℤ⟦X⟧) ^ (j * k)

section

-- Formal convergence is coefficientwise over the discrete integers.
local instance : TopologicalSpace ℤ := ⊥
local instance : DiscreteTopology ℤ := ⟨rfl⟩

theorem durfeeGeometricFactor_mul (j : ℕ) (hj : j ≠ 0) :
    durfeeGeometricFactor j * (1 - (X : ℤ⟦X⟧) ^ j) = 1 := by
  change (∑' k : ℕ, (X : ℤ⟦X⟧) ^ (j * k)) * (1 - X ^ j) = 1
  simp_rw [pow_mul]
  exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp [hj])

theorem restrictedPartitionSeries_eq_prod (d : ℕ) :
    restrictedPartitionSeries d = ∏ j ∈ Finset.range d, durfeeGeometricFactor (j + 1) := by
  rw [restrictedPartitionSeries, Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℤ (· ≤ d)]
  rw [tprod_eq_prod (s := Finset.range d)]
  · refine Finset.prod_congr rfl fun j hj ↦ ?_
    exact ite_eq_left (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
  · intro j hj
    exact ite_eq_right (fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_of_succ_le h)))

end

/-- The product of the formal factors `(1 - X^j)⁻²` for `1 ≤ j ≤ d`. -/
noncomputable def restrictedPairSeries (d : ℕ) : ℤ⟦X⟧ :=
  ∏ j ∈ Finset.range d, durfeeGeometricFactor (j + 1) ^ 2

theorem restrictedPairSeries_eq_mul (d : ℕ) :
    restrictedPairSeries d = restrictedPartitionSeries d * restrictedPartitionSeries d := by
  rw [restrictedPairSeries, restrictedPartitionSeries_eq_prod, ← Finset.prod_mul_distrib]
  simp_rw [pow_two]

/-- Ordered pairs are counted by convolution of their two partition sizes. -/
theorem coeff_restrictedPairSeries (d n : ℕ) :
    coeff n (restrictedPairSeries d) =
      ∑ ab ∈ Finset.antidiagonal n,
        ((Nat.Partition.restricted ab.1 (· ≤ d)).card : ℤ) *
          ((Nat.Partition.restricted ab.2 (· ≤ d)).card : ℤ) := by
  rw [restrictedPairSeries_eq_mul, PowerSeries.coeff_mul]
  simp only [coeff_restrictedPartitionSeries]

@[simp] theorem restrictedPartitionSeries_zero : restrictedPartitionSeries 0 = 1 := by
  simp [restrictedPartitionSeries_eq_prod]

theorem restrictedPartitionSeries_step (d : ℕ) :
    restrictedPartitionSeries (d + 1) * (1 - (X : ℤ⟦X⟧) ^ (d + 1)) =
      restrictedPartitionSeries d := by
  rw [restrictedPartitionSeries_eq_prod (d + 1), restrictedPartitionSeries_eq_prod d,
    Finset.prod_range_succ, mul_assoc, durfeeGeometricFactor_mul _ (Nat.succ_ne_zero d), mul_one]

theorem coeff_restrictedPartitionSeries_succ (d n : ℕ) :
    coeff n (restrictedPartitionSeries (d + 1)) = coeff n (restrictedPartitionSeries d) +
      if d + 1 ≤ n then coeff (n - (d + 1)) (restrictedPartitionSeries (d + 1)) else 0 := by
  have h := congrArg (coeff n) (restrictedPartitionSeries_step d)
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow'] at h
  exact sub_eq_iff_eq_add.mp h

/-- The recurrence for bounded partitions, computed with exact integers. -/
def restrictedPartitionCount (d n : ℕ) : ℤ :=
  match d with
  | 0 => if n = 0 then 1 else 0
  | d + 1 => restrictedPartitionCount d n +
      if h : d + 1 ≤ n then restrictedPartitionCount (d + 1) (n - (d + 1)) else 0
termination_by (d, n)
decreasing_by all_goals simp_wf; omega

theorem restrictedPartitionCount_eq_coeff (d n : ℕ) :
    restrictedPartitionCount d n = coeff n (restrictedPartitionSeries d) := by
  induction d generalizing n with
  | zero => simp [restrictedPartitionCount, PowerSeries.coeff_one]
  | succ d ihd =>
    induction n using Nat.strongRecOn with
    | ind n ihn =>
      rw [coeff_restrictedPartitionSeries_succ, restrictedPartitionCount, ihd]
      split_ifs with h
      · rw [ihn _ (by omega)]
      · rfl

theorem coeff_restrictedPairSeries_eq_count (d n : ℕ) :
    coeff n (restrictedPairSeries d) =
      ∑ ab ∈ Finset.antidiagonal n, restrictedPartitionCount d ab.1 * restrictedPartitionCount d ab.2 := by
  simp only [restrictedPairSeries_eq_mul, PowerSeries.coeff_mul, restrictedPartitionCount_eq_coeff]

@[simp] theorem coeff_restrictedPairSeries_zero (d : ℕ) : coeff 0 (restrictedPairSeries d) = 1 := by
  have hzero : restrictedPartitionCount d 0 = 1 := by
    induction d with
    | zero => simp [restrictedPartitionCount]
    | succ d ih => simp [restrictedPartitionCount, ih]
  simp [coeff_restrictedPairSeries_eq_count, hzero]

theorem coeff_pairSeries_two_zero : coeff 0 (restrictedPairSeries 2) = 1 := by simp

theorem coeff_pairSeries_two_five : coeff 5 (restrictedPairSeries 2) = 20 := by
  rw [coeff_restrictedPairSeries_eq_count, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b ↦ restrictedPartitionCount 2 a * restrictedPartitionCount 2 b) 5]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [restrictedPartitionCount]

theorem coeff_pairSeries_three_zero : coeff 0 (restrictedPairSeries 3) = 1 := by simp

end DurfeeCCS
