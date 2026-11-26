module

public import DurfeeCCS.GeneratingFunction
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The generating coefficients and the argument and prefactor normalizations in (14). -/

@[expose] public section
open PowerSeries
namespace DurfeeCCS.Step06

/-- The ordinary partition generating series. -/
noncomputable def ordinaryPartitionSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => (Fintype.card (Nat.Partition n) : ℤ)

/-- The coefficients of the square of the partition generating series. -/
noncomputable def twoColourPartitionCount (n : ℕ) : ℤ :=
  coeff n (ordinaryPartitionSeries ^ 2)

theorem twoColourPartitionCount_eq_convolution (n : ℕ) :
    twoColourPartitionCount n =
      ∑ ab ∈ Finset.antidiagonal n,
        (Fintype.card (Nat.Partition ab.1) : ℤ) * (Fintype.card (Nat.Partition ab.2) : ℤ) := by
  rw [twoColourPartitionCount, pow_two, coeff_mul]
  simp [ordinaryPartitionSeries]

private theorem coeff_ordinaryPartitionSeries_eq_restricted (d n : ℕ) (hd : n ≤ d) :
    coeff n ordinaryPartitionSeries = coeff n (DurfeeCCS.restrictedPartitionSeries d) := by
  simp only [ordinaryPartitionSeries, coeff_mk, DurfeeCCS.coeff_restrictedPartitionSeries]
  have hset : Nat.Partition.restricted n (· ≤ d) = Finset.univ := by
    ext P
    simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact fun a ha => (Nat.Partition.le_of_mem_parts ha).trans hd
  rw [hset, Finset.card_univ]

/-- Terms of degree at most `d` are unchanged by the finite product through size `d`. -/
theorem twoColourPartitionCount_eq_coeff_restricted (n d : ℕ) (hd : n ≤ d) :
    twoColourPartitionCount n = coeff n (DurfeeCCS.restrictedPairSeries d) := by
  rw [twoColourPartitionCount, pow_two, DurfeeCCS.restrictedPairSeries_eq_mul, coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hsum := Finset.mem_antidiagonal.mp hab
  rw [coeff_ordinaryPartitionSeries_eq_restricted d ab.1 (by omega),
    coeff_ordinaryPartitionSeries_eq_restricted d ab.2 (by omega)]

@[simp] theorem twoColourPartitionCount_zero : twoColourPartitionCount 0 = 1 := by
  rw [twoColourPartitionCount_eq_coeff_restricted 0 0 (by omega)]
  exact DurfeeCCS.coeff_restrictedPairSeries_zero 0

theorem twoColourPartitionCount_one : twoColourPartitionCount 1 = 2 := by
  rw [twoColourPartitionCount_eq_coeff_restricted 1 1 (by omega),
    DurfeeCCS.coeff_restrictedPairSeries_eq_count,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => DurfeeCCS.restrictedPartitionCount 1 a * DurfeeCCS.restrictedPartitionCount 1 b)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [DurfeeCCS.restrictedPartitionCount]

theorem twoColourPartitionCount_two : twoColourPartitionCount 2 = 5 := by
  rw [twoColourPartitionCount_eq_coeff_restricted 2 2 (by omega),
    DurfeeCCS.coeff_restrictedPairSeries_eq_count,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => DurfeeCCS.restrictedPartitionCount 2 a * DurfeeCCS.restrictedPartitionCount 2 b)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [DurfeeCCS.restrictedPartitionCount]

/-- The weight shift in (1.6) of 1907.03026v3 uses `α/24 = 1/12` at `α = 2`. -/
theorem ijtTwoColour_prefactor {n : ℕ} (hn : 0 < n) :
    (Real.sqrt (1 / 12)) ^ 2 / (Real.sqrt ((n : ℝ) - 1 / 12)) ^ 2 * (2 * Real.pi) =
      2 * Real.pi / (12 * (n : ℝ) - 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hshift : 0 < (n : ℝ) - 1 / 12 := by linarith
  have hden : 0 < 12 * (n : ℝ) - 1 := by linarith
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 12), Real.sq_sqrt hshift.le]
  field_simp [hshift.ne', hden.ne']

/-- The normalized argument of `I₂`, starting from (1.8) of 1907.03026v3. -/
theorem ijtTwoColour_argument {n : ℕ} (hn : 0 < n) (ℓ : ℕ) :
    (4 * Real.pi / ℓ) * Real.sqrt ((n : ℝ) - 1 / 12) * Real.sqrt (1 / 12) =
      Real.pi * Real.sqrt (12 * (n : ℝ) - 1) / (3 * ℓ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hshift : 0 < (n : ℝ) - 1 / 12 := by linarith
  have hden : 0 < 12 * (n : ℝ) - 1 := by linarith
  have harg : Real.sqrt ((n : ℝ) - 1 / 12) * Real.sqrt (1 / 12) =
      Real.sqrt (12 * (n : ℝ) - 1) / 12 := by
    rw [← Real.sqrt_mul hshift.le]
    have heq : ((n : ℝ) - 1 / 12) * (1 / 12) = (12 * (n : ℝ) - 1) / 12 ^ 2 := by ring
    rw [heq, Real.sqrt_div hden.le, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12)]
  rw [mul_assoc, harg]
  ring

end DurfeeCCS.Step06
