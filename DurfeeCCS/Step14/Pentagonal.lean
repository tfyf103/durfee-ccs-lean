module

public import DurfeeCCS.Step14.PentagonalAnalytic
public import DurfeeCCS.Step14.PentagonalPartition
import Mathlib.Algebra.Field.NegOnePow
import Mathlib.Tactic

/-! The Euler pentagonal recurrence for the manuscript's ordinary partition numbers. -/

@[expose] public section
namespace DurfeeCCS.Step14

open Complex Finset PowerSeries Step06

/-- The signed coefficient of the Euler product at a generalized pentagonal number. -/
noncomputable def pentagonalCoeff (n : ℕ) : ℤ := by
  classical
  exact if h : n ∈ Set.range pentagonal then (h.choose.negOnePow : ℤ) else 0

theorem pentagonalCoeff_at (k : ℤ) : pentagonalCoeff (pentagonal k) = (k.negOnePow : ℤ) := by
  classical
  unfold pentagonalCoeff
  split_ifs with h
  · rw [pentagonal_injective h.choose_spec]
  · exact False.elim (h ⟨k, rfl⟩)

theorem pentagonalCoeff_of_not_mem {n : ℕ} (h : n ∉ Set.range pentagonal) :
    pentagonalCoeff n = 0 := by
  simp [pentagonalCoeff, h]

/-- Euler's denominator series with integer coefficients. -/
noncomputable def pentagonalKernel : ℤ⟦X⟧ := PowerSeries.mk pentagonalCoeff

@[simp] theorem coeff_pentagonalKernel (n : ℕ) : coeff n pentagonalKernel = pentagonalCoeff n :=
  coeff_mk _ _

private theorem norm_pentagonalCoeff_le_one (n : ℕ) : ‖(pentagonalCoeff n : ℂ)‖ ≤ 1 := by
  by_cases h : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := h
    rw [pentagonalCoeff_at, Int.cast_negOnePow]
    simp
  · simp [pentagonalCoeff_of_not_mem h]

private theorem summable_norm_pentagonalKernel {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖((coeff n pentagonalKernel : ℤ) : ℂ) * q ^ n‖) := by
  refine (summable_geometric_of_lt_one (norm_nonneg _) hq).of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  rw [coeff_pentagonalKernel, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (norm_pentagonalCoeff_le_one n)

private theorem exp_neg_norm_lt_one {ζ : ℂ} (hζ : 0 < ζ.re) : ‖exp (-ζ)‖ < 1 := by
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_lt_one_iff]
  linarith

private theorem exp_eulerFactor_eq_pow (ζ : ℂ) (j : ℕ) :
    exp (-((j : ℂ) + 1) * ζ) = exp (-ζ) ^ (j + 1) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem hasSum_pentagonalKernel {ζ : ℂ} (hζ : 0 < ζ.re) :
    HasSum (fun n => ((coeff n pentagonalKernel : ℤ) : ℂ) * exp (-ζ) ^ n) (eulerProduct ζ) := by
  let f (n : ℕ) := ((coeff n pentagonalKernel : ℤ) : ℂ) * exp (-ζ) ^ n
  have hterm (k : ℤ) : f (pentagonal k) = (-1 : ℂ) ^ k * exp (-(pentagonal k : ℂ) * ζ) := by
    dsimp only [f]
    rw [coeff_pentagonalKernel, pentagonalCoeff_at, Int.cast_negOnePow, ← Complex.exp_nat_mul]
    congr 2
    ring
  have hzero (n : ℕ) (hn : n ∉ Set.range pentagonal) : f n = 0 := by
    simp [f, pentagonalCoeff_of_not_mem hn]
  refine (pentagonal_injective.hasSum_iff hzero).mp ?_
  rw [eulerProduct_eq_pentagonal_tsum hζ]
  have hn := (summable_norm_pentagonalKernel (exp_neg_norm_lt_one hζ)).of_norm.comp_injective
    pentagonal_injective
  simpa only [Function.comp_apply, ← hterm] using hn.hasSum

private theorem hasSum_pentagonalKernel_mul {ζ : ℂ} (hζ : 0 < ζ.re) :
    HasSum (fun n => ((coeff n (pentagonalKernel * ordinaryPartitionSeries) : ℤ) : ℂ) *
      exp (-ζ) ^ n) 1 ∧
    Summable (fun n => ‖((coeff n (pentagonalKernel * ordinaryPartitionSeries) : ℤ) : ℂ) *
      exp (-ζ) ^ n‖) := by
  have hq := exp_neg_norm_lt_one hζ
  have h := hasSum_coeff_mul_of_summable_norm (hasSum_pentagonalKernel hζ)
    (summable_norm_pentagonalKernel hq) (hasSum_ordinaryPartitionSeries hq)
    (summable_norm_ordinaryPartitionSeries hq)
  have hval : eulerProduct ζ = ∏' j : ℕ, (1 - exp (-ζ) ^ (j + 1)) := by
    unfold eulerProduct
    simp_rw [exp_eulerFactor_eq_pow]
  rwa [hval, mul_inv_cancel₀ (partitionEulerFactors_ne_zero hq)] at h

/-- The Euler series is the inverse, coefficient by coefficient, of the ordinary
partition generating function already used for the Durfee polynomial. -/
theorem pentagonalKernel_mul_ordinaryPartitionSeries :
    pentagonalKernel * ordinaryPartitionSeries = 1 := by
  apply PowerSeries.ext
  intro n
  let a (m : ℕ) := ((coeff m (pentagonalKernel * ordinaryPartitionSeries) : ℤ) : ℂ)
  let b (m : ℕ) : ℂ := if m = 0 then 1 else 0
  have ha := (hasSum_pentagonalKernel_mul (ζ := 1) (by simp)).2
  have hb (q : ℂ) : HasSum (fun m => b m * q ^ m) 1 := by
    have h0 : b 0 * q ^ (0 : ℕ) = 1 := by simp [b]
    rw [← h0]
    apply hasSum_single 0
    intro k hk
    simp [b, hk]
  have hb' : Summable (fun m => ‖b m * exp (-((1 : ℝ) : ℂ)) ^ m‖) := by
    refine (hasSum_single 0 (f := fun m => ‖b m * exp (-((1 : ℝ) : ℂ)) ^ m‖) ?_).summable
    intro m hm
    simp [b, hm]
  have hand (v : ℝ) :
      (∑' m, a m * exp (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) ^ m) =
        ∑' m, b m * exp (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) ^ m := by
    have hpos : 0 < (((1 : ℝ) : ℂ) + (v : ℂ) * I).re := by simp
    exact (hasSum_pentagonalKernel_mul hpos).1.tsum_eq.trans (hb _).tsum_eq.symm
  have haa := angular_coefficient_of_summable a n 1 (by simpa only [Complex.ofReal_one] using ha)
  have hbb := angular_coefficient_of_summable b n 1 hb'
  simp_rw [hand] at haa
  have hab := haa.trans hbb.symm
  have hc : b n = ((coeff n (1 : ℤ⟦X⟧) : ℤ) : ℂ) := by
    by_cases hn : n = 0 <;> simp [b, PowerSeries.coeff_one, hn]
  rw [hc] at hab
  change ((coeff n (pentagonalKernel * ordinaryPartitionSeries) : ℤ) : ℂ) = _ at hab
  exact_mod_cast hab

private theorem natAbs_le_pentagonal (k : ℤ) : k.natAbs ≤ pentagonal k := by
  have h := two_mul_natCast_pentagonal k
  by_cases hpos : 0 ≤ k
  · by_cases hz : k = 0
    · simp [hz]
    have hp : 0 ≤ k * (k - 1) := mul_nonneg hpos (by omega)
    have hk : (k.natAbs : ℤ) = k := by simp [abs_of_nonneg hpos]
    have hle : (k.natAbs : ℤ) ≤ pentagonal k := by
      rw [hk]
      nlinarith only [h, hp]
    exact_mod_cast hle
  · have hn : 0 ≤ (-k) * (-k - 1) := mul_nonneg (by omega) (by omega)
    have hk : (k.natAbs : ℤ) = -k := by simp [abs_of_neg (by omega : k < 0)]
    have hle : (k.natAbs : ℤ) ≤ pentagonal k := by
      rw [hk]
      nlinarith only [h, hn]
    exact_mod_cast hle

/-- The starting value in the recurrence. -/
theorem partition_card_zero : Fintype.card (Nat.Partition 0) = 1 :=
  Fintype.card_unique

/-- The truncated Euler recurrence, indexed by `j + 1` for the positive and negative
generalized pentagonal offsets. Each term with an offset greater than `n` is zero. -/
theorem partition_card_pentagonal_recurrence {n : ℕ} (hn : 0 < n) :
    (Fintype.card (Nat.Partition n) : ℤ) =
      ∑ j ∈ range n, (-1 : ℤ) ^ j *
        ((if pentagonal ((j : ℤ) + 1) ≤ n then
            (Fintype.card (Nat.Partition (n - pentagonal ((j : ℤ) + 1))) : ℤ) else 0) +
          (if pentagonal (-((j : ℤ) + 1)) ≤ n then
            (Fintype.card (Nat.Partition (n - pentagonal (-((j : ℤ) + 1)))) : ℤ) else 0)) := by
  classical
  let P (m : ℕ) : ℤ := Fintype.card (Nat.Partition m)
  let T (m : ℕ) := pentagonalCoeff m * P (n - m)
  let a (j : ℕ) := pentagonal ((j : ℤ) + 1)
  let b (j : ℕ) := pentagonal (-((j : ℤ) + 1))
  let A := ((range n).filter (fun j => a j ≤ n)).image a
  let B := ((range n).filter (fun j => b j ≤ n)).image b
  let S := (range (n + 1)).filter (fun m => m ∈ Set.range pentagonal)
  have h0 : pentagonal 0 = 0 := by norm_num [pentagonal_def]
  have ha : Function.Injective a := by
    intro x y hxy
    have h := pentagonal_injective hxy
    change (x : ℤ) + 1 = (y : ℤ) + 1 at h
    omega
  have hb : Function.Injective b := by
    intro x y hxy
    have h := pentagonal_injective hxy
    change -((x : ℤ) + 1) = -((y : ℤ) + 1) at h
    omega
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro m hmA hmB
    obtain ⟨j, _, hj⟩ := mem_image.mp hmA
    obtain ⟨k, _, hk⟩ := mem_image.mp hmB
    have h := pentagonal_injective (hj.trans hk.symm)
    change (j : ℤ) + 1 = -((k : ℤ) + 1) at h
    omega
  have hzAB : Disjoint ({0} : Finset ℕ) (A ∪ B) := by
    apply Finset.disjoint_left.mpr
    intro m hm hABm
    obtain rfl := mem_singleton.mp hm
    rcases mem_union.mp hABm with hA | hB
    · obtain ⟨j, _, hj⟩ := mem_image.mp hA
      have h := pentagonal_injective (hj.trans h0.symm)
      change (j : ℤ) + 1 = 0 at h
      omega
    · obtain ⟨j, _, hj⟩ := mem_image.mp hB
      have h := pentagonal_injective (hj.trans h0.symm)
      change -((j : ℤ) + 1) = 0 at h
      omega
  have hS : S = {0} ∪ (A ∪ B) := by
    ext m
    simp only [S, mem_filter, mem_range, mem_union, mem_singleton]
    constructor
    · rintro ⟨hm, k, rfl⟩
      have hkn := (natAbs_le_pentagonal k).trans (Nat.lt_succ_iff.mp hm)
      by_cases hk : k = 0
      · exact Or.inl (hk ▸ h0)
      have hIndex : k.natAbs - 1 < n := by omega
      by_cases hkpos : 0 ≤ k
      · have hk' : (k.natAbs : ℤ) = k := by simp [abs_of_nonneg hkpos]
        have hEq : ((k.natAbs - 1 : ℕ) : ℤ) + 1 = k := by omega
        have ha' : a (k.natAbs - 1) = pentagonal k := congrArg pentagonal hEq
        exact Or.inr (Or.inl (mem_image.mpr ⟨k.natAbs - 1,
          mem_filter.mpr ⟨mem_range.mpr hIndex, ha'.symm ▸ Nat.lt_succ_iff.mp hm⟩, ha'⟩))
      · have hk' : (k.natAbs : ℤ) = -k := by simp [abs_of_neg (by omega : k < 0)]
        have hEq : -(((k.natAbs - 1 : ℕ) : ℤ) + 1) = k := by omega
        have hb' : b (k.natAbs - 1) = pentagonal k := congrArg pentagonal hEq
        exact Or.inr (Or.inr (mem_image.mpr ⟨k.natAbs - 1,
          mem_filter.mpr ⟨mem_range.mpr hIndex, hb'.symm ▸ Nat.lt_succ_iff.mp hm⟩, hb'⟩))
    · rintro (rfl | hm | hm)
      · exact ⟨Nat.succ_pos _, 0, h0⟩
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
        exact ⟨Nat.lt_succ_iff.mpr (mem_filter.mp hj).2, (j : ℤ) + 1, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
        exact ⟨Nat.lt_succ_iff.mpr (mem_filter.mp hj).2, -((j : ℤ) + 1), rfl⟩
  have hcoef := congrArg (coeff n) pentagonalKernel_mul_ordinaryPartitionSeries
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => coeff j pentagonalKernel * coeff k ordinaryPartitionSeries),
    PowerSeries.coeff_one, ite_eq_right hn.ne'] at hcoef
  simp only [coeff_pentagonalKernel, ordinaryPartitionSeries, PowerSeries.coeff_mk] at hcoef
  change (∑ m ∈ range (n + 1), T m) = 0 at hcoef
  have hsum : (∑ m ∈ S, T m) = ∑ m ∈ range (n + 1), T m := by
    dsimp only [S]
    rw [sum_filter]
    apply sum_congr rfl
    intro m hm
    by_cases hmem : m ∈ Set.range pentagonal
    · simp [hmem]
    · simp [hmem, T, pentagonalCoeff_of_not_mem hmem]
  rw [← hsum, hS, sum_union hzAB, sum_union hAB, sum_singleton] at hcoef
  have hT0 : T 0 = P n := by
    change pentagonalCoeff 0 * P (n - 0) = P n
    rw [← h0, pentagonalCoeff_at]
    simp [h0]
  have haT (j : ℕ) : T (a j) = -((-1 : ℤ) ^ j * P (n - a j)) := by
    change pentagonalCoeff (pentagonal ((j : ℤ) + 1)) * P (n - a j) = _
    rw [pentagonalCoeff_at, ← Int.natCast_succ, Int.coe_negOnePow_natCast, pow_succ]
    ring
  have hbT (j : ℕ) : T (b j) = -((-1 : ℤ) ^ j * P (n - b j)) := by
    change pentagonalCoeff (pentagonal (-((j : ℤ) + 1))) * P (n - b j) = _
    rw [pentagonalCoeff_at, Int.negOnePow_neg, ← Int.natCast_succ,
      Int.coe_negOnePow_natCast, pow_succ]
    ring
  have hA : (∑ m ∈ A, T m) = -∑ j ∈ range n, (-1 : ℤ) ^ j *
      (if a j ≤ n then P (n - a j) else 0) := by
    dsimp only [A]
    rw [sum_image ha.injOn, sum_filter, ← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    by_cases h : a j ≤ n <;> simp [h, haT]
  have hB : (∑ m ∈ B, T m) = -∑ j ∈ range n, (-1 : ℤ) ^ j *
      (if b j ≤ n then P (n - b j) else 0) := by
    dsimp only [B]
    rw [sum_image hb.injOn, sum_filter, ← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    by_cases h : b j ≤ n <;> simp [h, hbT]
  rw [hT0, hA, hB] at hcoef
  change P n = ∑ j ∈ range n, (-1 : ℤ) ^ j *
    ((if a j ≤ n then P (n - a j) else 0) + (if b j ≤ n then P (n - b j) else 0))
  simp_rw [mul_add]
  rw [sum_add_distrib]
  linarith only [hcoef]

end DurfeeCCS.Step14
