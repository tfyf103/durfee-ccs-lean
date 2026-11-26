module

public import DurfeeCCS.Main
public import DurfeeCCS.PartitionTotals
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! The uniform partition law and its probability generating polynomial. -/

public section

namespace DurfeeCCS

open MeasureTheory Polynomial
open scoped BigOperators ENNReal

instance (n : ℕ) : MeasurableSpace (Nat.Partition n) := ⊤

instance (n : ℕ) : DiscreteMeasurableSpace (Nat.Partition n) := ⟨fun _ => trivial⟩

/-- The equiprobable distribution on all ordinary partitions of size n. -/
noncomputable def uniformPartitionMeasure (n : ℕ) : Measure (Nat.Partition n) :=
  (Fintype.card (Nat.Partition n) : ℝ≥0∞)⁻¹ • Measure.count

instance (n : ℕ) : IsProbabilityMeasure (uniformPartitionMeasure n) where
  measure_univ := by
    rw [uniformPartitionMeasure, smul_apply, smul_eq_mul, Measure.count_univ,
      ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (Fintype.card_pos (α := Nat.Partition n)).ne')
      (ENNReal.natCast_ne_top _)

/-- Choosing a partition uniformly gives every individual partition the same mass. -/
theorem uniformPartitionMeasure_singleton (n : ℕ) (P : Nat.Partition n) :
    uniformPartitionMeasure n {P} = (Fintype.card (Nat.Partition n) : ℝ≥0∞)⁻¹ := by
  classical
  simp [uniformPartitionMeasure]

/-- The law of the Durfee side under the uniform measure on partitions of size n. -/
@[expose]
noncomputable def durfeeDistribution (n : ℕ) : Measure ℕ :=
  Measure.map (@partitionSide n) (uniformPartitionMeasure n)

instance (n : ℕ) : IsProbabilityMeasure (durfeeDistribution n) := by
  unfold durfeeDistribution
  exact (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance

theorem durfeePolynomialReal_eval_one (n : ℕ) :
    (durfeePolynomialReal n).eval 1 = (Fintype.card (Nat.Partition n) : ℝ) := by
  rw [durfeePolynomialReal, eval_map, eval₂_at_one,
    durfeePolynomial_eval_one_eq_card_partitions]
  simp

theorem durfeePolynomialReal_eval_one_pos (n : ℕ) :
    0 < (durfeePolynomialReal n).eval 1 := by
  rw [durfeePolynomialReal_eval_one]
  exact_mod_cast Fintype.card_pos (α := Nat.Partition n)

/-- The probability that the Durfee side of a uniform partition of n equals d. -/
@[expose]
noncomputable def durfeeMass (n d : ℕ) : ℝ :=
  (p n d : ℝ) / (durfeePolynomialReal n).eval 1

theorem durfeeDistribution_singleton (n d : ℕ) :
    durfeeDistribution n {d} =
      (p n d : ℝ≥0∞) / (Fintype.card (Nat.Partition n) : ℝ≥0∞) := by
  classical
  let fiber : Finset (Nat.Partition n) := Finset.univ.filter fun P => partitionSide P = d
  have hfiber : (@partitionSide n) ⁻¹' {d} = (fiber : Set (Nat.Partition n)) := by
    ext P
    simp [fiber]
  rw [durfeeDistribution, Measure.map_apply Measurable.of_discrete (measurableSet_singleton d),
    hfiber, uniformPartitionMeasure, smul_apply, smul_eq_mul, Measure.count_apply_finset,
    p_eq_card_partitions_side, Nat.card_eq_fintype_card, Fintype.card_subtype, div_eq_mul_inv,
    mul_comm]

@[simp] theorem durfeeDistribution_singleton_toReal (n d : ℕ) :
    (durfeeDistribution n).real {d} = durfeeMass n d := by
  rw [measureReal_def, durfeeDistribution_singleton, ENNReal.toReal_div, durfeeMass,
    durfeePolynomialReal_eval_one]
  simp

theorem durfeeMass_zero_of_sqrt_lt {n d : ℕ} (hd : n.sqrt < d) : durfeeMass n d = 0 := by
  simp [durfeeMass, p_eq_zero_of_sq_gt (Nat.sqrt_lt.mp hd)]

theorem durfeeMass_zero_of_pos {n : ℕ} (hn : 0 < n) : durfeeMass n 0 = 0 := by
  simp [durfeeMass, p_zero_of_pos hn]

/-- The probability generating polynomial of the Durfee side. -/
noncomputable def durfeePGF (n : ℕ) : ℝ[X] :=
  ∑ d ∈ Finset.range (n.sqrt + 1), monomial d ((durfeeDistribution n).real {d})

@[simp] theorem coeff_durfeePGF (n d : ℕ) : (durfeePGF n).coeff d = durfeeMass n d := by
  classical
  simp only [durfeePGF, finsetSum_coeff, coeff_monomial_apply,
    durfeeDistribution_singleton_toReal]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · exact (durfeeMass_zero_of_sqrt_lt (by simpa using hd)).symm

/-- Dividing D_n by its value at one gives the exact probability generating polynomial. -/
theorem durfeePGF_eq_normalized (n : ℕ) :
    durfeePGF n = C ((durfeePolynomialReal n).eval 1)⁻¹ * durfeePolynomialReal n := by
  ext d
  rw [coeff_durfeePGF, coeff_C_mul, coeff_durfeePolynomialReal, durfeeMass, div_eq_mul_inv,
    mul_comm]

theorem durfeePGF_eval_eq_div (n : ℕ) (x : ℝ) :
    (durfeePGF n).eval x = (durfeePolynomialReal n).eval x / (durfeePolynomialReal n).eval 1 := by
  rw [durfeePGF_eq_normalized, eval_mul, eval_C, div_eq_mul_inv, mul_comm]

/-- In particular the probability generating function is normalized at one. -/
@[simp] theorem durfeePGF_eval_one (n : ℕ) : (durfeePGF n).eval 1 = 1 := by
  rw [durfeePGF_eq_normalized, eval_mul, eval_C, inv_mul_cancel₀]
  exact (durfeePolynomialReal_eval_one_pos n).ne'

/-- Evaluation of the PGF is the mean of x raised to the Durfee side. -/
theorem durfeePGF_eval_eq_integral (n : ℕ) (x : ℝ) :
    (durfeePGF n).eval x = ∫ P, x ^ partitionSide P ∂uniformPartitionMeasure n := by
  rw [durfeePGF_eq_normalized, eval_mul, eval_C, durfeePolynomialReal_eval_one,
    durfeePolynomialReal, eval_map, durfeePolynomial_eq_sum_partitions, eval₂_finsetSum,
    integral_fintype Integrable.of_finite, Finset.mul_sum]
  simp [eval₂_pow, uniformPartitionMeasure_singleton, measureReal_def, smul_eq_mul]

/-- Creating the Bernoulli parameter attached to a negative Durfee root -r. -/
noncomputable def durfeeRootProbability (r : ℝ) (hr : 0 < r) : Set.Icc (0 : ℝ) 1 :=
  ⟨(1 + r)⁻¹, inv_nonneg.mpr (by positivity),
    inv_le_one_of_one_le₀ (by linarith)⟩

@[simp] theorem durfeeRootProbability_val (r : ℝ) (hr : 0 < r) :
    (durfeeRootProbability r hr : ℝ) = 1 / (1 + r) := one_div _ |>.symm

private theorem durfeeRootProbability_factor (r : ℝ) (hr : 0 < r) :
    C ((1 + r)⁻¹) * (X + C r) =
      C (1 - (durfeeRootProbability r hr : ℝ))
        + C (durfeeRootProbability r hr : ℝ) * X := by
  have hsum : (1 : ℝ) + r ≠ 0 := by positivity
  have hc : (1 + r)⁻¹ * r = 1 - (1 + r)⁻¹ := by
    field_simp
    ring
  change C ((1 + r)⁻¹) * (X + C r) = C (1 - (1 + r)⁻¹) + C ((1 + r)⁻¹) * X
  rw [mul_add, ← C_mul, hc, add_comm]

/-- The normalization of a root factorization has a Bernoulli factor for each nonzero root. -/
theorem durfeePGF_factorization {n : ℕ}
    (r : Fin (n.sqrt - 1) ↪ ℝ) (hr : ∀ i, 0 < r i)
    (hfac : durfeePolynomialReal n = C (p n n.sqrt : ℝ) * X * ∏ i, (X + C (r i))) :
    durfeePGF n =
      X * ∏ i, (C (1 - (durfeeRootProbability (r i) (hr i) : ℝ))
        + C (durfeeRootProbability (r i) (hr i) : ℝ) * X) := by
  classical
  have heval : (durfeePolynomialReal n).eval 1 =
      (p n n.sqrt : ℝ) * ∏ i, (1 + r i) := by
    rw [hfac]
    simp only [eval_mul, eval_C, eval_X, mul_one, eval_prod, eval_add]
  have hlead : (p n n.sqrt : ℝ) ≠ 0 := by
    intro h
    have hpos := durfeePolynomialReal_eval_one_pos n
    simp [heval, h] at hpos
  have hsplit : C ((durfeePolynomialReal n).eval 1)⁻¹ =
      C (p n n.sqrt : ℝ)⁻¹ * ∏ i, C ((1 + r i)⁻¹) := by
    rw [heval, mul_inv_rev, mul_comm, C_mul, ← Finset.prod_inv_distrib, map_prod]
  rw [durfeePGF_eq_normalized, hsplit, hfac]
  calc
    _ = X * ((C (p n n.sqrt : ℝ)⁻¹ * C (p n n.sqrt : ℝ)) *
        ((∏ i, C ((1 + r i)⁻¹)) * ∏ i, (X + C (r i)))) := by ring
    _ = X * ∏ i, (C ((1 + r i)⁻¹) * (X + C (r i))) := by
      rw [← C_mul, inv_mul_cancel₀ hlead, C_1, one_mul, Finset.prod_mul_distrib]
    _ = _ := by
      congr 1
      exact Finset.prod_congr rfl fun i _ => durfeeRootProbability_factor _ (hr i)

/-- The degree-one law is deterministic, with the empty family of Bernoulli factors. -/
theorem durfeePGF_of_sqrt_eq_one {n : ℕ} (h : n.sqrt = 1) : durfeePGF n = X := by
  have hn : 1 ≤ n := by
    have hs := Nat.sqrt_le n
    rw [h] at hs
    simpa using hs
  obtain ⟨r, hr, hfac⟩ := durfee_factorization n hn
  let _ : IsEmpty (Fin (n.sqrt - 1)) := by
    rw [h, Nat.sub_self]
    infer_instance
  simpa using durfeePGF_factorization r hr hfac

/-- When the largest admissible side is one, the Durfee side equals one almost surely. -/
theorem durfeeDistribution_of_sqrt_eq_one {n : ℕ} (h : n.sqrt = 1) :
    durfeeDistribution n = Measure.dirac 1 := by
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro d
  rw [durfeeDistribution_singleton_toReal, ← coeff_durfeePGF, durfeePGF_of_sqrt_eq_one h,
    coeff_X, measureReal_def]
  by_cases hd : d = 1 <;> simp [hd, Set.mem_singleton_iff, eq_comm]

end DurfeeCCS
