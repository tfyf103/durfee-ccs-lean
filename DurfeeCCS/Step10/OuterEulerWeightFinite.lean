module

public import DurfeeCCS.Step06.GeneratingAnalytic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! Bounding finite sums of nonzero triples by the Euler-series mass. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Finset PowerSeries

/-- The mixed coefficient with the nonnegative size and degree weights in the outer range. -/
def outerFiniteTripleWeight (q z : ℝ) (p : (ℕ × ℕ) × ℕ) : ℝ :=
  ((coeff p.2 (restrictedPartitionSeries p.1.1 * restrictedPartitionSeries p.1.2) : ℤ) : ℝ) *
    z ^ (p.1.1 + p.1.2) * q ^ p.2

private theorem outerFiniteTripleWeight_nonneg {q z : ℝ} (hq : 0 ≤ q) (hz : 0 ≤ z)
    (p : (ℕ × ℕ) × ℕ) : 0 ≤ outerFiniteTripleWeight q z p := by
  have hc : 0 ≤ coeff p.2 (restrictedPartitionSeries p.1.1 * restrictedPartitionSeries p.1.2) := by
    rw [PowerSeries.coeff_mul]
    simp only [coeff_restrictedPartitionSeries]
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  exact mul_nonneg (mul_nonneg (by exact_mod_cast hc) (pow_nonneg hz _)) (pow_nonneg hq _)

private theorem outerFiniteTripleWeight_zero (q z : ℝ) :
    outerFiniteTripleWeight q z ((0, 0), 0) = 1 := by
  simp [outerFiniteTripleWeight, restrictedPartitionSeries_zero, PowerSeries.coeff_one]

private theorem outerFiniteTripleWeight_hasSum {q z : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1)
    (F : ℕ → ℝ) (hF : ∀ n, (F n : ℂ) = (z : ℂ)^n * (qPochhammer (q : ℂ) (q : ℂ) n)⁻¹)
    (ab : ℕ × ℕ) :
    HasSum (fun j => outerFiniteTripleWeight q z (ab, j)) (F ab.1 * F ab.2) := by
  have hq' : ‖(q : ℂ)‖ < 1 := by simpa [abs_of_nonneg hq₀] using hq
  have hseries := (hasSum_coeff_restrictedMixedSeries hq' ab.1 ab.2).1
  have hsum := Complex.hasSum_re (hseries.mul_left ((z : ℂ) ^ (ab.1 + ab.2)))
  have hprod :
      (z : ℂ) ^ (ab.1 + ab.2) *
        ((qPochhammer (q : ℂ) (q : ℂ) ab.1)⁻¹ * (qPochhammer (q : ℂ) (q : ℂ) ab.2)⁻¹) =
        ((F ab.1 * F ab.2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, hF, hF, pow_add]
    ring
  rw [hprod, Complex.ofReal_re] at hsum
  refine hsum.congr_fun ?_
  intro j
  simp only [outerFiniteTripleWeight, ← Complex.ofReal_intCast, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- Any finite subfamily of nonzero triples has mass at most the square of the
corresponding Euler series less the contribution of the origin. -/
theorem finite_nonzero_triple_weight_le {q z : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1) (hz : 0 ≤ z)
    (F : ℕ → ℝ) (hF : ∀ n, (F n : ℂ) = (z : ℂ)^n * (qPochhammer (q : ℂ) (q : ℂ) n)⁻¹)
    (hF₀ : ∀ n, 0 ≤ F n) (hFsum : Summable F)
    (A : Finset ((ℕ × ℕ) × ℕ)) (hA : ((0, 0), 0) ∉ A) :
    ∑ p ∈ A, outerFiniteTripleWeight q z p ≤ (∑' n, F n) ^ 2 - 1 := by
  let f := outerFiniteTripleWeight q z
  have hf (p : (ℕ × ℕ) × ℕ) : 0 ≤ f p := outerFiniteTripleWeight_nonneg hq₀ hz p
  have hs (ab : ℕ × ℕ) : HasSum (fun j => f (ab, j)) (F ab.1 * F ab.2) :=
    outerFiniteTripleWeight_hasSum hq₀ hq F hF ab
  have hM := hFsum.mul_of_nonneg hFsum hF₀ hF₀
  have hS : Summable f := by
    refine (summable_prod_of_nonneg hf).mpr ⟨(fun ab => (hs ab).summable), ?_⟩
    simp_rw [(hs _).tsum_eq]
    exact hM
  have hT : (∑' p, f p) = (∑' n, F n) ^ 2 := by
    rw [hS.tsum_prod]
    simp_rw [(hs _).tsum_eq]
    rw [hM.tsum_prod]
    simp_rw [tsum_mul_left]
    rw [tsum_mul_right, pow_two]
  classical
  have hbound := hS.sum_le_tsum (insert ((0, 0), 0) A) (fun p _ => hf p)
  rw [Finset.sum_insert hA, hT] at hbound
  change outerFiniteTripleWeight q z ((0, 0), 0) + _ ≤ _ at hbound
  rw [outerFiniteTripleWeight_zero] at hbound
  linarith

end DurfeeCCS.Step10
