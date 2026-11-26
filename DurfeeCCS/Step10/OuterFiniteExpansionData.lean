module

public import DurfeeCCS.Step10.OuterEulerTail
public import DurfeeCCS.Step10.OuterReplacement
public import DurfeeCCS.Step10.OuterBesselPoisson
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset Step06

/-- The coefficient P_{a,b}(j) from the two finite geometric products. -/
def outerMixedCoeff (a b j : ℕ) : ℤ :=
  PowerSeries.coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b)

def outerTripleBox (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  range (n + 1) ×ˢ (range (n + 1) ×ˢ range (n + 1))

def outerTripleRadius (n a b j : ℕ) : ℝ :=
  sqrt ((outerY n) ^ 2 - outerGamma a b j)

def outerGoodTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (outerTripleBox n).filter (fun abj => 0.9 * outerY n ≤
    outerTripleRadius n abj.1 abj.2.1 abj.2.2)

def outerShiftedIndex (n d a b j : ℕ) : ℤ :=
  (n : ℤ) - ((d ^ 2 + outerTailPower d a + outerTailPower d b + j : ℕ) : ℤ)

def outerTripleValue (n : ℕ) (h : ℝ) (abj : ℕ × ℕ × ℕ) : ℝ :=
  (-1 : ℝ) ^ (abj.1 + abj.2.1) * (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) *
    ∑ d ∈ Icc 1 n.sqrt, (-exp h) ^ d * clippedTwoColour (outerShiftedIndex n d abj.1 abj.2.1 abj.2.2)

def outerTripleKernel (n : ℕ) (h : ℝ) (abj : ℕ × ℕ × ℕ) : ℝ :=
  (-1 : ℝ) ^ (abj.1 + abj.2.1) * (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) *
    (∑' d : ℤ, (-(exp h : ℂ)) ^ d *
      (outerBesselKernel (outerTripleRadius n abj.1 abj.2.1 abj.2.2)
        ((d : ℝ) + ((abj.1 : ℝ) + abj.2.1) / 2) : ℂ)).re

theorem outerMixedCoeff_nonneg (a b j : ℕ) : 0 ≤ outerMixedCoeff a b j := by
  unfold outerMixedCoeff
  rw [PowerSeries.coeff_mul]
  simp only [coeff_restrictedPartitionSeries]
  positivity

theorem outerMixedCoeff_le_twoColour (a b j : ℕ) : outerMixedCoeff a b j ≤ twoColourPartitionCount j := by
  unfold outerMixedCoeff
  rw [PowerSeries.coeff_mul, twoColourPartitionCount_eq_convolution]
  have hcard (c t : ℕ) : ((Nat.Partition.restricted t (· ≤ c)).card : ℤ) ≤
      Fintype.card (Nat.Partition t) :=
    by exact_mod_cast Finset.card_le_univ (Nat.Partition.restricted t (· ≤ c))
  apply Finset.sum_le_sum
  intro kl _
  simp only [coeff_restrictedPartitionSeries]
  exact mul_le_mul (hcard _ _) (hcard _ _) (by positivity) (by positivity)

@[simp] theorem outerMixedCoeff_zero_zero (j : ℕ) :
    outerMixedCoeff 0 0 j = if j = 0 then 1 else 0 := by
  simp [outerMixedCoeff, restrictedPartitionSeries_eq_prod]

theorem outerShiftedIndex_sq {n d a b j : ℕ} (hn : 1 ≤ n)
    (hr : outerGamma a b j ≤ (outerY n) ^ 2) :
    (outerTripleRadius n a b j) ^ 2 -
      ((d : ℝ) + ((a : ℝ) + b) / 2) ^ 2 =
        (outerShiftedIndex n d a b j : ℝ) - 1 / 12 := by
  unfold outerTripleRadius outerShiftedIndex
  have he := outerGamma_complete_square d a b j
  push_cast at he ⊢
  rw [sq_sqrt (sub_nonneg.mpr hr), outerY_sq hn]
  linarith only [he]

theorem outerTripleRadius_le (n a b j : ℕ) : outerTripleRadius n a b j ≤ outerY n := by
  have hγ : 0 ≤ outerGamma a b j := (by positivity : 0 ≤ (j : ℝ) + ((a : ℝ) + b) / 2).trans
    (outerGamma_lower _ _ _)
  have hy : 0 ≤ outerY n := sqrt_nonneg _
  exact (sqrt_le_sqrt (sub_le_self _ hγ)).trans_eq (sqrt_sq hy)

end DurfeeCCS.Step10
