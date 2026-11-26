module

public import DurfeeCCS.Step06.TwoColour
public import DurfeeCCS.CoefficientDP
public import DurfeeCCS.Step10.OuterFarData
public import DurfeeCCS.Step08.SaddleAssembly
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Comparison of the bounded pair of partitions with the unrestricted pair, and
conversion from single-term domination to the sign of the Durfee polynomial. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open DurfeeCCS.Step06 Finset PowerSeries Real

private theorem restrictedOne_le {v d : ℕ} : ((Nat.Partition.restricted v (· ≤ d)).card : ℤ) ≤
    Fintype.card (Nat.Partition v) := by
  exact_mod_cast Finset.card_le_univ (Nat.Partition.restricted v (· ≤ d))

theorem restrictedPair_le_twoColour (d n : ℕ) :
    PowerSeries.coeff n (restrictedPairSeries d) ≤ twoColourPartitionCount n := by
  rw [coeff_restrictedPairSeries, twoColourPartitionCount_eq_convolution]
  exact Finset.sum_le_sum fun ab _ =>
    mul_le_mul restrictedOne_le restrictedOne_le (by positivity) (by positivity)

theorem twoColour_nonneg (n : ℕ) : 0 ≤ twoColourPartitionCount n := by
  rw [twoColourPartitionCount_eq_convolution]
  positivity

private theorem oneExtraFactor_le_twoColour (d n : ℕ) :
    PowerSeries.coeff n (restrictedPairSeries d * durfeeGeometricFactor (d + 1)) ≤
      twoColourPartitionCount n := by
  have hEq : restrictedPairSeries d * durfeeGeometricFactor (d + 1) =
      restrictedPartitionSeries d * restrictedPartitionSeries (d + 1) := by
    rw [restrictedPairSeries_eq_mul, restrictedPartitionSeries_eq_prod (d + 1),
      Finset.prod_range_succ, ← restrictedPartitionSeries_eq_prod, mul_assoc]
  rw [hEq, PowerSeries.coeff_mul, twoColourPartitionCount_eq_convolution]
  exact Finset.sum_le_sum fun ab _ =>
    mul_le_mul (by simpa using restrictedOne_le (v := ab.1) (d := d))
      (by simpa using restrictedOne_le (v := ab.2) (d := d + 1))
      (by rw [coeff_restrictedPartitionSeries]; positivity) (by positivity)

private theorem restrictedPair_gain_le (d n : ℕ) (hn : d + 1 ≤ n) :
    PowerSeries.coeff n (restrictedPairSeries (d + 1)) -
      PowerSeries.coeff n (restrictedPairSeries d) ≤
    2 * twoColourPartitionCount (n - (d + 1)) := by
  have ha := coeff_mul_geometric (restrictedPairSeries d) (d + 1) n (by omega)
  have hb := coeff_mul_geometric
    (restrictedPairSeries d * durfeeGeometricFactor (d + 1)) (d + 1) n (by omega)
  rw [ite_eq_left hn] at ha hb
  rw [← restrictedPairSeries_succ_eq_twice] at hb
  have h1 := oneExtraFactor_le_twoColour d (n - (d + 1))
  have h2 := restrictedPair_le_twoColour (d + 1) (n - (d + 1))
  linarith

/-- Removing the bound on the part sizes costs at most two copies of the coefficient
prefix through the size left after removing a part of size d+1. -/
theorem twoColour_sub_restrictedPair_le (n d : ℕ) :
    0 ≤ twoColourPartitionCount n - PowerSeries.coeff n (restrictedPairSeries d) ∧
    twoColourPartitionCount n - PowerSeries.coeff n (restrictedPairSeries d) ≤
      2 * ∑ v ∈ Finset.range (n - d), twoColourPartitionCount v := by
  refine ⟨sub_nonneg.mpr (restrictedPair_le_twoColour d n), ?_⟩
  generalize hN : n - d = N
  induction N generalizing d with
  | zero =>
      rw [twoColourPartitionCount_eq_coeff_restricted n d (by omega)]
      simp
  | succ N ih =>
      have hdn : d + 1 ≤ n := by omega
      have hdif : n - (d + 1) = N := by omega
      have hnext := ih (d + 1) hdif
      have hstep := restrictedPair_gain_le d n hdn
      rw [hdif] at hstep
      rw [Finset.sum_range_succ]
      linarith

set_option maxHeartbeats 600000 in
theorem durfeeCoeff_le_twoColour {n d : ℕ} (hd : d ^ 2 ≤ n) :
    (p n d : ℝ) ≤ (twoColourPartitionCount (n - d ^ 2) : ℝ) := by
  have heq := p_eq_coeff_restrictedPairSeries (n := n) (d := d) (by simpa [pow_two] using hd)
  exact_mod_cast (show (p n d : ℤ) ≤ twoColourPartitionCount (n - d ^ 2) by
    rw [heq, ← pow_two]
    exact restrictedPair_le_twoColour d _)

/-- Equation (67) specialized to the coefficient used in Lemma 4.3. -/
theorem durfeeCoeff_loss {n d : ℕ} (hd : d ^ 2 ≤ n) :
    0 ≤ (twoColourPartitionCount (n - d ^ 2) : ℝ) - p n d ∧
      (twoColourPartitionCount (n - d ^ 2) : ℝ) - p n d ≤
        2 * ∑ v ∈ Finset.range (n - d ^ 2 - d), (twoColourPartitionCount v : ℝ) := by
  have heq := p_eq_coeff_restrictedPairSeries (n := n) (d := d) (by simpa [pow_two] using hd)
  have h := twoColour_sub_restrictedPair_le (n - d ^ 2) d
  rw [show n - d ^ 2 = n - d * d by rw [pow_two], ← heq] at h
  rw [← pow_two] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- The endpoint coefficient when the partition consists of its square. -/
theorem durfee_square_coeff {n d : ℕ} (hn : n = d ^ 2) : p n d = 1 := by
  have hs : d * d ≤ n := by rw [hn, pow_two]
  have heq := p_eq_coeff_restrictedPairSeries hs
  rw [Nat.sub_eq_zero_of_le (by rw [hn, pow_two]), coeff_restrictedPairSeries_zero] at heq
  exact_mod_cast heq

/-- Positive weights for the absolute value of individual monomials. -/
def farWeighted (n l : ℕ) (h : ℝ) : ℝ := (p n l : ℝ) * exp ((l : ℝ) * h)

theorem farWeighted_nonneg (n l : ℕ) (h : ℝ) : 0 ≤ farWeighted n l h := by
  unfold farWeighted
  positivity

/-- Strict dominance of the d-th monomial gives the required sign at x = exp h. -/
theorem farSign_of_dominance {n d : ℕ} {h : ℝ} (hn : 0 < n)
    (hd : d ∈ Finset.Icc 1 n.sqrt)
    (hdom : (∑ l ∈ (Finset.Icc 1 n.sqrt).erase d, farWeighted n l h) < farWeighted n d h) :
    0 < (-1 : ℝ) ^ d * Step08.durfeeNegativeValue n (exp (h / 2)) := by
  have hz : p n 0 = 0 := p_zero_of_pos hn
  have heval : Step08.durfeeNegativeValue n (exp (h / 2)) =
      ∑ l ∈ Finset.Icc 1 n.sqrt, (-1 : ℝ) ^ l * farWeighted n l h := by
    unfold Step08.durfeeNegativeValue durfeePolynomial
    simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial, map_natCast]
    have hs : (exp (h / 2)) ^ 2 = exp h := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hs]
    have hterm (l : ℕ) :
        (p n l : ℝ) * (-(exp h)) ^ l = (-1 : ℝ) ^ l * farWeighted n l h := by
      unfold farWeighted
      rw [Real.exp_nat_mul, show -(exp h) = -1 * exp h by simp, mul_pow]
      ring
    simp_rw [hterm]
    have hr : Finset.range (n.sqrt + 1) = insert 0 (Finset.Icc 1 n.sqrt) := by
      ext l
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hr, Finset.sum_insert (by simp : 0 ∉ Finset.Icc 1 n.sqrt)]
    simp [farWeighted, hz]
  have hmain : (-1 : ℝ) ^ d * ((-1 : ℝ) ^ d * farWeighted n d h) =
      farWeighted n d h := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  have hsplit := Finset.sum_erase_add (f := fun l => (-1 : ℝ) ^ l * farWeighted n l h) _ hd
  rw [heval, ← hsplit, mul_add, hmain, Finset.mul_sum]
  have ht : -(∑ l ∈ (Finset.Icc 1 n.sqrt).erase d, farWeighted n l h) ≤
      ∑ l ∈ (Finset.Icc 1 n.sqrt).erase d, (-1 : ℝ) ^ d * ((-1 : ℝ) ^ l * farWeighted n l h) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun l _ => ?_
    have ha : |(-1 : ℝ) ^ d * ((-1 : ℝ) ^ l * farWeighted n l h)| = farWeighted n l h := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow]
      simp [abs_of_nonneg (farWeighted_nonneg n l h)]
    linarith [neg_abs_le ((-1 : ℝ) ^ d * ((-1 : ℝ) ^ l * farWeighted n l h))]
  linarith

end DurfeeCCS.Step10
