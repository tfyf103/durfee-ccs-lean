module

public import DurfeeCCS.Step10.OuterExpansion
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset Step06

private theorem outerShiftedCoeff_eq_sum {n d a b : ℕ} (hd : d ^ 2 ≤ n) :
    (outerShiftedCoeff d a b (n - d ^ 2) : ℝ) =
      (-1 : ℝ) ^ (a + b) * ∑ j ∈ range (n + 1),
        (outerMixedCoeff a b j : ℝ) * clippedTwoColour (outerShiftedIndex n d a b j) := by
  unfold outerShiftedCoeff
  by_cases hv : outerTailPower d a + outerTailPower d b ≤ n - d ^ 2
  · rw [ite_eq_left hv, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_sum]
    congr 1
    calc
      _ = ∑ j ∈ range (n - d ^ 2 - (outerTailPower d a + outerTailPower d b) + 1),
          (outerMixedCoeff a b j : ℝ) * clippedTwoColour (outerShiftedIndex n d a b j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        have hnon : 0 ≤ outerShiftedIndex n d a b j := by unfold outerShiftedIndex; omega
        have hidx : (outerShiftedIndex n d a b j).toNat =
            n - d ^ 2 - (outerTailPower d a + outerTailPower d b) - j := by
          unfold outerShiftedIndex
          omega
        rw [clippedTwoColour, ite_eq_left hnon, hidx, Int.cast_mul]
      _ = _ := by
        apply Finset.sum_subset
        · exact range_mono (by omega)
        · intro j _ hx
          have hx' := not_lt.mp (fun h => hx (mem_range.mpr h))
          have hneg : ¬ 0 ≤ outerShiftedIndex n d a b j := by unfold outerShiftedIndex; omega
          simp [clippedTwoColour, hneg]
  · rw [ite_eq_right hv, Int.cast_zero, Finset.sum_eq_zero]
    · simp
    · intro j _
      have hh : ¬ 0 ≤ outerShiftedIndex n d a b j := by unfold outerShiftedIndex; omega
      simp [clippedTwoColour, hh]

private theorem outerTailPower_ge (d a : ℕ) (hd : 1 ≤ d) : a ≤ outerTailPower d a := by
  unfold outerTailPower
  exact (show a ≤ d * a by simpa using Nat.mul_le_mul_right a hd).trans (Nat.le_add_right _ _)

private theorem durfeeCoeff_eq_outerBox {n d : ℕ} (hd : 1 ≤ d) (hdm : d ≤ n.sqrt) :
    (p n d : ℝ) = ∑ ab ∈ range (n + 1) ×ˢ range (n + 1),
      (outerShiftedCoeff d ab.1 ab.2 (n - d ^ 2) : ℝ) := by
  have hsq : d ^ 2 ≤ n := by
    have H := (Nat.sqrt_le n)
    nlinarith only [hdm, H]
  have hp := p_eq_coeff_restrictedPairSeries (n := n) (d := d) (by simpa [pow_two] using hsq)
  rw [← pow_two, restrictedPair_coefficient_eq_outerExpansion] at hp
  have hr := congrArg (Int.cast : ℤ → ℝ) hp
  push_cast at hr
  rw [hr]
  exact Finset.sum_subset (product_subset_product (range_mono (by omega)) (range_mono (by omega)))
    (fun ab _ hab => by
      have hpower : ¬ outerTailPower d ab.1 + outerTailPower d ab.2 ≤ n - d ^ 2 := by
        intro hv
        have ha := outerTailPower_ge d ab.1 hd
        have hb := outerTailPower_ge d ab.2 hd
        exact hab (mem_product.2 ⟨mem_range.2 (by omega), mem_range.2 (by omega)⟩)
      simp [outerShiftedCoeff, hpower])

/-- The exact finite Euler expansion of the real Durfee evaluation. -/
theorem durfeeNegativeValue_eq_outerTripleSum {n : ℕ} (hn : 0 < n) (h : ℝ) :
    Step08.durfeeNegativeValue n (exp (h / 2)) =
      ∑ abj ∈ outerTripleBox n, outerTripleValue n h abj := by
  rw [durfeeNegativeValue_exp_half]
  unfold durfeePolynomialReal durfeePolynomial outerTripleBox outerTripleValue
  simp only [Polynomial.map_sum, Polynomial.map_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, map_natCast]
  have hz : p n 0 = 0 := p_zero_of_pos hn
  rw [show range (n.sqrt + 1) = insert 0 (Icc 1 n.sqrt) by
    ext d; simp [mem_range, Finset.mem_Icc]; omega,
    Finset.sum_insert (by simp)]
  simp only [hz, Nat.cast_zero, zero_mul, zero_add]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := mem_Icc.mp hd
  rw [durfeeCoeff_eq_outerBox hd'.1 hd'.2]
  simp_rw [Finset.sum_product, outerShiftedCoeff_eq_sum (by
    have H := Nat.sqrt_le n
    nlinarith only [hd'.2, H] : d ^ 2 ≤ n)]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end DurfeeCCS.Step10
