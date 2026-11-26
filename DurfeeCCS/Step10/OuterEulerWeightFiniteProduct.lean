module

public import DurfeeCCS.Step10.OuterEulerWeightFinite
public import DurfeeCCS.Step10.OuterEulerWeight
public import DurfeeCCS.Step10.OuterEulerTail
import Mathlib.Tactic

/-! Finite outer gamma weights with the zero triple removed. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Finset PowerSeries

private theorem outerMixedCoeff_cast_nonneg (a b j : ℕ) : 0 ≤ ((coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℝ) := by
  have h : 0 ≤ coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) := by
    rw [PowerSeries.coeff_mul]
    simp only [coeff_restrictedPartitionSeries]
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  exact_mod_cast h

/-- The finite sum of nonzero gamma weights is bounded by the reciprocal Euler product minus one. -/
private theorem finite_nonzero_gamma_weight_le_left {w σ : ℝ}
    (hw₀ : 0 ≤ w) (hw : w < 1) (hσ : 0 < σ)
    (A : Finset ((ℕ × ℕ) × ℕ)) (hA : ((0, 0), 0) ∉ A) :
    (∑ p ∈ A, ((coeff p.2 (restrictedPartitionSeries p.1.1 * restrictedPartitionSeries p.1.2) : ℤ) : ℝ) *
      w ^ (p.1.1 + p.1.2) * Real.exp (-σ * outerGamma p.1.1 p.1.2 p.2)) ≤
      outerWeightProduct w σ - 1 := by
  let q := Real.exp (-σ)
  let z := w * Real.exp (-σ / 2)
  have hq₀ : 0 ≤ q := (Real.exp_pos _).le
  have hz₀ : 0 ≤ z := by dsimp [z]; positivity
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hz : z < 1 := by
    have he : Real.exp (-σ / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact (mul_le_of_le_one_right hw₀ he).trans_lt hw
  let F := outerEulerTerm q z
  have hF (n : ℕ) : (F n : ℂ) = (z : ℂ)^n * (qPochhammer (q : ℂ) (q : ℂ) n)⁻¹ := by
    change ((z ^ n / outerWeightQFactorial q n : ℝ) : ℂ) = _
    rw [Complex.ofReal_div, Complex.ofReal_pow, outerWeightQFactorial_cast, div_eq_mul_inv]
  have hF₀ (n : ℕ) : 0 ≤ F n := by
    exact div_nonneg (pow_nonneg hz₀ _) (outerWeightQFactorial_pos hq₀ hq _).le
  have hFs := outerEulerTerm_summable hq₀ hq hz₀ hz
  have hbound := finite_nonzero_triple_weight_le hq₀ hq hz₀ F hF hF₀ hFs A hA
  have hEq : (∑' n : ℕ, F n) ^ 2 = outerWeightProduct w σ :=
    outerEulerSeries_sq_eq_weightProduct hw₀ hw hσ
  rw [hEq] at hbound
  apply le_trans ?_ hbound
  apply Finset.sum_le_sum
  rintro ⟨⟨a,b⟩,j⟩ hj
  have hR : Real.exp (-σ * outerGamma a b j) ≤
      Real.exp (-σ * ((j : ℝ) + ((a : ℝ) + b) / 2)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (outerGamma_lower a b j) (neg_nonpos.mpr hσ.le)
  refine (mul_le_mul_of_nonneg_left hR
    (mul_nonneg (outerMixedCoeff_cast_nonneg a b j) (pow_nonneg hw₀ _))).trans_eq ?_
  change ((coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℝ) * w ^ (a + b) *
      Real.exp (-σ * ((j : ℝ) + ((a : ℝ) + b) / 2)) =
    ((coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℝ) * z ^ (a + b) * q ^ j
  calc
    _ = (((coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℝ) * w ^ (a + b)) *
        (Real.exp (↑(a + b : ℕ) * (-σ / 2)) * Real.exp ((j : ℝ) * -σ)) := by
      rw [← Real.exp_add]
      congr 2
      push_cast
      ring
    _ = _ := by simp only [z, q, mul_pow, Real.exp_nat_mul]; ring

/-- The mass bound in the same tuple convention as the finite Durfee expansion. -/
theorem finite_nonzero_gamma_weight_le {w σ : ℝ}
    (hw₀ : 0 ≤ w) (hw : w < 1) (hσ : 0 < σ)
    (A : Finset (ℕ × ℕ × ℕ)) (hA : (0, 0, 0) ∉ A) :
    (∑ p ∈ A, ((coeff p.2.2 (restrictedPartitionSeries p.1 * restrictedPartitionSeries p.2.1) : ℤ) : ℝ) *
      w ^ (p.1 + p.2.1) * Real.exp (-σ * outerGamma p.1 p.2.1 p.2.2)) ≤
      outerWeightProduct w σ - 1 := by
  let e := (Equiv.prodAssoc ℕ ℕ ℕ).symm
  have hz : ((0, 0), 0) ∉ A.map e.toEmbedding := by
    intro h
    obtain ⟨p, hp, he⟩ := Finset.mem_map.mp h
    have hp' : p = (0, 0, 0) := by
      apply e.injective
      exact he
    exact hA (hp' ▸ hp)
  simpa [e, Finset.sum_map] using finite_nonzero_gamma_weight_le_left hw₀ hw hσ (A.map e.toEmbedding) hz

end DurfeeCCS.Step10
