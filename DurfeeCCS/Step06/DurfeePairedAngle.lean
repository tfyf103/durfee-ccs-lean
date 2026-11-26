module

public import DurfeeCCS.Step06.EulerConstantTerm
public import DurfeeCCS.Step06.PairedAngle
public import DurfeeCCS.Step06.PairedProduct

/-! Equation (3) from the Euler expansion and the orthogonality of the angular modes. -/

@[expose] public section

namespace DurfeeCCS.Step06

open Complex

private theorem pairedTerm_eq_euler (r θ : ℝ) (ζ : ℂ) (j : ℕ) :
    pairedTerm r θ ζ j =
      ((r : ℂ) * I * exp (-ζ / 2) * exp ((θ : ℂ) * I)) * exp (-ζ) ^ j := by
  calc
    _ = (r : ℂ) * I * ((exp (-ζ / 2) * exp ((θ : ℂ) * I)) * exp ((j : ℂ) * (-ζ))) := by
      rw [pairedTerm, ← exp_add, ← exp_add]
      congr 2
      ring
    _ = _ := by rw [exp_nat_mul]; ac_rfl

private theorem eulerQTerm_shift (q z : ℂ) (θ : ℝ) (n : ℕ) :
    eulerQTerm q (z * exp ((θ : ℂ) * I)) n =
      eulerQTerm q z n * exp ((n : ℂ) * I * θ) := by
  have hphase : exp ((n : ℂ) * I * θ) = exp ((θ : ℂ) * I) ^ n := by
    rw [← exp_nat_mul]
    congr 1
    ring
  rw [hphase]
  simp only [eulerQTerm, mul_pow, div_eq_mul_inv]
  ring

/-- Equation (3) for the paired product on the right half-plane. -/
theorem durfeeAnalyticF_eq_pairedAngle (r : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) :
    durfeeAnalyticF (-(r : ℂ) ^ 2) (exp (-ζ)) =
      (2 * Real.pi : ℂ)⁻¹ * ∫ θ : ℝ in -Real.pi..Real.pi, pairedProduct r θ ζ := by
  let q := exp (-ζ)
  let z := (r : ℂ) * I * exp (-ζ / 2)
  let a := eulerQTerm q z
  have hq : ‖q‖ < 1 := by
    rw [show q = exp (-ζ) from rfl, norm_exp, neg_re, Real.exp_lt_one_iff]
    exact neg_neg_of_pos hζ
  have hz : z * z = (-(r : ℂ) ^ 2) * q := by
    dsimp only [z, q]
    have hexp : exp (-ζ / 2) * exp (-ζ / 2) = exp (-ζ) := by
      rw [← exp_add]
      congr 1
      ring
    calc
      _ = (r : ℂ) ^ 2 * I ^ 2 * (exp (-ζ / 2) * exp (-ζ / 2)) := by ring
      _ = _ := by rw [I_sq, hexp]; ring
  have hfactor (θ : ℝ) :
      (∏' j : ℕ, (1 + pairedTerm r θ ζ j)) =
      ∑' n : ℕ, a n * exp ((n : ℂ) * I * θ) := by
    simp_rw [pairedTerm_eq_euler]
    rw [← eulerQSeries_eq_tprod hq (z * exp ((θ : ℂ) * I))]
    exact tsum_congr (fun n => eulerQTerm_shift q z θ n)
  have hprod (θ : ℝ) :
      pairedProduct r θ ζ =
        (∑' n : ℕ, a n * exp ((n : ℂ) * I * θ)) *
          (∑' m : ℕ, a m * exp (-(m : ℂ) * I * θ)) := by
    rw [pairedProduct,
      (multipliable_one_add_of_summable (summable_norm_pairedTerm r θ hζ)).tprod_mul
        (multipliable_one_add_of_summable (summable_norm_pairedTerm r (-θ) hζ)),
      hfactor θ, hfactor (-θ)]
    simp only [ofReal_neg, mul_neg, neg_mul]
  have hdiag : durfeeAnalyticF (-(r : ℂ) ^ 2) q = ∑' n : ℕ, a n * a n := by
    rw [durfeeAnalyticF_eq_diagonal _ hq]
    exact tsum_congr (fun n => (eulerQTerm_mul_same_index q _ z z hz n).symm)
  have hsum : Summable fun n : ℕ => ‖a n‖ := summable_norm_eulerQTerm hq z
  simp_rw [hprod]
  rw [angular_integral_mul_tsum a a hsum hsum, ← hdiag, ← mul_assoc,
    inv_mul_cancel₀ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)), one_mul]

end DurfeeCCS.Step06
