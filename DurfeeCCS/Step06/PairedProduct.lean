module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The paired angular product and its absolutely convergent logarithmic expansion. -/

@[expose] public section

namespace DurfeeCCS.Step06

open Complex

/-- The perturbation of each factor in (2). Use θ or −θ for the two signs. -/
noncomputable def pairedTerm (r θ : ℝ) (ζ : ℂ) (j : ℕ) : ℂ :=
  r * I * Complex.exp (-((j : ℂ) + 1 / 2) * ζ + θ * I)

/-- The angular product in equation (2). -/
noncomputable def pairedProduct (r θ : ℝ) (ζ : ℂ) : ℂ :=
  ∏' j : ℕ, (1 + pairedTerm r θ ζ j) * (1 + pairedTerm r (-θ) ζ j)

theorem norm_pairedTerm (r θ : ℝ) (ζ : ℂ) (j : ℕ) :
    ‖pairedTerm r θ ζ j‖ = |r| * Real.exp (-ζ.re / 2) * (Real.exp (-ζ.re)) ^ j := by
  have he : (-((j : ℂ) + 1 / 2) * ζ + (θ : ℂ) * I).re = -(j : ℝ) * ζ.re - ζ.re / 2 := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hhalf]
    simp [Complex.mul_re]
    ring
  rw [pairedTerm, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_exp, he, sub_eq_add_neg, Real.exp_add]
  have hpow : Real.exp (-(j : ℝ) * ζ.re) = (Real.exp (-ζ.re)) ^ j := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow, ← neg_div]
  ac_rfl

theorem summable_norm_pairedTerm (r θ : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) :
    Summable (fun j : ℕ => ‖pairedTerm r θ ζ j‖) := by
  simp_rw [norm_pairedTerm]
  exact (summable_geometric_of_lt_one (Real.exp_nonneg _) ((Real.exp_lt_one_iff).2 (by linarith))).mul_left _

theorem multipliable_pairedProduct (r θ : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) :
    Multipliable (fun j : ℕ => (1 + pairedTerm r θ ζ j) * (1 + pairedTerm r (-θ) ζ j)) := by
  exact (multipliable_one_add_of_summable (summable_norm_pairedTerm r θ hζ)).mul
    (multipliable_one_add_of_summable (summable_norm_pairedTerm r (-θ) hζ))

private theorem norm_pairedTerm_le (r θ : ℝ) {ζ : ℂ} (j : ℕ)
    (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    ‖pairedTerm r θ ζ j‖ ≤ Real.exp (-ζ.re / 2) := by
  rw [norm_pairedTerm]
  have h₀ : 0 ≤ Real.exp (-ζ.re) := Real.exp_nonneg _
  have h₁ : Real.exp (-ζ.re) ≤ 1 := (Real.exp_le_one_iff).2 (by linarith)
  calc
    _ ≤ (1 * Real.exp (-ζ.re / 2)) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hr (Real.exp_nonneg _)) (pow_le_one₀ h₀ h₁)
        (pow_nonneg h₀ _) (by positivity)
    _ = _ := by simp

theorem norm_log_pairedTerm_le (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re)
    (j : ℕ) : ‖Complex.log (1 + pairedTerm r θ ζ j)‖ ≤
      Real.exp (-ζ.re / 2) * (Real.exp (-ζ.re)) ^ j / (1 - Real.exp (-ζ.re / 2)) := by
  let s := Real.exp (-ζ.re / 2)
  have hs : s < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let x := ‖pairedTerm r θ ζ j‖
  have hx : 0 ≤ x := norm_nonneg _
  have hj : x ≤ s := norm_pairedTerm_le r θ j hr hζ
  have hx₁ : 0 < 1 - x := sub_pos.mpr (hj.trans_lt hs)
  have hs₁ : 0 < 1 - s := sub_pos.mpr hs
  have hxbound : x ≤ s * (Real.exp (-ζ.re)) ^ j := by
    dsimp only [x]
    rw [norm_pairedTerm, ← one_mul s]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (Real.exp_nonneg _))
      (pow_nonneg (Real.exp_nonneg _) _)
  calc
    _ ≤ x ^ 2 * (1 - x)⁻¹ / 2 + x := norm_log_one_add_le (hj.trans_lt hs)
    _ ≤ x / (1 - x) := by
      apply (le_div_iff₀ hx₁).2
      field_simp
      nlinarith [sq_nonneg x]
    _ ≤ s * (Real.exp (-ζ.re)) ^ j / (1 - s) :=
      div_le_div₀ (by positivity) hxbound hs₁ (sub_le_sub_left hj _)

theorem summable_norm_log_pairedTerm (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    Summable (fun j : ℕ => ‖Complex.log (1 + pairedTerm r θ ζ j)‖) := by
  have hs := summable_geometric_of_lt_one (Real.exp_nonneg (-ζ.re))
    (Real.exp_lt_one_iff.mpr (by linarith : -ζ.re < 0))
  apply ((hs.mul_left (Real.exp (-ζ.re / 2))).mul_right (1 - Real.exp (-ζ.re / 2))⁻¹).of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (norm_nonneg _), ← div_eq_mul_inv]
  exact norm_log_pairedTerm_le r θ hr hζ j

theorem exp_sum_log_pairedProduct (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    Complex.exp (∑' j : ℕ,
      (Complex.log (1 + pairedTerm r θ ζ j) + Complex.log (1 + pairedTerm r (-θ) ζ j))) =
      pairedProduct r θ ζ := by
  have hn (t : ℝ) (j : ℕ) : 1 + pairedTerm r t ζ j ≠ 0 := by
    have hj := (norm_pairedTerm_le r t j hr hζ).trans_lt
      (Real.exp_lt_one_iff.mpr (by linarith) : Real.exp (-ζ.re / 2) < 1)
    intro he
    have he' : pairedTerm r t ζ j = -1 := eq_neg_of_add_eq_zero_right he
    simp [he'] at hj
  have hp (t : ℝ) : Summable (fun j => Complex.log (1 + pairedTerm r t ζ j)) :=
    (summable_norm_log_pairedTerm r t hr hζ).of_norm
  rw [(hp θ).tsum_add (hp (-θ)), Complex.exp_add,
    cexp_tsum_eq_tprod (hn θ) (hp θ), cexp_tsum_eq_tprod (hn (-θ)) (hp (-θ)), pairedProduct]
  symm
  exact (multipliable_one_add_of_summable (summable_norm_pairedTerm r θ hζ)).tprod_mul
    (multipliable_one_add_of_summable (summable_norm_pairedTerm r (-θ) hζ))

end DurfeeCCS.Step06
