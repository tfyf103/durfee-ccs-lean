module

public import DurfeeCCS.Step06.GeneratingAnalytic
public import DurfeeCCS.Step06.ThetaProduct

/-! The constant Laurent coefficient of a product of Euler series. -/

@[expose] public section

namespace DurfeeCCS.Step06

/-- The coefficient of degree d in the Euler expansion with argument z times t. -/
noncomputable def eulerQTerm (q z : ℂ) (d : ℕ) : ℂ :=
  z ^ d * q ^ d.choose 2 / qPochhammer q q d

/-- The unilateral Euler expansion in the notation of the Durfee generating function. -/
theorem eulerQSeries_eq_tprod {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) :
    (∑' d : ℕ, eulerQTerm q z d) = ∏' j : ℕ, (1 + z * q ^ j) := by
  simpa only [eulerQTerm, qPochhammer_self_eq_prod, qFactorial] using
    qProductSeries_eq_tprod hq z

/-- Absolute convergence of the unilateral Euler series for every complex argument. -/
theorem summable_norm_eulerQTerm {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) :
    Summable fun d : ℕ => ‖eulerQTerm q z d‖ := by
  simpa only [eulerQTerm, qPochhammer_self_eq_prod, qFactorial] using
    qProductSeries_summable_norm hq z

/-- The two Euler expansions may be multiplied as an absolutely convergent double sum. -/
theorem eulerQSeries_mul {q : ℂ} (hq : ‖q‖ < 1) (z w : ℂ) :
    (∑' n : ℕ, eulerQTerm q z n) * (∑' m : ℕ, eulerQTerm q w m) =
      ∑' nm : ℕ × ℕ, eulerQTerm q z nm.1 * eulerQTerm q w nm.2 :=
  tsum_mul_tsum_of_summable_norm (summable_norm_eulerQTerm hq z) (summable_norm_eulerQTerm hq w)

private theorem twice_choose_two_add (d : ℕ) : d.choose 2 + d.choose 2 + d = d * d := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [show d.succ.choose 2 = d.choose 1 + d.choose 2 from Nat.choose_succ_succ d 1,
      Nat.choose_one_right]
    nlinarith

/-- Matching exponents in the two Euler factors gives the Durfee-square summand. -/
theorem eulerQTerm_mul_same_index (q x z w : ℂ) (hzw : z * w = x * q) (d : ℕ) :
    eulerQTerm q z d * eulerQTerm q w d =
      q ^ (d * d) * x ^ d * (qPochhammer q q d)⁻¹ ^ 2 := by
  simp only [eulerQTerm, div_eq_mul_inv, pow_two ((qPochhammer q q d)⁻¹)]
  calc
    _ = (z ^ d * w ^ d) * (q ^ d.choose 2 * q ^ d.choose 2) *
          ((qPochhammer q q d)⁻¹ * (qPochhammer q q d)⁻¹) := by ac_rfl
    _ = _ := by
      rw [← mul_pow z w d, hzw, mul_pow x q d, ← pow_add q (d.choose 2) (d.choose 2),
        ← twice_choose_two_add d, pow_add q (d.choose 2 + d.choose 2) d]
      ring

/-- The terms of degree zero in the product of the Euler series in t and t⁻¹. -/
noncomputable def eulerConstantTermSummand (q z w : ℂ) (nm : ℕ × ℕ) : ℂ :=
  if nm.1 = nm.2 then eulerQTerm q z nm.1 * eulerQTerm q w nm.2 else 0

/-- The constant Laurent coefficient of the product of the Euler series. -/
noncomputable def eulerConstantTerm (q z w : ℂ) : ℂ :=
  ∑' nm : ℕ × ℕ, eulerConstantTermSummand q z w nm

private theorem hasSum_eulerConstantTerm {q : ℂ} (hq : ‖q‖ < 1)
    (x z w : ℂ) (hzw : z * w = x * q) :
    HasSum (eulerConstantTermSummand q z w) (durfeeAnalyticF x q) := by
  let diag : ℕ → ℕ × ℕ := fun n => (n, n)
  have hinj : Function.Injective diag := fun _ _ h => congrArg Prod.fst h
  have hz (nm : ℕ × ℕ) (hnm : nm ∉ Set.range diag) : eulerConstantTermSummand q z w nm = 0 := by
    have hne : nm.1 ≠ nm.2 := fun he => hnm ⟨nm.1, Prod.ext rfl he⟩
    simp [eulerConstantTermSummand, hne]
  apply (hinj.hasSum_iff hz).mp
  rw [durfeeAnalyticF_eq_diagonal x hq]
  refine (summable_norm_durfeeAnalyticDiagonal x hq).of_norm.hasSum.congr_fun (fun d => ?_)
  simp [diag, Function.comp_apply, eulerConstantTermSummand, eulerQTerm_mul_same_index q x z w hzw]

/-- The constant-term identity for the two Euler products on the open q-disc. -/
theorem durfeeAnalyticF_eq_eulerConstantTerm (x z : ℂ) {q : ℂ} (hq : ‖q‖ < 1)
    (hz : z ≠ 0) : durfeeAnalyticF x q = eulerConstantTerm q z (x * q / z) := by
  apply (hasSum_eulerConstantTerm hq x z (x * q / z) ?_).tsum_eq.symm
  field_simp

end DurfeeCCS.Step06
