module

public import DurfeeCCS.Step08.NearOriginDefs
public import DurfeeCCS.Step06.PairedAngle
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Trigonometric

/-! Angular Fourier averages for the first two terms of the near-origin model. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex Finset MeasureTheory DurfeeCCS.Step06

private def expCoeff (z : ℂ) (k : ℕ) : ℂ :=
  z^k / (k.factorial : ℂ)

private theorem summable_norm_expCoeff (z : ℂ) : Summable fun k => ‖expCoeff z k‖ := by
  simpa [expCoeff, norm_div, norm_pow, Complex.norm_natCast] using
    Real.summable_pow_div_factorial ‖z‖

private theorem exponential_fourier (z v : ℂ) :
    exp (z * exp v) = ∑' k, expCoeff z k * exp ((k : ℂ) * v) := by
  have he (w : ℂ) : exp w = ∑' k : ℕ, w^k / (k.factorial : ℂ) :=
    congrFun (Complex.exp_eq_exp_ℂ.trans NormedSpace.exp_eq_tsum_div) w
  rw [he (z * exp v)]
  apply tsum_congr
  intro k
  rw [exp_nat_mul, mul_pow, expCoeff]
  ring

private def twoShift (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 0
  | k+2 => a k

private theorem summable_norm_twoShift {a : ℕ → ℂ} (ha : Summable fun k => ‖a k‖) :
    Summable fun k => ‖twoShift a k‖ :=
  (summable_nat_add_iff 2).1 ha

private theorem tsum_twoShift {a : ℕ → ℂ} (ha : Summable fun k => ‖a k‖) {v : ℂ}
    (hv : ‖exp v‖ = 1) :
    (∑' k, twoShift a k * exp ((k : ℂ) * v)) =
      (∑' k, a k * exp ((k : ℂ) * v)) * exp (2 * v) := by
  let f k := twoShift a k * exp ((k : ℂ) * v)
  have hnorm k : ‖f k‖ = ‖twoShift a k‖ := by
    simp [f, exp_nat_mul, norm_pow, hv]
  have hf : Summable f := Summable.of_norm (by simp_rw [hnorm]; exact summable_norm_twoShift ha)
  change (∑' k, f k) = _
  rw [← hf.sum_add_tsum_nat_add 2, ← tsum_mul_right]
  have hzero : (∑ j ∈ Finset.range 2, f j) = 0 := by
    norm_num [Finset.sum_range_succ, f, twoShift]
  rw [hzero, zero_add]
  apply tsum_congr
  intro k
  change a k * exp (((k+2 : ℕ) : ℂ) * v) = _
  rw [Nat.cast_add, add_mul, Complex.exp_add]
  ring

private theorem tsum_twoShift_diag {a : ℕ → ℂ} (ha : Summable fun k => ‖a k‖) :
    (∑' k, twoShift a k * a k) = ∑' k, a k * a (k+2) := by
  let f k := twoShift a k * a k
  have hab := summable_mul_of_summable_norm (summable_norm_twoShift ha) ha
  have hf : Summable f := hab.comp_injective
    (i := fun k : ℕ => (k,k)) (fun _ _ h => congrArg Prod.fst h)
  change (∑' k, f k) = _
  rw [← hf.sum_add_tsum_nat_add 2]
  have hzero : (∑ j ∈ Finset.range 2, f j) = 0 := by
    norm_num [Finset.sum_range_succ, f, twoShift]
  rw [hzero, zero_add]
  rfl

private theorem cos_as_exp (θ : ℝ) :
    (Real.cos θ : ℂ) = (exp ((θ : ℂ) * I) + exp (-(θ : ℂ) * I)) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, neg_mul]

private theorem exp_two_mul_cos (z : ℂ) (θ : ℝ) :
    exp (2 * z * (Real.cos θ : ℂ)) =
      exp (z * exp ((θ : ℂ) * I)) * exp (z * exp (-(θ : ℂ) * I)) := by
  rw [cos_as_exp, ← Complex.exp_add]
  congr 1
  ring

private theorem angular_exp_cos (z : ℂ) :
    (∫ θ : ℝ in -Real.pi..Real.pi, exp (2 * z * (Real.cos θ : ℂ))) =
      (2 * Real.pi : ℂ) * ∑' k, expCoeff z k * expCoeff z k := by
  simp_rw [exp_two_mul_cos, exponential_fourier z, mul_comm (_ : ℂ) I]
  convert angular_integral_mul_tsum (expCoeff z) (expCoeff z)
    (summable_norm_expCoeff z) (summable_norm_expCoeff z) using 2
  ext θ
  congr 1 <;> apply tsum_congr <;> intro k <;> congr 2 <;> ring

private theorem angular_exp_cos_phase_pos (z : ℂ) :
    (∫ θ : ℝ in -Real.pi..Real.pi, exp (2 * z * (Real.cos θ : ℂ)) * exp ((2 : ℂ) * (θ : ℂ) * I)) =
      (2 * Real.pi : ℂ) * ∑' k, expCoeff z k * expCoeff z (k+2) := by
  let a := expCoeff z
  have ha := summable_norm_expCoeff z
  have hpoint (θ : ℝ) :
      exp (2 * z * (Real.cos θ : ℂ)) * exp ((2 : ℂ) * (θ : ℂ) * I) =
        (∑' k, twoShift a k * exp ((k : ℂ) * I * θ)) *
          (∑' k, a k * exp (-(k : ℂ) * I * θ)) := by
    have he (k : ℕ) : (k : ℂ) * I * θ = (k : ℂ) * ((θ : ℂ) * I) := by ring
    have he' (k : ℕ) : -(k : ℂ) * I * θ = (k : ℂ) * (-(θ : ℂ) * I) := by ring
    simp_rw [he, he']
    rw [tsum_twoShift ha (Complex.norm_exp_ofReal_mul_I θ), ← exponential_fourier z,
      ← exponential_fourier z, exp_two_mul_cos]
    ring
  simp_rw [hpoint]
  rw [angular_integral_mul_tsum _ _ (summable_norm_twoShift ha) ha, tsum_twoShift_diag ha]

private theorem angular_exp_cos_phase_neg (z : ℂ) :
    (∫ θ : ℝ in -Real.pi..Real.pi, exp (2 * z * (Real.cos θ : ℂ)) * exp (-(2 : ℂ) * (θ : ℂ) * I)) =
      (2 * Real.pi : ℂ) * ∑' k, expCoeff z k * expCoeff z (k+2) := by
  let a := expCoeff z
  have ha := summable_norm_expCoeff z
  have hpoint (θ : ℝ) :
      exp (2 * z * (Real.cos θ : ℂ)) * exp (-(2 : ℂ) * (θ : ℂ) * I) =
        (∑' k, a k * exp ((k : ℂ) * I * θ)) *
          (∑' k, twoShift a k * exp (-(k : ℂ) * I * θ)) := by
    have he (k : ℕ) : (k : ℂ) * I * θ = (k : ℂ) * ((θ : ℂ) * I) := by ring
    have he' (k : ℕ) : -(k : ℂ) * I * θ = (k : ℂ) * (-(θ : ℂ) * I) := by ring
    have hv : ‖exp (-(θ : ℂ) * I)‖ = 1 := by
      simpa using Complex.norm_exp_ofReal_mul_I (-θ)
    simp_rw [he, he']
    rw [tsum_twoShift ha hv, ← exponential_fourier z, ← exponential_fourier z,
      exp_two_mul_cos]
    ring
  simp_rw [hpoint]
  rw [angular_integral_mul_tsum _ _ ha (summable_norm_twoShift ha)]
  congr 1
  exact (tsum_congr (fun k => mul_comm (a k) (twoShift a k))).trans (tsum_twoShift_diag ha)

private theorem angular_exp_cos_weight (z : ℂ) :
    (∫ θ : ℝ in -Real.pi..Real.pi, exp (2 * z * (Real.cos θ : ℂ)) * (Real.cos (2*θ) : ℂ)) =
      (2 * Real.pi : ℂ) * ∑' k, expCoeff z k * expCoeff z (k+2) := by
  have hh (θ : ℝ) :
      exp (2 * z * (Real.cos θ : ℂ)) * (Real.cos (2*θ) : ℂ) =
      (exp (2 * z * (Real.cos θ : ℂ)) * exp ((2 : ℂ) * (θ : ℂ) * I) +
        exp (2 * z * (Real.cos θ : ℂ)) * exp (-(2 : ℂ) * (θ : ℂ) * I)) / 2 := by
    rw [cos_as_exp (2*θ)]
    push_cast
    ring
  simp_rw [hh]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add,
    angular_exp_cos_phase_pos, angular_exp_cos_phase_neg]
  · ring
  · exact (by fun_prop : Continuous (fun θ : ℝ =>
        exp (2 * z * (Real.cos θ : ℂ)) * exp ((2 : ℂ) * (θ : ℂ) * I))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun θ : ℝ =>
        exp (2 * z * (Real.cos θ : ℂ)) * exp (-(2 : ℂ) * (θ : ℂ) * I))).intervalIntegrable _ _

/-- Division by the full-circle length, with the convention on page 6. -/
def nearOriginAngleAverage (f : ℝ → ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ θ in -Real.pi..Real.pi, f θ

/-- The terms indexed by (d+1) in the average of (e^{L_0}-1). -/
def nearOriginAngularBaseTerm (r : ℝ) (ζ : ℂ) (d : ℕ) : ℂ :=
  (-((r : ℂ)^2))^(d+1) / (((d+1).factorial : ℂ)^2 * ζ^(2*(d+1)))

/-- The terms of the correction after extracting its factor (-r^4/2). -/
def nearOriginAngularCorrectionTerm (r : ℝ) (ζ : ℂ) (d : ℕ) : ℂ :=
  (-((r : ℂ)^2))^d / ((d.factorial : ℂ) * ((d+2).factorial : ℂ) * ζ^(2*d+3))

def nearOriginAngularModel (r : ℝ) (ζ : ℂ) : ℂ :=
  nearOriginAngleAverage fun θ =>
    exp (nearOriginMainLog r θ ζ) * (1 + nearOriginCorrection r θ ζ) - 1

private theorem circle_length_ne_zero : (2 * Real.pi : ℂ) ≠ 0 :=
  mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)

private theorem integral_one_over_circle :
    (∫ _ : ℝ in -Real.pi..Real.pi, (1 : ℂ)) = (2 * Real.pi : ℂ) := by
  simp [intervalIntegral.integral_const, Complex.real_smul, two_mul]

private theorem nearOrigin_main_log_factored (r θ : ℝ) (ζ : ℂ) :
    nearOriginMainLog r θ ζ = 2 * (I * (r : ℂ) / ζ) * (Real.cos θ : ℂ) := by
  unfold nearOriginMainLog
  ring

private theorem square_model_variable (r : ℝ) (ζ : ℂ) :
    (I * (r : ℂ) / ζ)^2 = -((r : ℂ)^2) / ζ^2 := by
  rw [div_pow, mul_pow, I_sq, neg_one_mul]

private theorem diagonal_expCoeff_eq (r : ℝ) (ζ : ℂ) (d : ℕ) :
    expCoeff (I * (r : ℂ) / ζ) (d+1) * expCoeff (I * (r : ℂ) / ζ) (d+1) =
      nearOriginAngularBaseTerm r ζ d := by
  unfold expCoeff nearOriginAngularBaseTerm
  rw [← pow_two, div_pow, ← pow_mul, mul_comm (d+1) 2,
    pow_mul (I * (r : ℂ) / ζ) 2 (d+1), square_model_variable, div_pow, ← pow_mul]
  ring

theorem nearOriginAngularBase_eq_series (r : ℝ) (ζ : ℂ) :
    nearOriginAngleAverage (fun θ => exp (nearOriginMainLog r θ ζ) - 1) =
      ∑' d, nearOriginAngularBaseTerm r ζ d := by
  let z := I * (r : ℂ) / ζ
  let g d := expCoeff z d * expCoeff z d
  have ha := summable_norm_expCoeff z
  have hs : Summable g := (summable_mul_of_summable_norm ha ha).comp_injective
    (i := fun k : ℕ => (k,k)) (fun _ _ h => congrArg Prod.fst h)
  have hg₀ : g 0 = 1 := by simp [g, expCoeff]
  unfold nearOriginAngleAverage
  simp_rw [nearOrigin_main_log_factored, ← show z = I * (r : ℂ) / ζ from rfl]
  rw [intervalIntegral.integral_sub, angular_exp_cos, integral_one_over_circle]
  · change (2 * Real.pi : ℂ)⁻¹ * ((2 * Real.pi : ℂ) * (∑' d, g d) -
        (2 * Real.pi : ℂ)) = _
    rw [hs.tsum_eq_zero_add, hg₀, mul_add, mul_one, add_sub_cancel_left, ← mul_assoc,
      inv_mul_cancel₀ circle_length_ne_zero, one_mul]
    exact tsum_congr (fun d => diagonal_expCoeff_eq r ζ d)
  · exact (by fun_prop : Continuous (fun θ : ℝ => exp (2 * z * (Real.cos θ : ℂ)))).intervalIntegrable _ _
  · exact intervalIntegrable_const

private theorem correction_expCoeff_eq (r : ℝ) {ζ : ℂ} (hζ : ζ ≠ 0) (d : ℕ) :
    ((r : ℂ)^2 / (2*ζ)) *
      (expCoeff (I * (r : ℂ) / ζ) d * expCoeff (I * (r : ℂ) / ζ) (d+2)) =
        (-((r : ℂ)^4) / 2) * nearOriginAngularCorrectionTerm r ζ d := by
  unfold expCoeff nearOriginAngularCorrectionTerm
  have hpow : (I * (r : ℂ) / ζ)^d * (I * (r : ℂ) / ζ)^(d+2) =
      ((I * (r : ℂ) / ζ)^2)^d * (I * (r : ℂ) / ζ)^2 := by
    rw [← pow_add, ← pow_mul, ← pow_add, show d+(d+2) = 2*d+2 by omega]
  calc
    _ = ((r : ℂ)^2 / (2*ζ)) *
        (((I * (r : ℂ) / ζ)^2)^d * (I * (r : ℂ) / ζ)^2 /
          ((d.factorial : ℂ) * ((d+2).factorial : ℂ))) := by rw [← hpow]; ring
    _ = _ := by
      rw [square_model_variable, div_pow, ← pow_mul,
        show 2*d+3 = 2*d + 2 + 1 by omega, pow_succ ζ (2*d+2), pow_add ζ (2*d) 2]
      field_simp

theorem nearOriginAngularCorrection_eq_series (r : ℝ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    nearOriginAngleAverage (fun θ => exp (nearOriginMainLog r θ ζ) * nearOriginCorrection r θ ζ) =
      (-((r : ℂ)^4) / 2) * ∑' d, nearOriginAngularCorrectionTerm r ζ d := by
  let z := I * (r : ℂ) / ζ
  let c := (r : ℂ)^2 / (2*ζ)
  have hpoint (θ : ℝ) :
      exp (nearOriginMainLog r θ ζ) * nearOriginCorrection r θ ζ =
        c * (exp (2 * z * (Real.cos θ : ℂ)) * (Real.cos (2*θ) : ℂ)) := by
    rw [nearOrigin_main_log_factored, nearOriginCorrection]
    unfold z c
    ring
  simp_rw [nearOriginAngleAverage, hpoint]
  rw [intervalIntegral.integral_const_mul, angular_exp_cos_weight]
  calc
    _ = c * (((2 * Real.pi : ℂ)⁻¹ * (2 * Real.pi : ℂ)) *
        ∑' d, expCoeff z d * expCoeff z (d+2)) := by ring
    _ = _ := by
      rw [inv_mul_cancel₀ circle_length_ne_zero, one_mul, ← tsum_mul_left, ← tsum_mul_left]
      exact tsum_congr (fun d => correction_expCoeff_eq r hζ d)

/-- Split the model into its base and correction angular averages. -/
theorem nearOriginAngularModel_eq_add (r : ℝ) (ζ : ℂ) :
    nearOriginAngularModel r ζ =
      nearOriginAngleAverage (fun θ => exp (nearOriginMainLog r θ ζ) - 1) +
        nearOriginAngleAverage (fun θ => exp (nearOriginMainLog r θ ζ) * nearOriginCorrection r θ ζ) := by
  have hpoint (θ : ℝ) :
      exp (nearOriginMainLog r θ ζ) * (1 + nearOriginCorrection r θ ζ) - 1 =
        (exp (nearOriginMainLog r θ ζ) - 1) +
          exp (nearOriginMainLog r θ ζ) * nearOriginCorrection r θ ζ := by ring
  have h₁ : IntervalIntegrable (fun θ : ℝ => exp (nearOriginMainLog r θ ζ) - 1) volume
      (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    unfold nearOriginMainLog
    fun_prop
  have h₂ : IntervalIntegrable
      (fun θ : ℝ => exp (nearOriginMainLog r θ ζ) * nearOriginCorrection r θ ζ) volume
      (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    unfold nearOriginMainLog nearOriginCorrection
    fun_prop
  simp_rw [nearOriginAngularModel, nearOriginAngleAverage, hpoint]
  rw [intervalIntegral.integral_add h₁ h₂, mul_add]

/-- The angular series on page 7, with the constant term subtracted. -/
theorem nearOriginAngularModel_eq_series (r : ℝ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    nearOriginAngularModel r ζ =
      (∑' d, nearOriginAngularBaseTerm r ζ d) -
        (r : ℂ)^4 / 2 * ∑' d, nearOriginAngularCorrectionTerm r ζ d := by
  rw [nearOriginAngularModel_eq_add, nearOriginAngularBase_eq_series, nearOriginAngularCorrection_eq_series r hζ]
  ring

end DurfeeCCS.Step08
