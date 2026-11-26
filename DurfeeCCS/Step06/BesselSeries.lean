module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic

/-! The entire Bessel series in (9), at natural orders. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step06

open Nat FormalMultilinearSeries

/-- The `k`th term of the modified Bessel series of natural order `ν`. -/
def besselITerm (ν k : ℕ) (z : ℂ) : ℂ :=
  (z / 2) ^ (2 * k + ν) / ((k.factorial : ℂ) * ((k + ν).factorial : ℂ))

/-- The `k`th term of the ordinary Bessel series of natural order `ν`. -/
def besselJTerm (ν k : ℕ) (z : ℂ) : ℂ := (-1 : ℂ) ^ k * besselITerm ν k z

/-- The modified Bessel function of the first kind of natural order. -/
def besselI (ν : ℕ) (z : ℂ) : ℂ := ∑' k, besselITerm ν k z

/-- The ordinary Bessel function of the first kind of natural order. -/
def besselJ (ν : ℕ) (z : ℂ) : ℂ := ∑' k, besselJTerm ν k z

/-- The scalar coefficients after factoring out the leading power. -/
def besselAuxCoeff (ν k : ℕ) : ℂ :=
  1 / ((k.factorial : ℂ) * ((k + ν).factorial : ℂ))

/-- The scalar power series in the squared argument of the Bessel functions. -/
def besselAuxSeries (ν : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (besselAuxCoeff ν)

private theorem auxSummableNorm (ν : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Summable (fun k => ‖besselAuxCoeff ν k‖ * r ^ k) := by
  apply (Real.summable_pow_div_factorial r).of_nonneg_of_le (fun _ => by positivity)
  intro k
  simp only [besselAuxCoeff, norm_div, norm_one, norm_mul, Complex.norm_natCast]
  rw [mul_comm, mul_one_div]
  exact div_le_div_of_nonneg_left (pow_nonneg hr _) (by positivity)
    (le_mul_of_one_le_right (by positivity) (by exact_mod_cast factorial_pos (k + ν)))

theorem besselAuxSeries_radius (ν : ℕ) : (besselAuxSeries ν).radius = ⊤ := by
  apply top_unique
  apply ENNReal.le_of_forall_nnreal_lt
  intro r _
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  simpa [besselAuxSeries] using auxSummableNorm ν (r : ℝ) r.coe_nonneg

private theorem besselITerm_aux (ν k : ℕ) (z : ℂ) :
    besselITerm ν k z = (z / 2) ^ ν * (((z / 2) ^ 2) ^ k * besselAuxCoeff ν k) := by
  rw [besselITerm, besselAuxCoeff, pow_add, pow_mul]
  ring

private theorem besselJTerm_aux (ν k : ℕ) (z : ℂ) :
    besselJTerm ν k z = (z / 2) ^ ν * ((- (z / 2) ^ 2) ^ k * besselAuxCoeff ν k) := by
  rw [besselJTerm, besselITerm_aux, neg_pow ((z / 2) ^ 2)]
  rw [mul_left_comm ((-1 : ℂ) ^ k), ← mul_assoc ((-1 : ℂ) ^ k)]

private theorem auxSummable (ν : ℕ) (w : ℂ) :
    Summable fun k => w ^ k * besselAuxCoeff ν k := by
  apply Summable.of_norm
  simpa [norm_mul, norm_pow, mul_comm] using auxSummableNorm ν ‖w‖ (norm_nonneg w)

theorem summable_norm_besselITerm (ν : ℕ) (z : ℂ) :
    Summable (fun k => ‖besselITerm ν k z‖) := by
  simp only [besselITerm_aux, norm_mul, norm_pow]
  simpa only [mul_comm ((‖z / 2‖ ^ 2) ^ _)] using
    (auxSummableNorm ν (‖z / 2‖ ^ 2) (by positivity)).mul_left (‖z / 2‖ ^ ν)

theorem summable_besselITerm (ν : ℕ) (z : ℂ) : Summable (fun k => besselITerm ν k z) :=
  ((auxSummable ν ((z / 2) ^ 2)).mul_left ((z / 2) ^ ν)).congr
    (fun k => (besselITerm_aux ν k z).symm)

theorem summable_besselJTerm (ν : ℕ) (z : ℂ) : Summable (fun k => besselJTerm ν k z) :=
  ((auxSummable ν (- (z / 2) ^ 2)).mul_left ((z / 2) ^ ν)).congr
    (fun k => (besselJTerm_aux ν k z).symm)

private theorem aux_tsum (ν : ℕ) (w : ℂ) :
    (besselAuxSeries ν).sum w = ∑' k, w ^ k * besselAuxCoeff ν k := by
  rw [besselAuxSeries, ← ofScalarsSum, ofScalars_sum_eq]
  exact tsum_congr (fun k => by simp [smul_eq_mul, mul_comm])

theorem besselI_eq_aux (ν : ℕ) (z : ℂ) :
    besselI ν z = (z / 2) ^ ν * (besselAuxSeries ν).sum ((z / 2) ^ 2) := by
  simp only [besselI, aux_tsum, besselITerm_aux, tsum_mul_left]

theorem besselJ_eq_aux (ν : ℕ) (z : ℂ) :
    besselJ ν z = (z / 2) ^ ν * (besselAuxSeries ν).sum (- (z / 2) ^ 2) := by
  simp only [besselJ, aux_tsum, besselJTerm_aux, tsum_mul_left]

@[fun_prop]
theorem analyticAt_besselAuxSeries (ν : ℕ) (z : ℂ) :
    AnalyticAt ℂ (besselAuxSeries ν).sum z :=
  (besselAuxSeries ν).analyticOnNhd z (by simp [besselAuxSeries_radius])

theorem analyticAt_besselI (ν : ℕ) (z : ℂ) : AnalyticAt ℂ (besselI ν) z := by
  change AnalyticAt ℂ (fun w => besselI ν w) z
  simp_rw [besselI_eq_aux]
  fun_prop

theorem analyticAt_besselJ (ν : ℕ) (z : ℂ) : AnalyticAt ℂ (besselJ ν) z := by
  change AnalyticAt ℂ (fun w => besselJ ν w) z
  simp_rw [besselJ_eq_aux]
  fun_prop

/-- Quarter-turning the argument relates the two Bessel series. -/
theorem besselI_mul_I (ν : ℕ) (z : ℂ) :
    besselI ν (Complex.I * z) = Complex.I ^ ν * besselJ ν z := by
  rw [besselI, besselJ, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [besselJTerm, besselITerm, besselITerm, mul_div_assoc, mul_pow, pow_add Complex.I,
    pow_mul Complex.I, Complex.I_sq]
  ring

end DurfeeCCS.Step06
