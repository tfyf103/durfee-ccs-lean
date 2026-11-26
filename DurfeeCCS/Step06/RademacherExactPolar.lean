module

public import DurfeeCCS.Step06.Rademacher
public import DurfeeCCS.Step08.NearOriginModelIntegral

/-! The completed vertical integral for the polar term of (14). -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step06

open Complex MeasureTheory
open DurfeeCCS.Step08

/-- The analytic polar kernel in the inverse cusp coordinate. -/
def rademacherPolarKernel (a b : ℝ) (w : ℂ) : ℂ :=
  exp ((a : ℂ) * w + (b : ℂ) / w) / w ^ 3

private def polarCoeff (b : ℝ) (j : ℕ) : ℂ :=
  (b : ℂ) ^ j / (j.factorial : ℂ)

private theorem summable_polarCoeff (b u : ℝ) :
    Summable (fun j : ℕ => ‖polarCoeff b j‖ / u ^ (j + 3 - 2)) := by
  have hs := (Real.summable_pow_div_factorial (|b| / u)).mul_left u⁻¹
  refine hs.congr fun j => ?_
  simp only [polarCoeff, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, div_pow, show j + 3 - 2 = j + 1 by omega]
  rw [pow_succ]
  ring

private theorem rademacherPolarKernel_eq_series (a b : ℝ) {w : ℂ} (hw : w ≠ 0) :
    rademacherPolarKernel a b w = exp ((a : ℂ) * w) *
      ∑' j : ℕ, polarCoeff b j / w ^ (j + 3) := by
  have he : exp ((b : ℂ) / w) = ∑' j : ℕ, ((b : ℂ) / w)^j / (j.factorial : ℂ) :=
    congrFun (Complex.exp_eq_exp_ℂ.trans NormedSpace.exp_eq_tsum_div) _
  rw [rademacherPolarKernel, exp_add, mul_div_assoc, div_eq_mul_inv (exp (_ / w)),
    he, ← tsum_mul_right]
  congr 1
  apply tsum_congr
  intro j
  rw [polarCoeff, div_pow, pow_add]
  field_simp [hw]

private theorem rademacherPolar_sum_eq_bessel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∑' j : ℕ, polarCoeff b j * ((a : ℂ) ^ (j + 2) / ((j + 2).factorial : ℂ))) =
      ((a / b : ℝ) : ℂ) * besselI 2 ((2 * Real.sqrt (a * b) : ℝ) : ℂ) := by
  have hs : ((Real.sqrt (a * b) : ℝ) : ℂ) ^ 2 = (a : ℂ) * (b : ℂ) := by
    exact_mod_cast Real.sq_sqrt (mul_nonneg ha.le hb.le)
  have hb₀ : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  rw [besselI, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [polarCoeff, besselITerm, show ((↑(2 * Real.sqrt (a * b) : ℝ) : ℂ) / 2) =
      ((Real.sqrt (a * b) : ℝ) : ℂ) by push_cast; ring,
    show 2 * j + 2 = 2 * (j + 1) by omega, pow_mul, hs, mul_pow, pow_succ, pow_succ,
    Complex.ofReal_div]
  field_simp [hb₀]
  ring

/-- Bromwich inversion of the polar kernel gives the modified Bessel function of order two.
The line can have any strictly positive real part. -/
theorem integral_rademacherPolarKernel {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun v : ℝ => rademacherPolarKernel a b (verticalPoint u v)) ∧
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ v : ℝ, rademacherPolarKernel a b (verticalPoint u v)) =
        ((a / b : ℝ) : ℂ) * besselI 2 ((2 * Real.sqrt (a * b) : ℝ) : ℂ) := by
  have h := integral_vertical_power_series (x := a) hu (polarCoeff b) (fun j => j + 3)
    (fun j => by omega) (summable_polarCoeff b u)
  simp_rw [← rademacherPolarKernel_eq_series a b (verticalPoint_ne_zero hu _),
    show ∀ j : ℕ, j + 3 - 1 = j + 2 by omega] at h
  exact ⟨h.1, (h.2 ha).trans (rademacherPolar_sum_eq_bessel ha hb)⟩

end DurfeeCCS.Step06
