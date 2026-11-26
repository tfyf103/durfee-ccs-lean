module

public import DurfeeCCS.Step08.NearOriginLaplace
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! Closing left semicircles for the Bromwich integral in (17). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step14

open Complex Filter MeasureTheory Set
open scoped Topology

/-- The contour integral on the left half of the circle centred at `u`, oriented
from the upper endpoint to the lower endpoint. -/
def bromwichLeftSemicircle (u x R : ℝ) (j : ℕ) : ℂ :=
  ∫ θ in (Real.pi / 2)..(Real.pi + Real.pi / 2),
    deriv (circleMap (u : ℂ) R) θ *
      (exp ((x : ℂ) * circleMap (u : ℂ) R θ) / circleMap (u : ℂ) R θ ^ j)

/-- The manuscript's arc length times the uniform kernel bound. -/
theorem norm_bromwichLeftSemicircle_le {u x R : ℝ}
    (hu : 0 ≤ u) (hx : 0 ≤ x) (hR : u < R) (j : ℕ) :
    ‖bromwichLeftSemicircle u x R j‖ ≤
      Real.pi * R * Real.exp (x * u) * ((R - u) ^ j)⁻¹ := by
  have hRp : 0 < R := hu.trans_lt hR
  have hinterval : Real.pi / 2 ≤ Real.pi + Real.pi / 2 := by linarith [Real.pi_pos]
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := Real.pi / 2) (b := Real.pi + Real.pi / 2)
      (C := R * (Real.exp (x * u) / (R - u) ^ j))
      (f := fun θ => deriv (circleMap (u : ℂ) R) θ *
        (exp ((x : ℂ) * circleMap (u : ℂ) R θ) / circleMap (u : ℂ) R θ ^ j))
      (by
        intro θ hθ
        rw [uIoc_of_le hinterval] at hθ
        let z := circleMap (u : ℂ) R θ
        have hzre : z.re ≤ u := by
          have hcos : Real.cos θ ≤ 0 :=
            Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1.le hθ.2
          change (circleMap (u : ℂ) R θ).re ≤ u
          rw [circleMap, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
            exp_ofReal_mul_I_re]
          simpa using mul_nonpos_of_nonneg_of_nonpos hRp.le hcos
        have hznorm : R - u ≤ ‖z‖ := by
          have hn := norm_sub_le z (u : ℂ)
          rw [show z - (u : ℂ) = circleMap 0 R θ by simp [z], norm_circleMap_zero,
            abs_of_pos hRp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] at hn
          linarith
        have hexp : ‖exp ((x : ℂ) * z)‖ ≤ Real.exp (x * u) := by
          rw [norm_exp, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hzre hx)
        simp only [norm_mul, deriv_circleMap, norm_circleMap_zero, norm_I, mul_one,
          abs_of_pos hRp]
        change R * ‖exp ((x : ℂ) * z) / z ^ j‖ ≤ _
        rw [norm_div, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (div_le_div₀ (Real.exp_pos _).le hexp (pow_pos (sub_pos.mpr hR) _)
            (pow_le_pow_left₀ (sub_nonneg.mpr hR.le) hznorm _)) hRp.le)
  calc
    _ ≤ R * (Real.exp (x * u) / (R - u) ^ j) *
        |Real.pi + Real.pi / 2 - Real.pi / 2| := h
    _ = _ := by
      rw [show Real.pi + Real.pi / 2 - Real.pi / 2 = Real.pi by ring,
        abs_of_pos Real.pi_pos, div_eq_mul_inv]
      ring

/-- With pole order at least two, the explicit bound tends to zero. -/
theorem tendsto_bromwichLeftSemicircle_bound_zero (u x : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun R : ℝ => Real.pi * R * Real.exp (x * u) * ((R - u) ^ j)⁻¹)
      atTop (𝓝 0) := by
  have hq : Tendsto (fun R : ℝ => (R - u)⁻¹) atTop (𝓝 0) := by
    simpa only [sub_eq_add_neg, Function.comp_def, id_eq] using
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-u) tendsto_id)
  have hp : Tendsto (fun R : ℝ => ((R - u)⁻¹) ^ (j - 1)) atTop (𝓝 0) := by
    convert hq.pow (j - 1) using 1
    rw [zero_pow (by omega : j - 1 ≠ 0)]
  have hlin : Tendsto (fun R : ℝ => 1 + u * (R - u)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hq.const_mul u)
  have hf : Tendsto (fun R : ℝ =>
      (Real.pi * Real.exp (x * u)) * (1 + u * (R - u)⁻¹) * ((R - u)⁻¹) ^ (j - 1))
      atTop (𝓝 0) := by
    simpa using (hlin.const_mul (Real.pi * Real.exp (x * u))).mul hp
  apply hf.congr'
  filter_upwards [eventually_gt_atTop u] with R hR
  have hz : R - u ≠ 0 := sub_ne_zero.mpr hR.ne'
  have hpow : ((R - u) ^ j)⁻¹ = ((R - u)⁻¹) ^ (j - 1) * (R - u)⁻¹ := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j), inv_pow]
  rw [hpow]
  field_simp
  ring

/-- The arc's own contribution vanishes in the limit. -/
theorem tendsto_bromwichLeftSemicircle_zero {u x : ℝ}
    (hu : 0 ≤ u) (hx : 0 ≤ x) {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun R : ℝ => bromwichLeftSemicircle u x R j) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    ((eventually_gt_atTop u).mono fun _ hR => norm_bromwichLeftSemicircle_le hu hx hR j)
    (tendsto_bromwichLeftSemicircle_bound_zero u x hj)

/-- The oriented arc joins the upper endpoint of the vertical segment to its
lower endpoint. -/
theorem bromwichLeftSemicircle_endpoints (u R : ℝ) :
    circleMap (u : ℂ) R (Real.pi / 2) = Step08.verticalPoint u R ∧
    circleMap (u : ℂ) R (Real.pi + Real.pi / 2) = Step08.verticalPoint u (-R) := by
  constructor
  · rw [circleMap_pi_div_two, Step08.verticalPoint]
  · rw [show Real.pi + Real.pi / 2 = -Real.pi / 2 + 2 * Real.pi by ring,
      periodic_circleMap (u : ℂ) R (-Real.pi / 2), circleMap_neg_pi_div_two,
      Step08.verticalPoint]
    simp [sub_eq_add_neg]

/-- The integral over the vertical segment followed by the closing arc tends
to the residue value of the closed contour. -/
theorem tendsto_bromwichClosedContour {u x : ℝ} (hu : 0 < u) (hx : 0 < x)
    {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun R : ℝ =>
      I * (∫ v in -R..R,
        exp ((x : ℂ) * Step08.verticalPoint u v) / Step08.verticalPoint u v ^ j) +
          bromwichLeftSemicircle u x R j)
      atTop (𝓝 (((2 * Real.pi : ℝ) : ℂ) * I *
        ((x : ℂ) ^ (j - 1) / (((j - 1 : ℕ).factorial : ℕ) : ℂ)))) := by
  let f : ℝ → ℂ := fun v => exp ((x : ℂ) * Step08.verticalPoint u v) /
    Step08.verticalPoint u v ^ j
  have hIntegrable : Integrable f := by
    apply ((Step08.integrable_vertical_inv_pow hu hj).norm.const_mul (Real.exp (x * u))).mono'
    · have hv : Continuous (Step08.verticalPoint u) := by
        unfold Step08.verticalPoint
        fun_prop
      exact ((continuous_const.mul hv).cexp.div (hv.pow _)
        (fun v => pow_ne_zero _ (Step08.verticalPoint_ne_zero hu v))).aestronglyMeasurable
    · exact Eventually.of_forall fun v => le_of_eq (by
        simp [f, div_eq_mul_inv, norm_inv, norm_pow, Complex.norm_exp,
          Complex.mul_re])
  have hTrunc : Tendsto (fun R : ℝ => ∫ v in -R..R, f v) atTop (𝓝 (∫ v, f v)) :=
    intervalIntegral_tendsto_integral hIntegrable tendsto_neg_atTop_atBot tendsto_id
  have hval : I * (∫ v, f v) = ((2 * Real.pi : ℝ) : ℂ) * I *
      ((x : ℂ) ^ (j - 1) / (((j - 1 : ℕ).factorial : ℕ) : ℂ)) := by
    have hb : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 from Real.two_pi_pos.ne')
    calc
      _ = ((2 * Real.pi : ℝ) : ℂ) * I *
          ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ v, f v) := by
        rw [mul_comm ((2 * Real.pi : ℝ) : ℂ) I, mul_assoc I,
          ← mul_assoc ((2 * Real.pi : ℝ) : ℂ),
          mul_inv_cancel₀ hb, one_mul]
      _ = _ := by rw [Step08.integral_vertical_kernel hu hx hj]
  simpa only [add_zero, hval] using
    (hTrunc.const_mul I).add (tendsto_bromwichLeftSemicircle_zero hu.le hx.le hj)

end DurfeeCCS.Step14
