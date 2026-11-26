module

public import DurfeeCCS.Step06.BesselIntegrals
public import DurfeeCCS.Step06.Branches
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Half-plane Laplace estimates for the modified Bessel function. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex Set Filter MeasureTheory DurfeeCCS.Step06
open scoped Topology

private theorem norm_exp_neg_mul_real (z : ℂ) (y : ℝ) :
    ‖Complex.exp (-z * (y : ℂ))‖ = Real.exp (-z.re * y) := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- Integrability of the Laplace density for each real exponent above `-1`. -/
theorem integrable_laplace_rpow {z : ℂ} (hz : 0 < z.re) {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (t ^ p : ℝ)) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-z.re * t)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (b := z.re) (p := 1) hp one_pos hz)
  refine h.mono' ?_ ?_
  · have hc : ContinuousOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (t ^ p : ℝ)) (Ioi 0) := by
      apply (show Continuous fun t : ℝ => Complex.exp (-z * (t : ℂ)) by fun_prop).continuousOn.mul
      apply Complex.continuous_ofReal.comp_continuousOn
      exact continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    rw [norm_mul, norm_exp_neg_mul_real, Complex.norm_of_nonneg (Real.rpow_nonneg (le_of_lt ht) _),
      mul_comm]

private theorem integrable_gaussian_sq (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2)) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-z.re * x ^ 2)) (Ioi 0) := by
    simpa only [Real.rpow_two] using integrableOn_rpow_mul_exp_neg_mul_sq hz (s := 2) (by norm_num)
  refine h.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  rw [norm_mul, norm_cexp_neg_mul_sq, norm_pow,
    Complex.norm_of_nonneg (le_of_lt hx)]

private theorem integral_gaussian_sq_halfline {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2)) =
      (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ) ^ 2)) / (2 * z) := by
  let f (x : ℝ) := (x : ℂ) * Complex.exp (-z * (x : ℂ) ^ 2)
  let h (x : ℝ) := Complex.exp (-z * (x : ℂ) ^ 2)
  let j (x : ℝ) := (x : ℂ) ^ 2 * h x
  have hf (x : ℝ) : HasDerivAt f (h x - (2 * z) * j x) x := by
    have hd := ((hasDerivAt_id (x : ℂ)).mul (((hasDerivAt_pow 2 (x : ℂ)).const_mul (-z)).cexp)).comp_ofReal
    change HasDerivAt f _ x at hd
    convert hd using 1
    dsimp [h, j, id]
    norm_num
    ring
  have hi : IntegrableOn (fun x => h x - (2 * z) * j x) (Ioi 0) :=
    (integrable_cexp_neg_mul_sq hz).integrableOn.sub ((integrable_gaussian_sq z hz).const_mul _)
  have ht : Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun x _ => hf x) hi
      (integrable_mul_cexp_neg_mul_sq hz).integrableOn
  have hz₀ : z ≠ 0 := by intro h'; simp [h'] at hz
  apply (eq_div_iff (mul_ne_zero two_ne_zero hz₀)).mpr
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hf x) hi ht
  rw [show f 0 = 0 by simp [f], sub_zero, integral_sub
    (integrable_cexp_neg_mul_sq hz).integrableOn ((integrable_gaussian_sq z hz).const_mul _),
    integral_const_mul, sub_eq_zero] at he
  exact mul_comm _ _ |>.trans he.symm

/-- Complex Laplace transform of `sqrt(t)`, obtained from a Gaussian moment. -/
theorem integral_laplace_sqrt {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-z * (t : ℂ)) * (Real.sqrt t : ℂ)) =
      Complex.sqrt ((Real.pi : ℂ) / z) / (2 * z) := by
  rw [← integral_comp_rpow_Ioi_of_pos (p := 2) (by norm_num)]
  calc
    _ = ∫ x : ℝ in Ioi 0, (2 : ℂ) * ((x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
        Real.sqrt_sq (le_of_lt hx), Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_pow]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_gaussian_sq_halfline hz, integral_gaussian_complex_Ioi hz,
        Complex.sqrt]
      ring

/-- The inverse square-root Laplace moment used in the central saddle model. -/
theorem integral_laplace_inv_sqrt {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-z * (t : ℂ)) / (Real.sqrt t : ℂ)) =
      Complex.sqrt ((Real.pi : ℂ) / z) := by
  rw [← integral_comp_rpow_Ioi_of_pos (p := 2) (by norm_num)]
  calc
    _ = ∫ x : ℝ in Ioi 0, (2 : ℂ) * Complex.exp (-z * (x : ℂ) ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx₀ : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < x from hx))
      simp only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
        Real.sqrt_sq (le_of_lt hx), Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_pow]
      field_simp
    _ = _ := by
      rw [integral_const_mul, integral_gaussian_complex_Ioi hz, Complex.sqrt]
      ring

theorem sqrt_ofReal_mul (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    Complex.sqrt ((a : ℂ) * z) = (Real.sqrt a : ℂ) * Complex.sqrt z := by
  have harg : (a : ℂ).arg + z.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ha, zero_add]
    exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  simp only [Complex.sqrt, Complex.mul_cpow harg]
  rw [show (2 : ℂ)⁻¹ = (((1 / 2 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_cpow ha,
    ← Real.sqrt_eq_rpow]

theorem sqrt_div_right_half_plane (a : ℝ) (ha : 0 ≤ a) {z : ℂ} (hz : 0 < z.re) :
    Complex.sqrt ((a : ℂ) / z) = (Real.sqrt a : ℂ) / Complex.sqrt z := by
  rw [div_eq_mul_inv, sqrt_ofReal_mul _ ha, Complex.sqrt, Complex.inv_cpow]
  · rfl
  · exact ne_of_lt (Complex.arg_lt_pi_iff.mpr (Or.inl hz.le))

/-- The infinite-interval identity in (34), on the open right half-plane. -/
theorem besselI_one_laplace_model {z : ℂ} (hz : 0 < z.re) :
    (z * (Real.sqrt 2 : ℂ) / (Real.pi : ℂ)) *
      (∫ y : ℝ in Ioi 0, Complex.exp (-z * (y : ℂ)) * (Real.sqrt y : ℂ)) =
      1 / Complex.sqrt (2 * (Real.pi : ℂ) * z) := by
  have hz₀ : z ≠ 0 := by intro h; simp [h] at hz
  have hs : Complex.sqrt z ≠ 0 := by
    intro h
    apply hz₀
    rw [← principalSqrt_sq z, h, zero_pow (by decide : 2 ≠ 0)]
  have hp₀ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h₂ : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num), Complex.ofReal_ofNat]
  have hπ : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [integral_laplace_sqrt hz, sqrt_div_right_half_plane _ Real.pi_pos.le hz,
    show (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ) : ℂ)) by push_cast; rfl,
    sqrt_ofReal_mul _ (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Complex.ofReal_mul]
  field_simp
  ring_nf
  rw [h₂, hπ]
  ring

theorem integral_laplace_rpow_real {a p : ℝ} (ha : 0 < a) (hp : -1 < p) :
    (∫ y : ℝ in Ioi 0, Real.exp (-a * y) * y ^ p) = Real.Gamma (p + 1) / a ^ (p + 1) := by
  convert (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p + 1) (by linarith) ha) using 1
  · simp only [add_sub_cancel_right]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    ring
  · rw [one_div, Real.inv_rpow ha.le, div_eq_mul_inv, mul_comm]

/-- Equation (34), the shifted Poisson integral for order one. -/
theorem besselI_one_laplace_finite (z : ℂ) :
    besselI 1 z = z * Complex.exp z * (Real.sqrt 2 : ℂ) / (Real.pi : ℂ) *
      ∫ y in (0 : ℝ)..2, Complex.exp (-z * (y : ℂ)) *
        (Real.sqrt y : ℂ) * (Real.sqrt (1 - y / 2) : ℂ) := by
  rw [besselI_one_integral]
  have hsub : (∫ y in (0 : ℝ)..2, Complex.exp (z * ((1 - y : ℝ) : ℂ)) *
      (Real.sqrt (1 - (1 - y) ^ 2) : ℂ)) =
      ∫ t in (-1 : ℝ)..1, Complex.exp (z * (t : ℂ)) * (Real.sqrt (1 - t ^ 2) : ℂ) := by
    simpa only [show (1 - 2 : ℝ) = -1 by norm_num, sub_zero] using
      (intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ)) (b := 2) (fun x : ℝ => Complex.exp (z * (x : ℂ)) *
          (Real.sqrt (1 - x ^ 2) : ℂ)) 1)
  rw [← hsub]
  have he (y : ℝ) (hy : y ∈ uIcc (0 : ℝ) 2) :
        Complex.exp (z * ((1 - y : ℝ) : ℂ)) * (Real.sqrt (1 - (1 - y) ^ 2) : ℂ) =
          (Complex.exp z * (Real.sqrt 2 : ℂ)) *
            (Complex.exp (-z * (y : ℂ)) * (Real.sqrt y : ℂ) * (Real.sqrt (1 - y / 2) : ℂ)) := by
    have hy' : 0 ≤ y := by
      rw [uIcc_of_le (by norm_num)] at hy
      exact hy.1
    rw [show 1 - (1 - y) ^ 2 = 2 * y * (1 - y / 2) by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * y), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
      mul_sub, mul_one, sub_eq_add_neg, Complex.exp_add, ← neg_mul]
    ring
  rw [intervalIntegral.integral_congr he, intervalIntegral.integral_const_mul]
  ring

private theorem sqrt_one_sub_half_error {y : ℝ} (hy : 0 ≤ y) :
    |Real.sqrt (1 - y / 2) - 1| ≤ y / 2 := by
  have hle : Real.sqrt (1 - y / 2) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (by linarith : 1 - y / 2 ≤ 1)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  by_cases hy' : y / 2 ≤ 1
  · have h₀ : 0 ≤ 1 - y / 2 := by linarith
    have h₁ : (1 - y / 2) ^ 2 ≤ 1 - y / 2 := by nlinarith [mul_nonneg h₀ (show 0 ≤ y / 2 by positivity)]
    linarith [Real.le_sqrt_of_sq_le h₁]
  · linarith [Real.sqrt_nonneg (1 - y / 2)]

private theorem besselI_one_laplace_Ioi (z : ℂ) :
    besselI 1 z = z * Complex.exp z * (Real.sqrt 2 : ℂ) / (Real.pi : ℂ) *
      ∫ y : ℝ in Ioi 0, Complex.exp (-z * (y : ℂ)) *
        (Real.sqrt y : ℂ) * (Real.sqrt (1 - y / 2) : ℂ) := by
  rw [besselI_one_laplace_finite, intervalIntegral.integral_of_le (by norm_num)]
  congr 1
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ h => h.1) ?_
  intro y hy
  have h : 2 < y := by
    by_contra! h
    exact hy.2 ⟨hy.1, h⟩
  rw [Real.sqrt_eq_zero_of_nonpos (show 1 - y / 2 ≤ 0 by linarith),
    Complex.ofReal_zero, mul_zero]

theorem gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

theorem gamma_five_halves : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    gamma_three_halves]
  ring

theorem real_laplace_moment_integrable {a p : ℝ} (ha : 0 < a) (hp : -1 < p) :
    IntegrableOn (fun y : ℝ => Real.exp (-a * y) * y ^ p) (Ioi 0) := by
  simpa only [Real.rpow_one, mul_comm] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (b := a) (p := 1) hp one_pos ha

/-- The large-real-part bound following from (34). -/
theorem norm_besselI_one_le_laplace {z : ℂ} (hz : 0 < z.re) :
    ‖besselI 1 z‖ ≤ ‖z‖ * Real.exp z.re /
      (Real.sqrt (2 * Real.pi) * z.re ^ (3 / 2 : ℝ)) := by
  let f (y : ℝ) := Complex.exp (-z * (y : ℂ)) * (Real.sqrt y : ℂ) *
    (Real.sqrt (1 - y / 2) : ℂ)
  let g (y : ℝ) := Real.exp (-z.re * y) * y ^ (1 / 2 : ℝ)
  have hi : IntegrableOn g (Ioi 0) := real_laplace_moment_integrable hz (by norm_num)
  have hnorm : ‖∫ y : ℝ in Ioi 0, f y‖ ≤ ∫ y : ℝ in Ioi 0, g y := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
    simp only [f, g, norm_mul, norm_exp_neg_mul_real,
      Complex.norm_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_eq_rpow]
    have h : Real.sqrt (1 - y / 2) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (show 1 - y / 2 ≤ 1 by linarith [hy.out])
    exact mul_le_of_le_one_right (by positivity) h
  have hγ : (∫ y : ℝ in Ioi 0, g y) = Real.sqrt Real.pi / 2 / z.re ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, integral_laplace_rpow_real hz (by norm_num),
      show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, gamma_three_halves]
  rw [besselI_one_laplace_Ioi, norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_exp,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_of_nonneg Real.pi_pos.le]
  apply (mul_le_mul_of_nonneg_left (hnorm.trans_eq hγ) (by positivity)).trans_eq
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h₁ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h₂ := Real.sq_sqrt Real.pi_pos.le
  field_simp
  ring_nf
  rw [h₁, h₂]
  ring

/-- The Poisson integral bound used when the real part of the Bessel argument is small. -/
theorem norm_besselI_one_le_half_mul_exp {z : ℂ} (hz : 0 ≤ z.re) :
    ‖besselI 1 z‖ ≤ ‖z‖ * Real.exp z.re / 2 := by
  let f (x : ℝ) := Complex.exp (z * (x : ℂ)) * (Real.sqrt (1 - x ^ 2) : ℂ)
  let b (x : ℝ) := Real.exp z.re * Real.sqrt (1 - x ^ 2)
  have hi : IntervalIntegrable b volume (-1) 1 :=
    (show Continuous b by dsimp [b]; fun_prop).intervalIntegrable _ _
  have hbound : ‖∫ x in (-1 : ℝ)..1, f x‖ ≤ ∫ x in (-1 : ℝ)..1, b x := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) (Eventually.of_forall ?_) hi
    intro x hx
    simp only [f, b, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_of_le_one_right hz hx.2)
  have hb : (∫ x in (-1 : ℝ)..1, b x) = Real.exp z.re * (Real.pi / 2) := by
    dsimp [b]
    rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
  have ha := mul_le_mul_of_nonneg_left (hbound.trans_eq hb)
    (show 0 ≤ ‖z‖ / Real.pi by positivity)
  calc
    _ = (‖z‖ / Real.pi) * ‖∫ x in (-1 : ℝ)..1, f x‖ := by
      rw [besselI_one_integral, norm_mul, norm_div, Complex.norm_of_nonneg Real.pi_pos.le]
    _ ≤ _ := ha
    _ = _ := by field_simp

/-- Equation (35), with `‖z‖ / sqrt(2π)` written as a single prefactor. -/
theorem besselI_one_half_plane_error_scaled {z : ℂ} (hz : 0 < z.re) :
    ‖besselI 1 z - Complex.exp z / Complex.sqrt (2 * (Real.pi : ℂ) * z)‖ ≤
      (3 * ‖z‖ * Real.exp z.re) / (4 * Real.sqrt (2 * Real.pi) * z.re ^ (5 / 2 : ℝ)) := by
  let f (y : ℝ) := Complex.exp (-z * (y : ℂ)) * (Real.sqrt y : ℂ)
  let w (y : ℝ) := (Real.sqrt (1 - y / 2) : ℂ)
  let M (y : ℝ) := (1 / 2 : ℝ) * (Real.exp (-z.re * y) * y ^ (3 / 2 : ℝ))
  have hfi : IntegrableOn f (Ioi 0) := by
    simpa only [f, Real.sqrt_eq_rpow] using integrable_laplace_rpow hz (p := 1 / 2) (by norm_num)
  have hM : IntegrableOn M (Ioi 0) :=
    (real_laplace_moment_integrable hz (p := 3 / 2) (by norm_num)).const_mul _
  have hb : ∀ᵐ y ∂volume.restrict (Ioi (0 : ℝ)), ‖f y * (w y - 1)‖ ≤ M y := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
    have hy' : 0 < y := hy
    calc
      _ = (Real.exp (-z.re * y) * Real.sqrt y) * |Real.sqrt (1 - y / 2) - 1| := by
        simp only [f, w, norm_mul, norm_exp_neg_mul_real,
          Complex.norm_of_nonneg (Real.sqrt_nonneg _), ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (Real.exp (-z.re * y) * Real.sqrt y) * (y / 2) := by
        gcongr
        exact sqrt_one_sub_half_error hy'.le
      _ = M y := by
        dsimp only [M]
        rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hy',
          Real.rpow_one, ← Real.sqrt_eq_rpow]
        ring
  have he : IntegrableOn (fun y => f y * (w y - 1)) (Ioi 0) := by
    apply hM.mono' (Continuous.aestronglyMeasurable (by dsimp [f, w]; fun_prop)) hb
  have hfw : IntegrableOn (fun y => f y * w y) (Ioi 0) := by
    convert he.add hfi using 1
    ext y
    change f y * w y = f y * (w y - 1) + f y
    ring
  have hnorm := norm_integral_le_of_norm_le hM hb
  have hMval : (∫ y : ℝ in Ioi 0, M y) = (3 * Real.sqrt Real.pi / 8) / z.re ^ (5 / 2 : ℝ) := by
    dsimp only [M]
    rw [integral_const_mul, integral_laplace_rpow_real hz (by norm_num),
      show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num, gamma_five_halves]
    ring
  have hmain : Complex.exp z / Complex.sqrt (2 * (Real.pi : ℂ) * z) =
      (z * Complex.exp z * (Real.sqrt 2 : ℂ) / (Real.pi : ℂ)) * ∫ y : ℝ in Ioi 0, f y := by
    rw [div_eq_mul_inv, ← one_div (Complex.sqrt _), ← besselI_one_laplace_model hz]
    change _ * (_ * ∫ y : ℝ in Ioi 0, f y) = _
    ring
  rw [besselI_one_laplace_Ioi, hmain]
  change ‖_ * (∫ y : ℝ in Ioi 0, f y * w y) - _ * (∫ y : ℝ in Ioi 0, f y)‖ ≤ _
  rw [← mul_sub, ← integral_sub hfw hfi]
  simp_rw [← mul_sub_one]
  rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_of_nonneg
    (Real.sqrt_nonneg _), Complex.norm_of_nonneg Real.pi_pos.le]
  apply (mul_le_mul_of_nonneg_left (hnorm.trans_eq hMval) (by positivity)).trans_eq
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h₁ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h₂ := Real.sq_sqrt Real.pi_pos.le
  field_simp
  ring_nf
  rw [h₁, h₂]
  ring

/-- Equation (35) in the normalization displayed in the manuscript. -/
theorem besselI_one_half_plane_error {z : ℂ} (hz : 0 < z.re) :
    ‖besselI 1 z - Complex.exp z / Complex.sqrt (2 * (Real.pi : ℂ) * z)‖ ≤
      (Real.exp z.re / Real.sqrt (2 * Real.pi * ‖z‖)) *
      (3 * ‖z‖ ^ (3 / 2 : ℝ) / (4 * z.re ^ (5 / 2 : ℝ))) := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr (fun h => by simp [h] at hz)
  have hs := Real.sqrt_pos.mpr hz'
  refine (besselI_one_half_plane_error_scaled hz).trans_eq ?_
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi),
    show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hz', Real.rpow_one, ← Real.sqrt_eq_rpow]
  field_simp


end DurfeeCCS.Step08
