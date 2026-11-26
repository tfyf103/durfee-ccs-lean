module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The scalar integrals used in the Bessel model. Fourier inversion avoids
approximating the closing contour. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set Filter
open scoped FourierTransform Topology

def verticalPoint (u v : ℝ) : ℂ := (u : ℂ) + (v : ℂ) * I

@[simp] theorem verticalPoint_re (u v : ℝ) : (verticalPoint u v).re = u := by
  simp [verticalPoint, Complex.mul_re]

@[simp] theorem verticalPoint_im (u v : ℝ) : (verticalPoint u v).im = v := by
  simp [verticalPoint, Complex.mul_im]

theorem norm_verticalPoint_sq (u v : ℝ) : ‖verticalPoint u v‖ ^ 2 = u ^ 2 + v ^ 2 := by
  rw [← normSq_eq_norm_sq, Complex.normSq_apply, verticalPoint_re, verticalPoint_im, pow_two, pow_two]

theorem verticalPoint_ne_zero {u : ℝ} (hu : 0 < u) (v : ℝ) : verticalPoint u v ≠ 0 := by
  intro h
  have e := congrArg Complex.re h
  simpa using hu.ne' (by simpa only [verticalPoint_re, zero_re] using e)

theorem integrable_cauchy_density {u : ℝ} (hu : 0 < u) :
    Integrable (fun v : ℝ => (u ^ 2 + v ^ 2)⁻¹) := by
  have h := (integrable_inv_one_add_mul_sq (inv_ne_zero hu.ne')).const_mul ((u ^ 2)⁻¹)
  apply h.congr
  filter_upwards with v
  change ((u ^ 2)⁻¹) * (1 + (u⁻¹ * v) ^ 2)⁻¹ = _
  rw [← mul_inv]
  congr 1
  field_simp

theorem integral_cauchy_density {u : ℝ} (hu : 0 < u) :
    ∫ v : ℝ, (u ^ 2 + v ^ 2)⁻¹ = Real.pi / u := by
  have h (v : ℝ) : (u ^ 2 + v ^ 2)⁻¹ = ((u ^ 2)⁻¹) * (1 + (u⁻¹ * v) ^ 2)⁻¹ := by
    rw [← mul_inv]
    congr 1
    field_simp
  simp_rw [h, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_mul_sq,
    abs_of_nonneg (inv_nonneg.mpr hu.le)]
  field_simp

theorem integrable_vertical_inv_pow {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 2 ≤ j) :
    Integrable (fun v : ℝ => ((verticalPoint u v) ^ j)⁻¹) := by
  let c : ℝ := (u ^ (j - 2))⁻¹
  refine ((integrable_cauchy_density hu).const_mul c).mono' (?_) (ae_of_all _ fun v => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    apply Continuous.inv₀ (f := fun v : ℝ => (verticalPoint u v) ^ j)
    · unfold verticalPoint
      fun_prop
    · exact fun v => pow_ne_zero _ (verticalPoint_ne_zero hu v)
  · have hz : u ≤ ‖verticalPoint u v‖ := by simpa using Complex.re_le_norm (verticalPoint u v)
    have hinv : (‖verticalPoint u v‖ ^ (j - 2))⁻¹ ≤ (u ^ (j - 2))⁻¹ :=
      inv_anti₀ (pow_pos hu _) (pow_le_pow_left₀ hu.le hz _)
    have hp : ‖verticalPoint u v‖ ^ j =
        ‖verticalPoint u v‖ ^ (j - 2) * ‖verticalPoint u v‖ ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    rw [norm_inv, norm_pow, hp, mul_inv, norm_verticalPoint_sq]
    exact mul_le_mul_of_nonneg_right hinv (by positivity)

def laplaceTerm (m : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ m * exp (-z * t)

theorem integrableOn_laplaceTerm (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (laplaceTerm m z) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(z.re * t))) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := (m : ℝ)) (p := 1) (by
        linarith [Nat.cast_nonneg (α := ℝ) m]) one_pos hz
  apply hb.mono'
  · apply Continuous.aestronglyMeasurable
    unfold laplaceTerm
    fun_prop
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have htp : 0 < t := ht
    simp [laplaceTerm, norm_pow, Complex.norm_real, abs_of_pos htp,
      Complex.norm_exp, Complex.mul_re, Real.norm_eq_abs]

private theorem tendsto_laplaceTerm (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (laplaceTerm m z) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hr := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) z.re hz
  apply hr.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
  simp [laplaceTerm, norm_pow, Complex.norm_real, abs_of_pos ht,
    Complex.norm_exp, Complex.mul_re, Real.norm_eq_abs]

/-- The positive-ray Laplace transform of an integral power, with complex decay parameter. -/
theorem integral_laplaceTerm (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), laplaceTerm m z t = ((m.factorial : ℕ) : ℂ) / z ^ (m + 1) := by
  have hz₀ : z ≠ 0 := by intro h; simp [h] at hz
  induction m with
  | zero =>
    simpa only [laplaceTerm, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add,
      pow_one, Complex.ofReal_zero, mul_zero, exp_zero, neg_div_neg_eq] using
      integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
  | succ m ih =>
    let p := fun t : ℝ => ((m + 1 : ℕ) : ℂ) * laplaceTerm m z t
    let q := fun t : ℝ => z * laplaceTerm (m + 1) z t
    have hp : IntegrableOn p (Ioi 0) := (integrableOn_laplaceTerm m hz).const_mul _
    have hq : IntegrableOn q (Ioi 0) := (integrableOn_laplaceTerm (m + 1) hz).const_mul _
    have hder (t : ℝ) : HasDerivAt (laplaceTerm (m + 1) z) (p t - q t) t := by
      have ht := (hasDerivAt_id (t : ℂ)).pow (m + 1)
      have he := ((hasDerivAt_id (t : ℂ)).const_mul (-z)).cexp
      convert (ht.mul he).comp_ofReal using 1
      · rfl
      · simp only [laplaceTerm, p, q, Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one]
        ring
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
      (fun t _ => hder t) (hp.sub hq) (tendsto_laplaceTerm (m + 1) hz)
    change (∫ t in Ioi (0 : ℝ), p t - q t) = 0 - laplaceTerm (m + 1) z 0 at h
    rw [integral_sub hp hq] at h
    have hz' : laplaceTerm (m + 1) z 0 = 0 := by simp [laplaceTerm]
    simp only [p, q, integral_const_mul, hz', sub_zero] at h
    rw [ih] at h
    have h' := sub_eq_zero.mp h
    apply (eq_div_iff (pow_ne_zero _ hz₀)).2
    calc
      _ = (z * ∫ t in Ioi (0 : ℝ), laplaceTerm (m + 1) z t) * z ^ (m + 1) := by
        rw [pow_succ]
        ring
      _ = _ := by
        rw [← h', mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hz₀), Nat.factorial_succ, Nat.cast_mul]

private def laplacePosRay (m : ℕ) (u : ℝ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator (laplaceTerm m u)

private theorem fourier_laplacePosRay (m : ℕ) {u : ℝ} (hu : 0 < u) (w : ℝ) :
    𝓕 (laplacePosRay m u) w =
      (m.factorial : ℂ) / (verticalPoint u (2 * Real.pi * w)) ^ (m + 1) := by
  rw [Real.fourier_eq']
  have he (v : ℝ) :
      exp ((↑(-2 * Real.pi * inner ℝ v w : ℝ) : ℂ) * I) • laplacePosRay m u v =
        (Ioi (0 : ℝ)).indicator (laplaceTerm m (verticalPoint u (2 * Real.pi * w))) v := by
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · simp only [laplacePosRay, Set.indicator_of_mem hv, smul_eq_mul, laplaceTerm,
        Real.inner_apply, verticalPoint]
      rw [mul_left_comm, ← exp_add]
      congr 2
      push_cast
      ring
    · simp [laplacePosRay, hv]
  simp_rw [he, integral_indicator measurableSet_Ioi]
  exact integral_laplaceTerm m (z := verticalPoint u (2 * Real.pi * w)) (by simpa using hu)

/-- The Bromwich kernel in (17). The real frequency variable is scaled by
`2π` before applying Fourier inversion. -/
theorem integral_vertical_kernel {u x : ℝ} (hu : 0 < u) (hx : 0 < x) {j : ℕ} (hj : 2 ≤ j) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ v : ℝ, exp ((x : ℂ) * verticalPoint u v) / (verticalPoint u v) ^ j) =
        (x : ℂ) ^ (j - 1) / (((j - 1 : ℕ).factorial : ℕ) : ℂ) := by
  let m : ℕ := j - 1
  let b : ℝ := 2 * Real.pi
  let α : ℂ := m.factorial
  have hj' : m + 1 = j := by omega
  have hbp : 0 < b := by dsimp [b]; positivity
  have hα : α ≠ 0 := by dsimp [α]; exact_mod_cast Nat.factorial_ne_zero m
  have hBase : Integrable (laplacePosRay m u) :=
    (integrableOn_laplaceTerm m (z := (u : ℂ)) (by simpa using hu)).integrable_indicator measurableSet_Ioi
  have hFourier : Integrable (𝓕 (laplacePosRay m u)) := by
    have hf : (𝓕 (laplacePosRay m u)) =
        fun v : ℝ => α * (verticalPoint u (b * v) ^ j)⁻¹ := by
      funext v
      rw [fourier_laplacePosRay m hu, hj', div_eq_mul_inv]
    rw [hf]
    exact ((integrable_vertical_inv_pow hu hj).comp_mul_left' hbp.ne').const_mul _
  have hCont : ContinuousAt (laplacePosRay m u) x := by
    have ht : ContinuousAt (laplaceTerm m u) x := by unfold laplaceTerm; fun_prop
    apply ht.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact Set.indicator_of_mem ht _
  have hInv := hBase.fourierInv_fourier_eq hFourier hCont
  rw [Real.fourierInv_eq'] at hInv
  have hEq (v : ℝ) :
      exp ((↑(2 * Real.pi * inner ℝ v x : ℝ) : ℂ) * I) •
        𝓕 (laplacePosRay m u) v =
        α * (exp ((x : ℂ) * ((b * v : ℝ) : ℂ) * I) / verticalPoint u (b * v) ^ j) := by
    rw [fourier_laplacePosRay m hu, hj', Real.inner_apply, smul_eq_mul]
    dsimp [b, α]
    rw [show (↑(2 * Real.pi * (v * x) : ℝ) : ℂ) = (x : ℂ) * ((2 * Real.pi * v : ℝ) : ℂ) by
      push_cast; ring]
    ring
  simp_rw [hEq, integral_const_mul] at hInv
  have hScale := Measure.integral_comp_mul_left (fun v : ℝ =>
    exp ((x : ℂ) * (v : ℂ) * I) / (verticalPoint u v) ^ j) b
  simp only [Complex.real_smul] at hScale
  have hInv' : α * ((b : ℂ)⁻¹ *
      (∫ v : ℝ, exp ((x : ℂ) * (v : ℂ) * I) / (verticalPoint u v) ^ j)) =
      (x : ℂ) ^ m * exp (-(u : ℂ) * x) := by
    rw [abs_of_pos (inv_pos.mpr hbp), Complex.ofReal_inv] at hScale
    rw [hScale, laplacePosRay, Set.indicator_of_mem hx, laplaceTerm] at hInv
    exact hInv
  have hExp (v : ℝ) : exp ((x : ℂ) * verticalPoint u v) / verticalPoint u v ^ j =
      exp ((u : ℂ) * x) * (exp ((x : ℂ) * (v : ℂ) * I) / verticalPoint u v ^ j) := by
    rw [verticalPoint, mul_add, exp_add]
    ring
  change (b : ℂ)⁻¹ * _ = (x : ℂ) ^ m / α
  simp_rw [hExp, integral_const_mul]
  apply (eq_div_iff hα).2
  calc
    _ = exp ((u : ℂ) * x) * (α * ((b : ℂ)⁻¹ *
        (∫ v : ℝ, exp ((x : ℂ) * (v : ℂ) * I) / verticalPoint u v ^ j))) := by ring
    _ = _ := by
      rw [hInv', mul_left_comm, ← exp_add, show (u : ℂ) * x + -(u : ℂ) * x = 0 by ring,
        exp_zero, mul_one]

end DurfeeCCS.Step08
