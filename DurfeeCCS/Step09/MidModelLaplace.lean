module

public import DurfeeCCS.Step09.MidModelDecay
public import DurfeeCCS.Step08.SaddleBesselLaplace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The half-integer Laplace transform used in the Fourier inversion for Lemma 3.7. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set Filter
open scoped FourierTransform Topology
open DurfeeCCS.Step08 (verticalPoint verticalPoint_re)

/-- The rational coefficient of `√π` in the half-integer Gamma value. -/
def midHalfGammaCoeff (k : ℕ) : ℝ :=
  (((2 * k + 2).factorial : ℕ) : ℝ) / (4 ^ (k + 1) * ((k + 1).factorial : ℝ))

theorem midHalfGammaCoeff_pos (k : ℕ) : 0 < midHalfGammaCoeff k := by
  unfold midHalfGammaCoeff
  positivity

theorem midHalfGammaCoeff_zero : midHalfGammaCoeff 0 = 1 / 2 := by
  norm_num [midHalfGammaCoeff, Nat.factorial]

theorem midHalfGammaCoeff_succ (k : ℕ) :
    midHalfGammaCoeff (k + 1) = ((k : ℝ) + 3 / 2) * midHalfGammaCoeff k := by
  unfold midHalfGammaCoeff
  rw [show 2 * (k + 1) + 2 = (2 * k + 2 + 1) + 1 by omega]
  rw [Nat.factorial_succ (2 * k + 2 + 1), Nat.factorial_succ (2 * k + 2),
    Nat.factorial_succ (k + 1), pow_succ (4 : ℝ) (k + 1)]
  push_cast
  have hp : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hk : (0 : ℝ) ≤ k := by positivity
  field_simp
  ring

def midHalfDensity (k : ℕ) (z : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-z * (y : ℂ)) * ((y ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ)

theorem integrableOn_midHalfDensity (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (midHalfDensity k z) (Ioi 0) :=
  DurfeeCCS.Step08.integrable_laplace_rpow hz (by linarith [Nat.cast_nonneg (α := ℝ) k])

private theorem tendsto_midHalfDensity (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (midHalfDensity k z) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) + 1 / 2) z.re hz
  apply h.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with y hy
  have hpos := Real.rpow_nonneg hy.le ((k : ℝ) + 1 / 2)
  simp [midHalfDensity, Complex.norm_exp, Complex.mul_re, mul_comm]
  simpa only [one_div] using (abs_of_nonneg hpos).symm

private theorem midHalfDensity_zero (k : ℕ) (z : ℂ) : midHalfDensity k z 0 = 0 := by
  rw [midHalfDensity, Real.zero_rpow (by positivity : (k : ℝ) + 1 / 2 ≠ 0)]
  simp

private theorem hasDerivAt_midHalfDensity_succ (k : ℕ) (z : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (midHalfDensity (k + 1) z)
      ((((k : ℂ) + 3 / 2) * midHalfDensity k z y) - z * midHalfDensity (k + 1) z y) y := by
  have hE := (((hasDerivAt_id (y : ℂ)).const_mul (-z)).cexp).comp_ofReal
  let q := (((k + 1 : ℕ) : ℝ) + 1 / 2)
  have hD := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hy.ne')).ofReal_comp
  have hq : q - 1 = (k : ℝ) + 1 / 2 := by dsimp [q]; push_cast; ring
  have hqC : (q : ℂ) = (k : ℂ) + 3 / 2 := by dsimp [q]; push_cast; ring
  have h := hE.mul hD
  change HasDerivAt (midHalfDensity (k + 1) z) _ y at h
  convert h using 1
  change _ = Complex.exp (-z * (y : ℂ)) * (-z * 1) *
    ((y ^ q : ℝ) : ℂ) + Complex.exp (-z * (y : ℂ)) *
    ((q * y ^ (q - 1) : ℝ) : ℂ)
  simp only [midHalfDensity, hq, Complex.ofReal_mul, hqC, mul_one]
  change _ * (Complex.exp (-z * (y : ℂ)) * _) -
    z * (Complex.exp (-z * (y : ℂ)) * ((y ^ q : ℝ) : ℂ)) = _
  ring

/-- Half-integer version of the positive-ray Laplace transform. -/
theorem integral_midHalfDensity (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    (∫ y in Ioi (0 : ℝ), midHalfDensity k z y) =
      (midHalfGammaCoeff k : ℂ) * (Real.sqrt Real.pi : ℂ) * (z.sqrt / z ^ (k + 2)) := by
  have hz' : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hs : z.sqrt ^ 2 = z := DurfeeCCS.Step06.principalSqrt_sq z
  have hs' : z.sqrt ≠ 0 := by intro h; simp [h] at hs; exact hz' hs.symm
  induction k with
  | zero =>
    simp only [midHalfDensity, Nat.cast_zero, zero_add, ← Real.sqrt_eq_rpow]
    rw [DurfeeCCS.Step08.integral_laplace_sqrt hz,
      DurfeeCCS.Step08.sqrt_div_right_half_plane Real.pi Real.pi_pos.le hz,
      midHalfGammaCoeff_zero]
    push_cast
    field_simp
    rw [hs]
  | succ k ih =>
    let f := fun y : ℝ => ((k : ℂ) + 3 / 2) * midHalfDensity k z y
    let g := fun y : ℝ => z * midHalfDensity (k + 1) z y
    have hf : IntegrableOn f (Ioi 0) := (integrableOn_midHalfDensity k hz).const_mul _
    have hg : IntegrableOn g (Ioi 0) := (integrableOn_midHalfDensity (k + 1) hz).const_mul _
    have hcont : Continuous (midHalfDensity (k + 1) z) := by
      unfold midHalfDensity
      exact (by fun_prop : Continuous (fun y : ℝ => exp (-z * (y : ℂ)))).mul
        (Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by positivity)))
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) hcont.continuousAt.continuousWithinAt
      (fun t ht => hasDerivAt_midHalfDensity_succ k z ht)
      (hf.sub hg) (tendsto_midHalfDensity (k + 1) hz)
    change (∫ t in Ioi (0 : ℝ), f t - g t) = 0 - midHalfDensity (k + 1) z 0 at h
    rw [integral_sub hf hg] at h
    simp only [f, g, integral_const_mul, midHalfDensity_zero, sub_zero] at h
    have he := sub_eq_zero.mp h
    rw [ih] at he
    rw [midHalfGammaCoeff_succ]
    apply mul_left_cancel₀ hz'
    rw [← he]
    push_cast
    rw [show k + 1 + 2 = k + 2 + 1 by omega, pow_succ]
    field_simp
    ring

private def midHalfDensityPositive (k : ℕ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator (midHalfDensity k 1)

private theorem fourier_midHalfDensity (k : ℕ) (v : ℝ) :
    𝓕 (midHalfDensityPositive k) v =
      (midHalfGammaCoeff k : ℂ) * (Real.sqrt Real.pi : ℂ) *
        ((midModelZ (2 * Real.pi * v)).sqrt / (midModelZ (2 * Real.pi * v)) ^ (k + 2)) := by
  rw [Real.fourier_eq']
  have he (y : ℝ) :
      exp ((↑(-2 * Real.pi * inner ℝ y v : ℝ) : ℂ) * I) • midHalfDensityPositive k y =
        (Ioi (0 : ℝ)).indicator (midHalfDensity k (midModelZ (2 * Real.pi * v))) y := by
    by_cases hy : y ∈ Ioi (0 : ℝ)
    · simp only [midHalfDensityPositive, Set.indicator_of_mem hy, smul_eq_mul,
        midHalfDensity, Real.inner_apply, verticalPoint]
      rw [← mul_assoc, ← exp_add]
      congr 2
      push_cast
      ring
    · simp [midHalfDensityPositive, hy]
  simp_rw [he, integral_indicator measurableSet_Ioi]
  exact integral_midHalfDensity k (by simp)

theorem continuous_midHalfKernel (k : ℕ) :
    Continuous (fun η : ℝ => (midModelZ η).sqrt / midModelZ η ^ (k + 2)) := by
  have hz : Continuous (fun η : ℝ => (midModelZ η).sqrt) :=
    continuous_iff_continuousAt.mpr fun η => (hasDerivAt_midModelSqrt η).continuousAt
  exact hz.div (continuous_midModelZ.pow _) (fun η => pow_ne_zero _ (midModelZ_ne_zero η))

theorem integrable_midHalfKernel (k : ℕ) :
    Integrable (fun η : ℝ => (midModelZ η).sqrt / midModelZ η ^ (k + 2)) := by
  have hi := integrable_midModelDecay (q := ((k + 2 : ℕ) : ℝ) - 1 / 2) (by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
  exact hi.mono' (continuous_midHalfKernel k).aestronglyMeasurable (Eventually.of_forall
    fun η => (norm_midModelSqrt_div_pow η (k + 2)).le)

/-- Fourier inversion for the positive-ray half-integer density. -/
theorem integral_midHalfKernel_fourier (k : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ η : ℝ, midModelOsc t η * ((midModelZ η).sqrt / midModelZ η ^ (k + 2))) =
      ((2 * Real.pi : ℝ) : ℂ) / ((midHalfGammaCoeff k * Real.sqrt Real.pi : ℝ) : ℂ) *
        ((t ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.exp (-(t : ℂ)) := by
  let b : ℝ := 2 * Real.pi
  let C : ℂ := (midHalfGammaCoeff k : ℂ) * (Real.sqrt Real.pi : ℂ)
  let kernel := fun η : ℝ => (midModelZ η).sqrt / midModelZ η ^ (k + 2)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hC : C ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr (midHalfGammaCoeff_pos k).ne')
    (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')
  have hBase : Integrable (midHalfDensityPositive k) :=
    (integrableOn_midHalfDensity k (z := 1) (by norm_num)).integrable_indicator measurableSet_Ioi
  have hFourier : Integrable (𝓕 (midHalfDensityPositive k)) := by
    have he : (𝓕 (midHalfDensityPositive k)) = fun v : ℝ => C * kernel (b * v) := by
      funext v
      exact fourier_midHalfDensity k v
    rw [he]
    exact ((integrable_midHalfKernel k).comp_mul_left' hb.ne').const_mul _
  have hCont : ContinuousAt (midHalfDensityPositive k) t := by
    have htc : ContinuousAt (midHalfDensity k 1) t := by
      unfold midHalfDensity
      exact (by fun_prop : ContinuousAt (fun y : ℝ => exp (-(1 : ℂ) * (y : ℂ))) t).mul
        (Complex.continuous_ofReal.continuousAt.comp
          (continuousAt_id.rpow_const (Or.inl ht.ne')))
    apply htc.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with v hv
    exact Set.indicator_of_mem hv _
  have hInv := hBase.fourierInv_fourier_eq hFourier hCont
  rw [Real.fourierInv_eq'] at hInv
  have he (v : ℝ) :
      exp ((↑(2 * Real.pi * inner ℝ v t : ℝ) : ℂ) * I) • 𝓕 (midHalfDensityPositive k) v =
        C * (midModelOsc t (b * v) * kernel (b * v)) := by
    rw [fourier_midHalfDensity, Real.inner_apply, smul_eq_mul, midModelOsc]
    dsimp [b, C, kernel]
    rw [show (↑(2 * Real.pi * (v * t) : ℝ) : ℂ) =
        (t : ℂ) * ((2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring]
    ring
  simp_rw [he, integral_const_mul] at hInv
  have hScale := Measure.integral_comp_mul_left (fun v : ℝ => midModelOsc t v * kernel v) b
  simp only [Complex.real_smul, abs_of_pos (inv_pos.mpr hb), Complex.ofReal_inv] at hScale
  rw [hScale, midHalfDensityPositive, Set.indicator_of_mem ht, midHalfDensity] at hInv
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hbc : (b : ℂ) = (2 : ℂ) * (Real.pi : ℂ) := by
    unfold b
    norm_cast
  rw [← hbc]
  change (∫ v : ℝ, midModelOsc t v * kernel v) = (b : ℂ) / C * _ * _
  have hb' := ofReal_ne_zero.mpr hb.ne'
  apply mul_left_cancel₀ (mul_ne_zero hC (inv_ne_zero hb') : C * (b : ℂ)⁻¹ ≠ 0)
  rw [mul_assoc, hInv]
  field_simp

end DurfeeCCS.Step09
