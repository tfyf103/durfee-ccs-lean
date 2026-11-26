module

public import DurfeeCCS.Step06.BesselIntegrals
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# First-order error estimate for the ordinary Bessel function

The theorem `nemes_first_error` proves manuscript equation (11) for orders zero and one.
The exact Hankel–Gamma representation is obtained by deforming the Poisson integral
to two conjugate vertical rays. The local estimate then follows by comparing the
half-power factor with one and integrating against the normalized Gamma density.
-/

@[expose] public noncomputable section

namespace DurfeeCCS.Step06

open MeasureTheory Set

/-- The two half-power factors used for orders zero and one. -/
def hankelHalfPower (ν : ℕ) (s : ℝ) : ℂ :=
  if ν = 0 then (Complex.sqrt (1 + (s : ℂ) * Complex.I))⁻¹
  else Complex.sqrt (1 + (s : ℂ) * Complex.I)

private theorem re_sqrt_vertical_ge_one (s : ℝ) :
    1 ≤ (Complex.sqrt (1 + (s : ℂ) * Complex.I)).re := by
  have hz : (1 + (s : ℂ) * Complex.I).re = 1 := by simp [Complex.mul_re]
  have hn : 1 ≤ ‖1 + (s : ℂ) * Complex.I‖ := by
    simpa only [hz] using Complex.re_le_norm (1 + (s : ℂ) * Complex.I)
  rw [Complex.sqrt, Complex.cpow_inv_two_re, hz]
  apply Real.le_sqrt_of_sq_le
  norm_num
  linarith

private theorem sqrt_square_nonzero {z : ℂ} (hz : z ≠ 0) :
    Complex.sqrt z ^ (2 : ℕ) = z := by
  rw [Complex.sqrt, pow_two, ← Complex.cpow_add _ _ hz,
    show (2 : ℂ)⁻¹ + 2⁻¹ = 1 by norm_num, Complex.cpow_one]

private theorem sqrt_vertical_square (s : ℝ) :
    Complex.sqrt (1 + (s : ℂ) * Complex.I) ^ (2 : ℕ) = 1 + (s : ℂ) * Complex.I := by
  apply sqrt_square_nonzero
  intro h
  have h' := congrArg Complex.re h
  simp [Complex.mul_re] at h'

/-- On the vertical line with real part one the two half-powers differ from one by
at most half the distance along the line. -/
theorem norm_hankelHalfPower_sub_one_le (ν : ℕ) (s : ℝ) :
    ‖hankelHalfPower ν s - 1‖ ≤ |s| / 2 := by
  let w := Complex.sqrt (1 + (s : ℂ) * Complex.I)
  have hw : 1 ≤ w.re := re_sqrt_vertical_ge_one s
  have hnorm : 1 ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  have hnorm_add : 2 ≤ ‖w + 1‖ := by
    have h := Complex.re_le_norm (w + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hprod : (w - 1) * (w + 1) = (s : ℂ) * Complex.I := by
    calc
      (w - 1) * (w + 1) = w ^ 2 - 1 := by ring
      _ = (s : ℂ) * Complex.I := by dsimp [w]; rw [sqrt_vertical_square s]; ring
  have hmain : ‖w - 1‖ ≤ |s| / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      ‖w - 1‖ * 2 ≤ ‖w - 1‖ * ‖w + 1‖ :=
        mul_le_mul_of_nonneg_left hnorm_add (norm_nonneg _)
      _ = ‖(s : ℂ) * Complex.I‖ := by rw [← norm_mul, hprod]
      _ = |s| := by simp [Complex.norm_real, Real.norm_eq_abs]
  by_cases hν : ν = 0
  · have hw₀ : w ≠ 0 := by intro hz; norm_num [hz] at hnorm
    have hinv : w⁻¹ - 1 = (1 - w) / w := by
      field_simp [hw₀]
    change ‖(if ν = 0 then w⁻¹ else w) - 1‖ ≤ _
    rw [ite_eq_left hν, hinv, norm_div, norm_sub_rev]
    exact (div_le_self (norm_nonneg _) hnorm).trans hmain
  · simpa [hankelHalfPower, hν, w] using hmain

private theorem continuous_hankelHalfPower (ν : ℕ) : Continuous (hankelHalfPower ν) := by
  have hf : Continuous fun s : ℝ => (1 : ℂ) + (s : ℂ) * Complex.I := by fun_prop
  have hs : Continuous fun s : ℝ => Complex.sqrt (1 + (s : ℂ) * Complex.I) := by
    refine continuous_iff_continuousAt.mpr fun s => ?_
    refine (Complex.continuousAt_sqrt (Or.inl ?_)).comp hf.continuousAt
    simp [Complex.mul_re]
  change Continuous (fun s => hankelHalfPower ν s)
  by_cases hν : ν = 0
  · simp only [hankelHalfPower, ite_eq_left hν]
    apply hs.inv₀
    intro s hz
    have h := re_sqrt_vertical_ge_one s
    rw [hz] at h
    norm_num at h
  · simpa [hankelHalfPower, hν] using hs

/-- Integrand for deforming the Poisson segment to vertical rays. -/
def poissonKernel (ν : ℕ) (x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I * z) *
    if ν = 0 then (Complex.sqrt (1 - z ^ (2 : ℕ)))⁻¹
    else Complex.sqrt (1 - z ^ (2 : ℕ))

/-- The branch for the Poisson kernel is holomorphic on the deformation strip above the
integration segment, including either vertical line over an endpoint. -/
theorem differentiableAt_poissonKernel (ν : ℕ) (x : ℝ) {z : ℂ}
    (hre : |z.re| ≤ 1) (him : 0 < z.im) :
    DifferentiableAt ℂ (poissonKernel ν x) z := by
  let φ : ℂ → ℂ := fun w => 1 - w ^ (2 : ℕ)
  have hφ : 0 < (φ z).re := by
    simp only [φ, Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re]
    obtain ⟨hl, hu⟩ := abs_le.mp hre
    nlinarith [mul_nonneg (show 0 ≤ 1 + z.re by linarith)
      (show 0 ≤ 1 - z.re by linarith), mul_pos him him]
  have hs : DifferentiableAt ℂ (Complex.sqrt ∘ φ) z :=
    (Complex.differentiableAt_sqrt (Or.inl hφ)).comp z (by dsimp [φ]; fun_prop)
  have hφ₀ : φ z ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hφ
    exact lt_irrefl _ hφ
  have hs₀ : (Complex.sqrt ∘ φ) z ≠ 0 := by
    intro hz
    have h := sqrt_square_nonzero hφ₀
    change Complex.sqrt (φ z) = 0 at hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact hφ₀ h.symm
  have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((x : ℂ) * Complex.I * w)) z := by
    fun_prop
  change DifferentiableAt ℂ (fun w => poissonKernel ν x w) z
  by_cases hν : ν = 0
  · simp only [poissonKernel, ite_eq_left hν]
    exact he.mul (hs.inv hs₀)
  · simp only [poissonKernel, ite_eq_right hν]
    exact he.mul hs

/-- Principal square root on the right vertical side of the Poisson contour. -/
theorem sqrt_poisson_right_ray {y : ℝ} (hy : 0 < y) :
    Complex.sqrt (1 - (1 + (y : ℂ) * Complex.I) ^ (2 : ℕ)) =
      ((Real.sqrt y : ℂ) * (1 - Complex.I)) *
        Complex.sqrt (1 + ((y / 2 : ℝ) : ℂ) * Complex.I) := by
  let z : ℂ := 1 - (1 + (y : ℂ) * Complex.I) ^ (2 : ℕ)
  let w : ℂ := Complex.sqrt (1 + ((y / 2 : ℝ) : ℂ) * Complex.I)
  let u : ℂ := Complex.sqrt z
  let v : ℂ := ((Real.sqrt y : ℂ) * (1 - Complex.I)) * w
  change u = v
  have hz : z.re = y ^ 2 := by
    simp [z, pow_two, Complex.mul_re, Complex.mul_im]
  have hz₀ : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    exact (pow_pos hy 2).ne' hz.symm
  have hu : u ^ (2 : ℕ) = z := sqrt_square_nonzero hz₀
  have hi : (1 - Complex.I) ^ (2 : ℕ) = -2 * Complex.I := by
    calc
      (1 - Complex.I) ^ (2 : ℕ) = 1 - 2 * Complex.I + Complex.I ^ (2 : ℕ) := by ring
      _ = -2 * Complex.I := by rw [Complex.I_sq]; ring
  have hv : v ^ (2 : ℕ) = z := by
    dsimp only [v]
    rw [mul_pow, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hy.le, hi,
      show w ^ (2 : ℕ) = 1 + ((y / 2 : ℝ) : ℂ) * Complex.I from sqrt_vertical_square _]
    push_cast
    calc
      (y : ℂ) * (-2 * Complex.I) * (1 + (y : ℂ) / 2 * Complex.I) =
          -(y : ℂ) ^ (2 : ℕ) * Complex.I ^ (2 : ℕ) - 2 * (y : ℂ) * Complex.I := by ring
      _ = z := by dsimp [z]; ring
  have huw : 0 ≤ u.re := by
    change 0 ≤ (Complex.sqrt z).re
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hww : 1 ≤ w.re := re_sqrt_vertical_ge_one _
  have hwi : 0 ≤ w.im := by
    dsimp only [w, Complex.sqrt]
    rw [Complex.cpow_inv_two_im_eq_sqrt]
    · exact Real.sqrt_nonneg _
    · simpa [Complex.mul_im] using (div_nonneg hy.le (by norm_num : (0 : ℝ) ≤ 2))
  have hvw : 0 < v.re := by
    simp only [v, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.sub_re,
      Complex.one_re, Complex.I_re, sub_zero, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.I_im, zero_sub, zero_mul, add_zero]
    have hsp : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
    nlinarith [mul_pos hsp (show 0 < w.re from zero_lt_one.trans_le hww),
      mul_nonneg hsp.le hwi]
  have hprod : (u - v) * (u + v) = 0 := by
    calc
      (u - v) * (u + v) = u ^ (2 : ℕ) - v ^ (2 : ℕ) := by ring
      _ = 0 := by rw [hu, hv, sub_self]
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at h'
    linarith

/-- The norm on a horizontal contour is bounded by an exponential times a half-power.
The positive lower bound on the real part of the square-root argument permits the
reciprocal estimate at order zero. -/
theorem norm_poissonKernel_le (ν : ℕ) (x : ℝ) (z : ℂ)
    (hz : 0 < 1 - z.re ^ 2 + z.im ^ 2) :
    ‖poissonKernel ν x z‖ ≤ Real.exp (-(x * z.im)) *
      (if ν = 0 then (Real.sqrt (1 - z.re ^ 2 + z.im ^ 2))⁻¹
       else Real.sqrt (1 + z.re ^ 2 + z.im ^ 2)) := by
  let a : ℂ := 1 - z ^ (2 : ℕ)
  have ha : a.re = 1 - z.re ^ 2 + z.im ^ 2 := by
    simp [a, pow_two, Complex.sub_re, Complex.mul_re]
    ring
  have ha₀ : a ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at ha
    exact hz.ne' ha.symm
  have hR : ‖Complex.sqrt a‖ = Real.sqrt ‖a‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (Complex.sqrt a)), ← norm_pow, sqrt_square_nonzero ha₀]
  have hE : ((x : ℂ) * Complex.I * z).re = -(x * z.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  unfold poissonKernel
  change ‖Complex.exp ((x : ℂ) * Complex.I * z) *
    (if ν = 0 then (Complex.sqrt a)⁻¹ else Complex.sqrt a)‖ ≤ _
  rw [norm_mul, Complex.norm_exp, hE]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  by_cases hν : ν = 0
  · simp only [ite_eq_left hν, norm_inv, hR]
    exact inv_anti₀ (Real.sqrt_pos.2 hz) (Real.sqrt_le_sqrt (ha ▸ Complex.re_le_norm a))
  · simp only [ite_eq_right hν, hR]
    apply Real.sqrt_le_sqrt
    calc
      ‖a‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ (2 : ℕ)‖ := norm_sub_le _ _
      _ = 1 + z.re ^ 2 + z.im ^ 2 := by
        have hsq := sub_eq_iff_eq_add.mp (Complex.sq_norm_sub_sq_re z)
        rw [norm_one, norm_pow, hsq]
        ring

open scoped ComplexConjugate

/-- The two vertical rays of the Poisson contour give conjugate integrands. -/
theorem poissonKernel_neg_conj (ν : ℕ) (x : ℝ) {z : ℂ}
    (hz : 0 < (1 - z ^ (2 : ℕ)).re) :
    poissonKernel ν x (-conj z) = conj (poissonKernel ν x z) := by
  let a : ℂ := 1 - z ^ (2 : ℕ)
  have harg : a.arg ≠ Real.pi := by
    intro h
    exact hz.not_gt (Complex.arg_eq_pi_iff.mp h).1
  have ha : 1 - (-conj z) ^ (2 : ℕ) = conj a := by simp [a]
  have hs : Complex.sqrt (conj a) = conj (Complex.sqrt a) := by
    simp only [Complex.sqrt, Complex.conj_cpow a _ harg, map_inv₀, map_ofNat]
  have he : (x : ℂ) * Complex.I * (-conj z) = conj ((x : ℂ) * Complex.I * z) := by
    simp [Complex.conj_I]
  simp only [poissonKernel, he, ha, hs, Complex.exp_conj]
  by_cases hν : ν = 0
  · simp only [ite_eq_left hν, map_mul, map_inv₀, a]
  · simp only [ite_eq_right hν, map_mul, a]

/-- For positive order the Poisson kernel is continuous on the closed vertical strip
including both endpoints of the finite Poisson segment. -/
theorem continuousOn_poissonKernel_of_ne_zero {ν : ℕ} (hν : ν ≠ 0) (x : ℝ) :
    ContinuousOn (poissonKernel ν x) {z | |Complex.re z| ≤ 1} := by
  intro z hz
  have ha : 0 ≤ (1 - z ^ (2 : ℕ)).re := by
    have ⟨h₁, h₂⟩ := abs_le.mp (show |z.re| ≤ 1 from hz)
    simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re]
    nlinarith [mul_nonneg (show 0 ≤ 1 + z.re by linarith)
      (show 0 ≤ 1 - z.re by linarith), sq_nonneg z.im]
  have hin : ContinuousAt (fun w : ℂ => 1 - w ^ (2 : ℕ)) z := by fun_prop
  have hs : ContinuousAt (fun z : ℂ => Complex.sqrt (1 - z ^ (2 : ℕ))) z :=
    (Complex.continuousAt_sqrt (Or.inl ha)).comp (f := fun w : ℂ => 1 - w ^ (2 : ℕ)) hin
  have he : ContinuousAt (fun z : ℂ => Complex.exp ((x : ℂ) * Complex.I * z)) z := by
    fun_prop
  change ContinuousWithinAt (fun z => poissonKernel ν x z) _ z
  simp only [poissonKernel, ite_eq_right hν]
  exact (he.mul hs).continuousWithinAt

open Filter Topology

/-- The Poisson kernel tends uniformly to zero as the imaginary part grows in the
closed vertical strip over the Poisson segment. -/
theorem tendsto_poissonKernel_upper_strip (ν : ℕ) {x : ℝ} (hx : 0 < x) :
    Tendsto (poissonKernel ν x)
      (comap Complex.im atTop ⊓ 𝓟 {z : ℂ | |z.re| ≤ 1}) (𝓝 0) := by
  let l := comap Complex.im atTop ⊓ 𝓟 {z : ℂ | |z.re| ≤ 1}
  have him : Tendsto Complex.im l atTop := tendsto_comap.mono_left inf_le_left
  have hmul : Tendsto (fun y : ℝ => x * y) atTop atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos hx).2 tendsto_id
  have h₁ := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hmul
  have h₂ := Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  have hlim : Tendsto (fun y : ℝ => Real.exp (-(x * y)) * (y + 2)) atTop (𝓝 0) := by
    convert (h₁.const_mul x⁻¹).add (h₂.const_mul 2) using 1
    · funext y
      simp only [Function.comp_apply, pow_one]
      field_simp [hx.ne']
    · simp
  have hre : ∀ᶠ z : ℂ in l, |z.re| ≤ 1 :=
    (eventually_principal.mpr fun _ hz => hz).filter_mono inf_le_right
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (hlim.comp him)
  filter_upwards [him.eventually_ge_atTop 1, hre] with z hzi hzr
  have hzr₂ : z.re ^ 2 ≤ 1 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hzr
    nlinarith [mul_nonneg (show 0 ≤ 1 + z.re by linarith)
      (show 0 ≤ 1 - z.re by linarith)]
  have hzi₂ : 1 ≤ z.im ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ z.im - 1 by linarith)
      (show 0 ≤ z.im + 1 by linarith)]
  have hp : 0 < 1 - z.re ^ 2 + z.im ^ 2 := by linarith
  apply (norm_poissonKernel_le ν x z hp).trans
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  by_cases hν : ν = 0
  · rw [ite_eq_left hν]
    have h : 1 ≤ Real.sqrt (1 - z.re ^ 2 + z.im ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      norm_num
      linarith
    exact (inv_le_one_of_one_le₀ h).trans (by linarith)
  · rw [ite_eq_right hν]
    exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩

private theorem integrableOn_exp_linear {x : ℝ} (hx : 0 < x) (c : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * (t + c)) (Ioi 0) := by
  have h₀ : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa using Real.GammaIntegral_convergent (s := 1) (by norm_num)
  have h₁ : IntegrableOn (fun t : ℝ => Real.exp (-t) * t) (Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := 2) (by norm_num) using 1
    ext t
    norm_num
  let f : ℝ → ℝ := fun t => Real.exp (-t) * (x⁻¹ * t + c)
  have hf_eq : f = (fun t => x⁻¹ * (Real.exp (-t) * t) + c * Real.exp (-t)) := by
    ext t
    dsimp [f]
    ring
  have hf : IntegrableOn f (Ioi 0) := by
    rw [hf_eq]
    exact (h₁.const_mul x⁻¹).add (h₀.const_mul c)
  have hc : IntegrableOn (fun t => f (x * t)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff f 0 hx).mpr (by simpa using hf)
  simpa [f, ← mul_assoc, hx.ne'] using hc

/-- Both vertical sides of a contour above the real interval have integrable tails.
For positive orders the sides can start at the interval endpoints. -/
theorem integrableOn_poissonKernel_vertical (ν : ℕ) {x δ b : ℝ} (hx : 0 < x)
    (hδ : 0 ≤ δ) (hνδ : ν ≠ 0 ∨ 0 < δ) (hb : |b| = 1) :
    IntegrableOn (fun y : ℝ => poissonKernel ν x ((b : ℂ) + (y : ℂ) * Complex.I))
      (Ioi δ) := by
  let z : ℝ → ℂ := fun y => (b : ℂ) + (y : ℂ) * Complex.I
  have hzr (y : ℝ) : (z y).re = b := by simp [z, Complex.mul_re]
  have hzi (y : ℝ) : (z y).im = y := by simp [z, Complex.mul_im]
  have hb₂ : b ^ 2 = 1 := by rw [← sq_abs, hb]; norm_num
  have hmaj : IntegrableOn (fun y : ℝ => Real.exp (-(x * y)) * (y + (2 + δ⁻¹))) (Ioi δ) :=
    (integrableOn_exp_linear hx (2 + δ⁻¹)).mono_set (Ioi_subset_Ioi hδ)
  have hmeas : AEStronglyMeasurable (poissonKernel ν x ∘ z) (volume.restrict (Ioi δ)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro y hy
    have hy₀ : 0 < y := hδ.trans_lt hy
    have hd := differentiableAt_poissonKernel ν x (z := z y)
      (by rw [hzr, hb]) (by rwa [hzi])
    exact (hd.continuousAt.comp (by dsimp [z]; fun_prop)).continuousWithinAt
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  have hy₀ : 0 < y := hδ.trans_lt hy
  have hp : 0 < 1 - (z y).re ^ 2 + (z y).im ^ 2 := by
    simpa [hzr, hzi, hb₂] using pow_pos hy₀ 2
  refine (norm_poissonKernel_le ν x (z y) hp).trans ?_
  rw [hzr, hzi, hb₂]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  by_cases hν : ν = 0
  · rw [ite_eq_left hν, sub_self, zero_add, Real.sqrt_sq hy₀.le]
    have hδ₀ := hνδ.resolve_left (not_not_intro hν)
    exact (inv_anti₀ hδ₀ hy.le).trans (by linarith)
  · rw [ite_eq_right hν]
    apply Real.sqrt_le_iff.mpr
    have hd : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ
    refine ⟨by linarith, ?_⟩
    nlinarith [mul_nonneg hy₀.le hd, sq_nonneg δ⁻¹]

/-- Cauchy's contour deformation from a horizontal segment to the two infinite rays. -/
theorem integral_boundary_poissonKernel (ν : ℕ) {x δ : ℝ} (hx : 0 < x)
    (hδ : 0 ≤ δ) (hνδ : ν ≠ 0 ∨ 0 < δ) :
    (∫ t : ℝ in (-1 : ℝ)..1, poissonKernel ν x ((t : ℂ) + (δ : ℂ) * Complex.I)) +
      Complex.I * (∫ t in Ioi δ, poissonKernel ν x (1 + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t in Ioi δ, poissonKernel ν x (-1 + (t : ℂ) * Complex.I)) = 0 := by
  have hr : Set.uIcc (-1 : ℝ) 1 = Icc (-1) 1 := Set.uIcc_of_le (by norm_num)
  have hcont :
      ContinuousOn (poissonKernel ν x) (Set.uIcc (-1 : ℝ) 1 ×ℂ Ici δ) := by
    intro z hz
    rw [hr, Complex.mem_reProdIm] at hz
    have hzr : |z.re| ≤ 1 := abs_le.mpr hz.1
    rcases hνδ with hν | hδ₀
    · exact (continuousOn_poissonKernel_of_ne_zero hν x z hzr).mono
        (fun w hw => by rw [hr, Complex.mem_reProdIm] at hw; exact abs_le.mpr hw.1)
    · exact (differentiableAt_poissonKernel ν x hzr (hδ₀.trans_le hz.2)).continuousAt.continuousWithinAt
  have hd : ∀ z ∈ (Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1) ×ℂ Ioi δ) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (poissonKernel ν x) z := by
    intro z hz
    obtain ⟨hzr, hzi⟩ := Complex.mem_reProdIm.mp hz.1
    apply differentiableAt_poissonKernel ν x _ (hδ.trans_lt hzi)
    rw [abs_le]
    have hzr' : z.re ∈ Ioo (-1 : ℝ) 1 := by simpa using hzr
    exact ⟨hzr'.1.le, hzr'.2.le⟩
  have htop : Tendsto (poissonKernel ν x)
      (comap Complex.im atTop ⊓ 𝓟 (Set.uIcc (-1 : ℝ) 1 ×ℂ univ)) (𝓝 0) := by
    have hs : Set.uIcc (-1 : ℝ) 1 ×ℂ (univ : Set ℝ) = {z : ℂ | |z.re| ≤ 1} := by
      ext z
      simp [Complex.mem_reProdIm, abs_le]
    rw [hs]
    exact tendsto_poissonKernel_upper_strip ν hx
  have hright := integrableOn_poissonKernel_vertical ν hx hδ hνδ (b := 1) (by norm_num)
  have hleft := integrableOn_poissonKernel_vertical ν hx hδ hνδ (b := -1) (by norm_num)
  simpa [smul_eq_mul] using
    Complex.integral_boundary_unbounded_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
      δ hcont ∅ Set.countable_empty hd hleft hright htop

/-- The positive density in Euler's integral for `Γ(a)`. -/
def hankelGammaWeight (a t : ℝ) : ℝ := Real.exp (-t) * t ^ (a - 1)

/-- The Gamma-normalized Hankel factor on the positive real axis at orders zero and one. -/
def hankelGammaAmplitude (ν : ℕ) (x : ℝ) : ℂ :=
  (∫ t in Ioi (0 : ℝ), (hankelGammaWeight ((ν : ℝ) + 1 / 2) t : ℂ) *
    hankelHalfPower ν (t / (2 * x))) / (Real.Gamma ((ν : ℝ) + 1 / 2) : ℂ)

private theorem gamma_weight_mul (a t : ℝ) (ht : 0 < t) :
    hankelGammaWeight a t * t = hankelGammaWeight (a + 1) t := by
  unfold hankelGammaWeight
  rw [mul_assoc, ← Real.rpow_add_one ht.ne', show a - 1 + 1 = a + 1 - 1 by ring]

/-- Normalized Gamma averages preserve the sharp first-order estimate for the half-power
factor. This estimate applies to the stated integral independently of a Bessel identity. -/
theorem norm_hankelGammaAmplitude_sub_one_le (ν : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖hankelGammaAmplitude ν x - 1‖ ≤ ((ν : ℝ) + 1 / 2) / (4 * x) := by
  let a : ℝ := (ν : ℝ) + 1 / 2
  let μ := volume.restrict (Ioi (0 : ℝ))
  let w : ℝ → ℂ := fun t => (hankelGammaWeight a t : ℂ)
  let g : ℝ → ℂ := fun t => w t * (hankelHalfPower ν (t / (2 * x)) - 1)
  let h : ℝ → ℝ := fun t => (4 * x)⁻¹ * hankelGammaWeight (a + 1) t
  have ha : 0 < a := by dsimp [a]; positivity
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hΓ₀ : (Real.Gamma a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΓ.ne'
  have hw : Integrable w μ := (Real.GammaIntegral_convergent ha).ofReal
  have hi : Integrable h μ := (Real.GammaIntegral_convergent (by linarith : 0 < a + 1)).const_mul _
  have hbound : ∀ᵐ t ∂μ, ‖g t‖ ≤ h t := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    have hw' : 0 ≤ hankelGammaWeight a t := by unfold hankelGammaWeight; positivity
    change ‖w t * (hankelHalfPower ν (t / (2 * x)) - 1)‖ ≤ h t
    rw [norm_mul, show ‖w t‖ = hankelGammaWeight a t from Complex.norm_of_nonneg hw']
    have hb := mul_le_mul_of_nonneg_left (norm_hankelHalfPower_sub_one_le ν (t / (2 * x))) hw'
    rw [abs_of_nonneg (by positivity : 0 ≤ t / (2 * x))] at hb
    convert hb using 1
    dsimp only [h]
    rw [← gamma_weight_mul a t ht']
    field_simp [hx.ne']
    ring
  have hmeas : AEStronglyMeasurable g μ := by
    have hc : ContinuousOn (hankelGammaWeight a) (Ioi (0 : ℝ)) :=
      continuous_neg.rexp.continuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl ht.ne')
    have hd : Continuous fun t : ℝ => hankelHalfPower ν (t / (2 * x)) - 1 :=
      ((continuous_hankelHalfPower ν).comp (by fun_prop)).sub continuous_const
    exact ContinuousOn.aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_continuousOn hc).mul hd.continuousOn) measurableSet_Ioi
  have hg : Integrable g μ := hi.mono' hmeas hbound
  have hgw : (fun t => w t * hankelHalfPower ν (t / (2 * x))) = fun t => g t + w t := by
    funext t
    dsimp only [g]
    ring
  have hnorm : ‖∫ t, g t ∂μ‖ ≤ (4 * x)⁻¹ * Real.Gamma (a + 1) := by
    calc
      ‖∫ t, g t ∂μ‖ ≤ ∫ t, h t ∂μ := norm_integral_le_of_norm_le hi hbound
      _ = _ := by
        dsimp only [h]
        rw [integral_const_mul, Real.Gamma_eq_integral (by linarith : 0 < a + 1)]
        rfl
  have hwval : (∫ t, w t ∂μ) = (Real.Gamma a : ℂ) := by
    rw [Real.Gamma_eq_integral ha]
    exact integral_complex_ofReal
  have heq : hankelGammaAmplitude ν x - 1 = (∫ t, g t ∂μ) / (Real.Gamma a : ℂ) := by
    change (∫ t, w t * hankelHalfPower ν (t / (2 * x)) ∂μ) / (Real.Gamma a : ℂ) - 1 = _
    rw [hgw, integral_add hg hw, hwval]
    rw [add_div, div_self hΓ₀, add_sub_cancel_right]
  rw [heq, norm_div, Complex.norm_of_nonneg hΓ.le]
  apply (div_le_iff₀ hΓ).2
  refine hnorm.trans_eq ?_
  rw [Real.Gamma_add_one ha.ne']
  change (4 * x)⁻¹ * (a * Real.Gamma a) = a / (4 * x) * Real.Gamma a
  ring

/-- The phase used in the first term of the asymptotic expansion of `J_ν(x)`. -/
def besselPhase (ν : ℕ) (x : ℝ) : ℝ := x - (ν : ℝ) * Real.pi / 2 - Real.pi / 4

/-- A Hankel–Gamma representation implies the exact first-omitted-term bound in (11).
The representation is the hypothesis `hrep`; this statement makes no identification of
the Gamma integral with the series definition of `J_ν` on its own. -/
theorem nemes_first_error_of_hankelGamma (ν : ℕ) (hν : ν = 0 ∨ ν = 1)
    {x : ℝ} (hx : 0 < x)
    (hrep : Real.sqrt (Real.pi * x / 2) * (besselJ ν (x : ℂ)).re =
      (Complex.exp ((besselPhase ν x : ℂ) * Complex.I) * hankelGammaAmplitude ν x).re) :
    |Real.sqrt (Real.pi * x / 2) * (besselJ ν (x : ℂ)).re - Real.cos (besselPhase ν x)| ≤
      |4 * (ν : ℝ) ^ 2 - 1| / (8 * x) := by
  let φ := besselPhase ν x
  let E := Complex.exp ((φ : ℂ) * Complex.I)
  have hEre : E.re = Real.cos φ := Complex.exp_ofReal_mul_I_re φ
  have hE : ‖E‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
  have hm : E * hankelGammaAmplitude ν x - E = E * (hankelGammaAmplitude ν x - 1) := by
    ring
  rw [hrep]
  change |(E * hankelGammaAmplitude ν x).re - Real.cos φ| ≤ _
  rw [← hEre, ← Complex.sub_re, hm]
  calc
    |(E * (hankelGammaAmplitude ν x - 1)).re| ≤ ‖E * (hankelGammaAmplitude ν x - 1)‖ :=
      Complex.abs_re_le_norm _
    _ = ‖hankelGammaAmplitude ν x - 1‖ := by rw [norm_mul, hE, one_mul]
    _ ≤ ((ν : ℝ) + 1 / 2) / (4 * x) := norm_hankelGammaAmplitude_sub_one_le ν hx
    _ = |4 * (ν : ℝ) ^ 2 - 1| / (8 * x) := by
      rcases hν with rfl | rfl <;> norm_num <;> field_simp [hx.ne'] <;> ring

open scoped ComplexOrder

private theorem sqrt_poisson_on_segment {t : ℝ} (ht : |t| ≤ 1) :
    Complex.sqrt (1 - (t : ℂ) ^ (2 : ℕ)) = (Real.sqrt (1 - t ^ 2) : ℂ) := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp ht
  have hn : 0 ≤ 1 - t ^ 2 := by
    have h := mul_nonneg (by linarith : 0 ≤ 1 + t) (by linarith : 0 ≤ 1 - t)
    nlinarith
  have hnC : (0 : ℂ) ≤ ((1 - t ^ 2 : ℝ) : ℂ) := (RCLike.ofReal_nonneg (K := ℂ)).mpr hn
  have h : Complex.sqrt (((1 - t ^ 2 : ℝ) : ℂ)) = (Real.sqrt (1 - t ^ 2) : ℂ) := by
    simpa only [Complex.ofReal_re] using Complex.sqrt_of_nonneg hnC
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using h

private theorem besselJ_one_eq_poisson (x : ℝ) :
    besselJ 1 (x : ℂ) = ((x : ℂ) / (Real.pi : ℂ)) *
      ∫ t : ℝ in (-1 : ℝ)..1, poissonKernel 1 x t := by
  have h := besselI_mul_I 1 (x : ℂ)
  rw [besselI_one_integral, pow_one] at h
  have hseg : (∫ t : ℝ in (-1 : ℝ)..1, poissonKernel 1 x t) =
      ∫ t : ℝ in (-1 : ℝ)..1, Complex.exp ((Complex.I * (x : ℂ)) * t) *
        (Real.sqrt (1 - t ^ 2) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    dsimp only
    simp [poissonKernel, sqrt_poisson_on_segment (abs_le.mpr ht), mul_comm Complex.I (x : ℂ)]
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [← h, hseg]
  ring

private theorem poissonKernel_left_eq_conj (ν : ℕ) (x y : ℝ) (hy : 0 < y) :
    poissonKernel ν x (-1 + (y : ℂ) * Complex.I) =
      conj (poissonKernel ν x (1 + (y : ℂ) * Complex.I)) := by
  have hp : 0 < (1 - (1 + (y : ℂ) * Complex.I) ^ (2 : ℕ)).re := by
    simp [pow_two, Complex.mul_re, Complex.mul_im, hy]
  have h := poissonKernel_neg_conj ν x hp
  rw [show -conj (1 + (y : ℂ) * Complex.I) = -1 + (y : ℂ) * Complex.I by
    simp [Complex.conj_I]; ring] at h
  exact h

private theorem poisson_integral_re_eq_right (ν : ℕ) {x δ : ℝ} (hx : 0 < x)
    (hδ : 0 ≤ δ) (hνδ : ν ≠ 0 ∨ 0 < δ) :
    (∫ t : ℝ in (-1 : ℝ)..1, poissonKernel ν x ((t : ℂ) + (δ : ℂ) * Complex.I)).re =
      2 * ((-Complex.I) * (∫ t in Ioi δ, poissonKernel ν x (1 + (t : ℂ) * Complex.I))).re := by
  have hl : (∫ t in Ioi δ, poissonKernel ν x (-1 + (t : ℂ) * Complex.I)) =
      conj (∫ t in Ioi δ, poissonKernel ν x (1 + (t : ℂ) * Complex.I)) := by
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact poissonKernel_left_eq_conj ν x t (hδ.trans_lt ht)
  have hc := integral_boundary_poissonKernel ν hx hδ hνδ
  rw [hl] at hc
  have hr := congrArg Complex.re hc
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub, Complex.conj_im, Complex.zero_re] at hr
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, zero_mul, neg_one_mul, sub_neg_eq_add, zero_add]
  linarith

private theorem exp_poisson_right_ray (x y : ℝ) :
  Complex.exp ((x : ℂ) * Complex.I * (1 + (y : ℂ) * Complex.I)) =
    Complex.exp ((x : ℂ) * Complex.I) * (Real.exp (-(x * y)) : ℂ) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_mul]
  congr 1
  calc
    (x : ℂ) * Complex.I * (1 + (y : ℂ) * Complex.I) =
        (x : ℂ) * Complex.I + (x : ℂ) * y * Complex.I ^ (2 : ℕ) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

private theorem poissonKernel_right_one (x y : ℝ) (hy : 0 < y) :
    poissonKernel 1 x (1 + (y : ℂ) * Complex.I) =
      (Complex.exp ((x : ℂ) * Complex.I) * (1 - Complex.I)) *
        ((Real.exp (-(x * y)) * Real.sqrt y : ℝ) : ℂ) * hankelHalfPower 1 (y / 2) := by
  have hexp := exp_poisson_right_ray x y
  simp only [poissonKernel, one_ne_zero, ite_false, hankelHalfPower, hexp,
    sqrt_poisson_right_ray hy, Complex.ofReal_mul]
  ring

private theorem poisson_integral_right_one {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), poissonKernel 1 x (1 + (t : ℂ) * Complex.I)) =
      (Complex.exp ((x : ℂ) * Complex.I) * (1 - Complex.I)) /
        ((x * Real.sqrt x : ℝ) : ℂ) * (Real.Gamma (1 + 1 / 2) : ℂ) * hankelGammaAmplitude 1 x := by
  let f : ℝ → ℂ := fun t => (hankelGammaWeight (1 + 1 / 2) t : ℂ) * hankelHalfPower 1 (t / (2 * x))
  let c := Complex.exp ((x : ℂ) * Complex.I) * (1 - Complex.I)
  have hΓ : (Real.Gamma (1 + 1 / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsxC : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpoint : ∀ y ∈ Ioi (0 : ℝ),
      poissonKernel 1 x (1 + (y : ℂ) * Complex.I) = (c / (Real.sqrt x : ℂ)) * f (x * y) := by
    intro y hy
    have hy' : 0 < y := hy
    have hyx : x * y / (2 * x) = y / 2 := by field_simp
    rw [poissonKernel_right_one x y hy']
    simp only [f, hankelGammaWeight, hyx, Complex.ofReal_mul]
    rw [show (1 + 1 / 2 : ℝ) - 1 = 1 / 2 by ring,
      ← Real.sqrt_eq_rpow, Real.sqrt_mul hx.le, Complex.ofReal_mul]
    field_simp [hsxC]
    ring
  calc
    (∫ t in Ioi (0 : ℝ), poissonKernel 1 x (1 + (t : ℂ) * Complex.I)) =
      ∫ y in Ioi (0 : ℝ), (c / (Real.sqrt x : ℂ)) * f (x * y) :=
        setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = (c / (Real.sqrt x : ℂ)) * ((x⁻¹ : ℝ) • (∫ t in Ioi (0 : ℝ), f t)) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi f 0 hx, mul_zero]
    _ = _ := by
      simp only [hankelGammaAmplitude, Nat.cast_one]
      change (c / (Real.sqrt x : ℂ)) * ((x⁻¹ : ℝ) • (∫ t in Ioi (0 : ℝ), f t)) =
        c / ((x * Real.sqrt x : ℝ) : ℂ) * (Real.Gamma (1 + 1 / 2) : ℂ) *
          ((∫ t in Ioi (0 : ℝ), f t) / (Real.Gamma (1 + 1 / 2) : ℂ))
      rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul]
      field_simp [hΓ, hxC, hsxC]

private theorem exp_neg_quarter_phase :
  Complex.exp (-((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - Complex.I) := by
  rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four,
    Complex.ofReal_neg]
  ring

private theorem exp_besselPhase_one (x : ℝ) :
    Complex.exp ((besselPhase 1 x : ℂ) * Complex.I) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
        ((-Complex.I) * (Complex.exp ((x : ℂ) * Complex.I) * (1 - Complex.I))) := by
  have h₂ : Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  have h₄ := exp_neg_quarter_phase
  simp only [besselPhase, Nat.cast_one, one_mul, Complex.ofReal_sub]
  rw [show ((x : ℂ) - ((Real.pi / 2 : ℝ) : ℂ) - ((Real.pi / 4 : ℝ) : ℂ)) * Complex.I =
    ((x : ℂ) * Complex.I + (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) +
      (-((Real.pi / 4 : ℝ) : ℂ) * Complex.I) by ring,
    Complex.exp_add, Complex.exp_add, h₂, h₄]
  ring

private theorem gamma_prefactor_one {x : ℝ} (hx : 0 < x) :
    Real.sqrt (Real.pi * x / 2) * (x / Real.pi) *
        (2 * (Real.Gamma (1 + 1 / 2) / (x * Real.sqrt x))) = Real.sqrt 2 / 2 := by
  have hΓ : Real.Gamma (1 + 1 / 2) = Real.sqrt Real.pi / 2 := by
    rw [add_comm (1 : ℝ) (1 / 2), Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hs₂ : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  calc
    _ = (Real.sqrt Real.pi) ^ 2 / (Real.pi * Real.sqrt 2) := by
      rw [Real.sqrt_div (mul_nonneg Real.pi_pos.le hx.le), Real.sqrt_mul Real.pi_pos.le, hΓ]
      field_simp [hx.ne', hsx, hs₂, Real.pi_ne_zero]
    _ = _ := by
      rw [Real.sq_sqrt Real.pi_pos.le]
      field_simp [Real.pi_ne_zero, hs₂]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Exact Hankel–Gamma representation of the normalized ordinary Bessel function at order one. -/
theorem besselJ_one_hankelGamma {x : ℝ} (hx : 0 < x) :
    Real.sqrt (Real.pi * x / 2) * (besselJ 1 (x : ℂ)).re =
      (Complex.exp ((besselPhase 1 x : ℂ) * Complex.I) * hankelGammaAmplitude 1 x).re := by
  let v := (-Complex.I) * (Complex.exp ((x : ℂ) * Complex.I) * (1 - Complex.I)) *
    hankelGammaAmplitude 1 x
  have hQ : (-Complex.I) * (∫ t in Ioi (0 : ℝ), poissonKernel 1 x (1 + (t : ℂ) * Complex.I)) =
      ((Real.Gamma (1 + 1 / 2) / (x * Real.sqrt x) : ℝ) : ℂ) * v := by
    rw [poisson_integral_right_one hx, Complex.ofReal_div]
    dsimp [v]
    ring
  have hP : Complex.exp ((besselPhase 1 x : ℂ) * Complex.I) * hankelGammaAmplitude 1 x =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) * v := by
    rw [exp_besselPhase_one]
    dsimp [v]
    ring
  have hR := poisson_integral_re_eq_right 1 hx (δ := 0) (by norm_num) (Or.inl one_ne_zero)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hR
  calc
    _ = (Real.sqrt (Real.pi * x / 2) * (x / Real.pi) *
        (2 * (Real.Gamma (1 + 1 / 2) / (x * Real.sqrt x)))) * v.re := by
      rw [besselJ_one_eq_poisson, ← Complex.ofReal_div, Complex.re_ofReal_mul, hR, hQ,
        Complex.re_ofReal_mul]
      ring
    _ = _ := by
      rw [gamma_prefactor_one hx, hP, Complex.re_ofReal_mul]

/-- Manuscript equation (11) at order one, proved via the Hankel–Gamma integral. -/
theorem nemes_first_error_one {x : ℝ} (hx : 0 < x) :
    |Real.sqrt (Real.pi * x / 2) * (besselJ 1 (x : ℂ)).re - Real.cos (besselPhase 1 x)| ≤
      3 / (8 * x) := by
  simpa only [Nat.cast_one, one_pow, mul_one, show |(4 : ℝ) - 1| = 3 by norm_num] using
    nemes_first_error_of_hankelGamma 1 (Or.inr rfl) hx (besselJ_one_hankelGamma hx)
private theorem besselJ_zero_eq_poisson (x : ℝ) :
    besselJ 0 (x : ℂ) = (Real.pi : ℂ)⁻¹ *
      ∫ t : ℝ in (-1 : ℝ)..1, poissonKernel 0 x t := by
  have h := besselI_mul_I 0 (x : ℂ)
  rw [besselI_zero_integral_segment, pow_zero, one_mul] at h
  rw [← h]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
  simp [poissonKernel, sqrt_poisson_on_segment (abs_le.mpr ht), mul_comm Complex.I (x : ℂ)]

private theorem poissonKernel_right_zero_scaled {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    poissonKernel 0 x (1 + (y : ℂ) * Complex.I) =
      (Complex.exp ((x : ℂ) * Complex.I) / (1 - Complex.I) * (Real.sqrt x : ℂ)) *
        ((hankelGammaWeight (1 / 2) (x * y) : ℂ) * hankelHalfPower 0 (x * y / (2 * x))) := by
  have hexp := exp_poisson_right_ray x y
  have hyx : x * y / (2 * x) = y / 2 := by field_simp
  have hsxC : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'
  have hsyC : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne'
  simp only [poissonKernel, ite_true, hankelHalfPower, hexp,
    sqrt_poisson_right_ray hy, hyx, hankelGammaWeight, Complex.ofReal_mul]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by ring, Real.rpow_neg (mul_nonneg hx.le hy.le),
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hx.le, Complex.ofReal_inv, Complex.ofReal_mul]
  rw [mul_inv_rev, mul_inv_rev, mul_inv_rev]
  simp only [div_eq_mul_inv]
  field_simp [hsxC, hsyC]

private theorem poisson_integral_right_zero {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), poissonKernel 0 x (1 + (t : ℂ) * Complex.I)) =
      (Complex.exp ((x : ℂ) * Complex.I) / (1 - Complex.I)) /
        (Real.sqrt x : ℂ) * (Real.Gamma (1 / 2) : ℂ) * hankelGammaAmplitude 0 x := by
  let f : ℝ → ℂ := fun t => (hankelGammaWeight (1 / 2) t : ℂ) * hankelHalfPower 0 (t / (2 * x))
  let c := Complex.exp ((x : ℂ) * Complex.I) / (1 - Complex.I)
  have hΓ : (Real.Gamma (1 / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hsxC : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hsq : (Real.sqrt x : ℂ) ^ (2 : ℕ) = (x : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hx.le]
  calc
    (∫ t in Ioi (0 : ℝ), poissonKernel 0 x (1 + (t : ℂ) * Complex.I)) =
      ∫ y in Ioi (0 : ℝ), (c * (Real.sqrt x : ℂ)) * f (x * y) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact poissonKernel_right_zero_scaled hx ht
    _ = (c * (Real.sqrt x : ℂ)) * ((x⁻¹ : ℝ) • (∫ t in Ioi (0 : ℝ), f t)) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi f 0 hx, mul_zero]
    _ = _ := by
      simp only [hankelGammaAmplitude, Nat.cast_zero, zero_add]
      change (c * (Real.sqrt x : ℂ)) * ((x⁻¹ : ℝ) • (∫ t in Ioi (0 : ℝ), f t)) =
        c / (Real.sqrt x : ℂ) * (Real.Gamma (1 / 2) : ℂ) *
          ((∫ t in Ioi (0 : ℝ), f t) / (Real.Gamma (1 / 2) : ℂ))
      rw [Complex.real_smul, Complex.ofReal_inv]
      field_simp [hΓ, hxC, hsxC]
      linear_combination c * (∫ t in Ioi (0 : ℝ), f t) * hsq

private theorem integrableOn_poissonKernel_right_zero {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => poissonKernel 0 x (1 + (t : ℂ) * Complex.I)) (Ioi 0) := by
  let d : ℂ := Complex.exp ((x : ℂ) * Complex.I) / (1 - Complex.I) * (Real.sqrt x : ℂ)
  have hW : IntegrableOn (hankelGammaWeight (1 / 2)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hW' : IntegrableOn (fun t => hankelGammaWeight (1 / 2) (x * t)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff _ 0 hx).mpr (by simpa only [mul_zero] using hW)
  have hmaj := hW'.const_mul ‖d‖
  refine hmaj.mono' (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi) ?_
  · intro t ht
    have ht' : 0 < t := ht
    have h₁ : |(1 + (t : ℂ) * Complex.I).re| ≤ 1 := by simp [Complex.mul_re]
    have h₂ : 0 < (1 + (t : ℂ) * Complex.I).im := by simpa [Complex.mul_im] using ht'
    have hct := (differentiableAt_poissonKernel 0 x h₁ h₂).continuousAt
    have hin : ContinuousAt (fun t : ℝ => 1 + (t : ℂ) * Complex.I) t := by fun_prop
    exact (hct.comp (f := fun t : ℝ => 1 + (t : ℂ) * Complex.I) hin).continuousWithinAt
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    have ht' : 0 < t := ht
    have hW₀ : 0 ≤ hankelGammaWeight (1 / 2) (x * t) := by unfold hankelGammaWeight; positivity
    have hhalf : ‖hankelHalfPower 0 (x * t / (2 * x))‖ ≤ 1 := by
      simp only [hankelHalfPower, ite_true, norm_inv]
      exact inv_le_one_of_one_le₀ ((re_sqrt_vertical_ge_one _).trans (Complex.re_le_norm _))
    change ‖poissonKernel 0 x (1 + (t : ℂ) * Complex.I)‖ ≤ ‖d‖ * hankelGammaWeight (1 / 2) (x * t)
    rw [poissonKernel_right_zero_scaled hx ht']
    change ‖d * ((hankelGammaWeight (1 / 2) (x * t) : ℂ) *
      hankelHalfPower 0 (x * t / (2 * x)))‖ ≤ _
    rw [norm_mul d, norm_mul ((hankelGammaWeight (1 / 2) (x * t) : ℝ) : ℂ),
      Complex.norm_of_nonneg hW₀]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hW₀ hhalf) (norm_nonneg _)

/-- The positive-height Poisson integrals converge to the real segment at order zero. -/
private theorem tendsto_poisson_integral_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ in (-1 : ℝ)..1,
      poissonKernel 0 x ((t : ℂ) + (δ : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ in (-1 : ℝ)..1, poissonKernel 0 x (t : ℂ))) := by
  let b (t : ℝ) := (Real.sqrt (1 - t ^ 2))⁻¹
  have ha : ∀ᵐ t ∂volume, t ∈ uIoc (-1 : ℝ) 1 → t ∈ Ioo (-1 : ℝ) 1 := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact (Ioo_ae_eq_Ioc (μ := volume) (a := (-1 : ℝ)) (b := 1)).mono (fun t h => h.mpr)
  have hb : IntervalIntegrable b volume (-1) 1 := by
    rw [intervalIntegrable_iff, uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    refine intervalIntegral.integrableOn_deriv_of_nonneg Real.continuous_arccos.neg.continuousOn
      (fun t ht => ?_) (by simp [b])
    simpa [b, one_div] using (Real.hasDerivAt_arccos (ne_of_gt ht.1) (ne_of_lt ht.2)).neg
  have hδ : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hp (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - t ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 + t by linarith [ht.1]) (show 0 < 1 - t by linarith [ht.2])]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence b ?_ ?_ hb ?_
  · filter_upwards [hδ] with δ hδ'
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
    intro t ht
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hc : ContinuousAt (poissonKernel 0 x) ((t : ℂ) + (δ : ℂ) * Complex.I) := by
      apply (differentiableAt_poissonKernel 0 x ?_ ?_).continuousAt
      · simpa [Complex.add_re, Complex.mul_re] using ht'
      · simpa [Complex.add_im, Complex.mul_im] using hδ'
    have hshift : ContinuousAt (fun t : ℝ => (t : ℂ) + (δ : ℂ) * Complex.I) t :=
      Complex.continuous_ofReal.continuousAt.add continuousAt_const
    exact (hc.comp (f := fun w : ℝ => (w : ℂ) + (δ : ℂ) * Complex.I)
      (x := t) hshift).continuousWithinAt
  · filter_upwards [hδ] with δ hδ'
    filter_upwards [ha] with t ht ht'
    have h := hp t (ht ht')
    have h₁ : 0 < 1 - t ^ 2 + δ ^ 2 := by positivity
    have h₂ := norm_poissonKernel_le 0 x ((t : ℂ) + (δ : ℂ) * Complex.I)
      (by simpa [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] using h₁)
    refine h₂.trans ?_
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, zero_add, add_zero]
    have hE : Real.exp (-(x * δ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx.le hδ'.le))
    have hsq : 1 - t ^ 2 ≤ 1 - t ^ 2 + δ ^ 2 := le_add_of_nonneg_right (sq_nonneg δ)
    have hs := inv_anti₀ (Real.sqrt_pos.2 h) (Real.sqrt_le_sqrt hsq)
    calc
      _ ≤ 1 * (Real.sqrt (1 - t ^ 2 + δ ^ 2))⁻¹ := mul_le_mul_of_nonneg_right hE (by positivity)
      _ ≤ _ := by simpa [b] using hs
  · filter_upwards [ha] with t ht ht'
    have hφ : 0 < (1 - (t : ℂ) ^ (2 : ℕ)).re := by
      simpa [Complex.sub_re, pow_two, Complex.mul_re] using (hp t (ht ht'))
    have hφ₀ : (1 - (t : ℂ) ^ (2 : ℕ)) ≠ 0 := by
      intro h
      simp [h] at hφ
    have hs₀ : Complex.sqrt (1 - (t : ℂ) ^ (2 : ℕ)) ≠ 0 := by
      intro hg
      have hs := sqrt_square_nonzero hφ₀
      rw [hg, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
      exact hφ₀ hs.symm
    have hφc : ContinuousAt (fun z : ℂ => 1 - z ^ (2 : ℕ)) (t : ℂ) := by fun_prop
    have hs : ContinuousAt (fun z : ℂ => Complex.sqrt (1 - z ^ (2 : ℕ))) (t : ℂ) :=
      ((Complex.differentiableAt_sqrt (Or.inl hφ)).continuousAt).comp
        (f := fun z : ℂ => 1 - z ^ (2 : ℕ)) (x := (t : ℂ)) hφc
    have hcont : ContinuousAt (poissonKernel 0 x) (t : ℂ) := by
      change ContinuousAt (fun w : ℂ => Complex.exp ((x : ℂ) * Complex.I * w) *
        (Complex.sqrt (1 - w ^ (2 : ℕ)))⁻¹) (t : ℂ)
      exact ContinuousAt.mul (by fun_prop) (hs.inv₀ hs₀)
    have hshift : ContinuousAt (fun δ : ℝ => (t : ℂ) + (δ : ℂ) * Complex.I) 0 :=
      continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have hshift' : Tendsto (fun δ : ℝ => (t : ℂ) + (δ : ℂ) * Complex.I)
        (𝓝[>] 0) (𝓝 (t : ℂ)) := by
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
        hshift.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    exact hcont.tendsto.comp hshift'

private theorem poisson_integral_zero_re_eq_right {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in (-1 : ℝ)..1, poissonKernel 0 x (t : ℂ)).re =
      2 * ((-Complex.I) * (∫ t in Ioi (0 : ℝ), poissonKernel 0 x (1 + (t : ℂ) * Complex.I))).re := by
  let C := ∫ t in Ioi (0 : ℝ), poissonKernel 0 x (1 + (t : ℂ) * Complex.I)
  have hc : Tendsto (fun δ : ℝ => ∫ t in Ioi δ, poissonKernel 0 x (1 + (t : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 C) := by
    have h := (integrableOn_poissonKernel_right_zero hx).continuousWithinAt_Ici_primitive_Ioi
    exact h.mono Ioi_subset_Ici_self |>.tendsto
  have hleft := (Complex.continuous_re.tendsto _).comp (tendsto_poisson_integral_zero x hx)
  have hρ : Continuous fun z : ℂ => 2 * ((-Complex.I) * z).re := by fun_prop
  have hright := (hρ.tendsto C).comp hc
  have he : (fun δ : ℝ => (∫ t : ℝ in (-1 : ℝ)..1,
      poissonKernel 0 x ((t : ℂ) + (δ : ℂ) * Complex.I)).re) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ => 2 * ((-Complex.I) * (∫ t in Ioi δ,
        poissonKernel 0 x (1 + (t : ℂ) * Complex.I))).re) := by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with δ hδ
    have h : 0 < δ := hδ
    exact poisson_integral_re_eq_right 0 hx h.le (Or.inr h)
  exact tendsto_nhds_unique (hleft.congr' he) hright

private theorem exp_besselPhase_zero (x : ℝ) :
    Complex.exp ((besselPhase 0 x : ℂ) * Complex.I) =
      (Real.sqrt 2 : ℂ) * ((-Complex.I) * (Complex.exp ((x : ℂ) * Complex.I) / (1 - Complex.I))) := by
  have h₄ := exp_neg_quarter_phase
  have hI : (1 - Complex.I : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
  have hsq : (1 - Complex.I) ^ (2 : ℕ) = -2 * Complex.I := by
    calc
      (1 - Complex.I) ^ (2 : ℕ) = 1 - 2 * Complex.I + Complex.I ^ (2 : ℕ) := by ring
      _ = -2 * Complex.I := by rw [Complex.I_sq]; ring
  have hhalf : (1 - Complex.I) / 2 = (-Complex.I) / (1 - Complex.I) := by
    apply (eq_div_iff hI).2
    calc
      (1 - Complex.I) / 2 * (1 - Complex.I) = (1 - Complex.I) ^ (2 : ℕ) / 2 := by ring
      _ = -Complex.I := by rw [hsq]; ring
  simp only [besselPhase, Nat.cast_zero, zero_mul, zero_div, sub_zero, Complex.ofReal_sub]
  rw [sub_mul, sub_eq_add_neg, Complex.exp_add, ← neg_mul, h₄, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  calc
    _ = (Real.sqrt 2 : ℂ) * (Complex.exp ((x : ℂ) * Complex.I) * ((1 - Complex.I) / 2)) := by ring
    _ = _ := by rw [hhalf]; ring

private theorem gamma_prefactor_zero {x : ℝ} (hx : 0 < x) :
    Real.sqrt (Real.pi * x / 2) * Real.pi⁻¹ *
        (2 * (Real.Gamma (1 / 2) / Real.sqrt x)) = Real.sqrt 2 := by
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hs₂ : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  calc
    _ = (Real.sqrt Real.pi) ^ 2 * 2 / (Real.pi * Real.sqrt 2) := by
      rw [Real.sqrt_div (mul_nonneg Real.pi_pos.le hx.le), Real.sqrt_mul Real.pi_pos.le,
        Real.Gamma_one_half_eq]
      field_simp [hsx, hs₂, Real.pi_ne_zero]
    _ = _ := by
      rw [Real.sq_sqrt Real.pi_pos.le]
      field_simp [Real.pi_ne_zero, hs₂]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Exact Hankel–Gamma representation of the normalized ordinary Bessel function at order zero. -/
theorem besselJ_zero_hankelGamma {x : ℝ} (hx : 0 < x) :
    Real.sqrt (Real.pi * x / 2) * (besselJ 0 (x : ℂ)).re =
      (Complex.exp ((besselPhase 0 x : ℂ) * Complex.I) * hankelGammaAmplitude 0 x).re := by
  let v := (-Complex.I) * (Complex.exp ((x : ℂ) * Complex.I) / (1 - Complex.I)) *
    hankelGammaAmplitude 0 x
  have hQ : (-Complex.I) * (∫ t in Ioi (0 : ℝ), poissonKernel 0 x (1 + (t : ℂ) * Complex.I)) =
      ((Real.Gamma (1 / 2) / Real.sqrt x : ℝ) : ℂ) * v := by
    rw [poisson_integral_right_zero hx, Complex.ofReal_div]
    dsimp [v]
    ring
  have hP : Complex.exp ((besselPhase 0 x : ℂ) * Complex.I) * hankelGammaAmplitude 0 x =
      (Real.sqrt 2 : ℂ) * v := by
    rw [exp_besselPhase_zero]
    dsimp [v]
    ring
  calc
    _ = (Real.sqrt (Real.pi * x / 2) * Real.pi⁻¹ *
        (2 * (Real.Gamma (1 / 2) / Real.sqrt x))) * v.re := by
      rw [besselJ_zero_eq_poisson, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
        poisson_integral_zero_re_eq_right hx, hQ, Complex.re_ofReal_mul]
      ring
    _ = _ := by
      rw [gamma_prefactor_zero hx, hP, Complex.re_ofReal_mul]
/-- Manuscript equation (11) at orders zero and one for every positive real argument. -/
theorem nemes_first_error (ν : ℕ) (hν : ν = 0 ∨ ν = 1) {x : ℝ} (hx : 0 < x) :
    |Real.sqrt (Real.pi * x / 2) * (besselJ ν (x : ℂ)).re - Real.cos (besselPhase ν x)| ≤
      |4 * (ν : ℝ) ^ 2 - 1| / (8 * x) := by
  apply nemes_first_error_of_hankelGamma ν hν hx
  rcases hν with rfl | rfl
  · exact besselJ_zero_hankelGamma hx
  · exact besselJ_one_hankelGamma hx
end DurfeeCCS.Step06
