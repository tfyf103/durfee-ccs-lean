module

public import DurfeeCCS.Step06.BesselIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! The Gamma-integral envelope for the order-two modified Bessel function. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Step06 Set MeasureTheory intervalIntegral

/-- The leading exponential envelope for the order-two Bessel function. -/
def outerBesselEnvelope (x : ℝ) : ℝ := Real.exp x / Real.sqrt (2 * Real.pi * x)

private theorem rpow_three_halves {a : ℝ} (ha : 0 ≤ a) :
    a ^ (3 / 2 : ℝ) = a * Real.sqrt a := by
  rcases ha.eq_or_lt with he | hp
  · rw [← he, Real.zero_rpow (by norm_num)]; simp
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one,
      ← Real.sqrt_eq_rpow]

private def gammaWeight (ν x : ℝ) : ℝ := Real.exp (-x) * x ^ ν

private def outerGammaWeight (x u : ℝ) : ℝ :=
  gammaWeight (3 / 2) u * max 0 (1 - u / (2 * x)) ^ (3 / 2 : ℝ)

private theorem continuous_outerGammaWeight (x : ℝ) : Continuous (outerGammaWeight x) := by
  unfold outerGammaWeight gammaWeight
  fun_prop

private theorem outerGammaWeight_zero {x u : ℝ} (hx : 0 < x) (hu : 2 * x ≤ u) :
    outerGammaWeight x u = 0 := by
  have h : 1 - u / (2 * x) ≤ 0 := by
    have h' := (le_div_iff₀ (show 0 < 2 * x by positivity)).mpr
      (show 1 * (2 * x) ≤ u by simpa using hu)
    linarith
  simp [outerGammaWeight, max_eq_left h, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]

private theorem outerGammaWeight_bounds {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    gammaWeight (3 / 2) u * (1 - 3 * u / (4 * x)) ≤ outerGammaWeight x u ∧
      outerGammaWeight x u ≤ gammaWeight (3 / 2) u := by
  have hg : 0 ≤ gammaWeight (3 / 2) u := by unfold gammaWeight; positivity
  let a : ℝ := max 0 (1 - u / (2 * x))
  have hA : 0 ≤ a := le_max_left ..
  have hA' : a ≤ 1 := max_le (by norm_num) (by linarith [div_nonneg hu.le (by positivity : 0 ≤ 2*x)])
  have hl : 1 - 3 * u / (4 * x) ≤ 3 * a / 2 - 1 / 2 := by
    have hAL : 1 - u / (2 * x) ≤ a := le_max_right ..
    linarith [show 3 * u / (4 * x) = 3 / 2 * (u / (2 * x)) by ring]
  have hr : 3 * a / 2 - 1 / 2 ≤ a ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves hA]
    have hs := Real.sq_sqrt hA
    have hs₀ := Real.sqrt_nonneg a
    nlinarith [mul_nonneg (sq_nonneg (Real.sqrt a - 1)) (show 0 ≤ 2 * Real.sqrt a + 1 by positivity),
      congrArg (· * Real.sqrt a) hs]
  have hr' : a ^ (3 / 2 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow hA hA' (by norm_num : (0 : ℝ) ≤ 3 / 2)
  change gammaWeight (3 / 2) u * (1 - 3 * u / (4 * x)) ≤ gammaWeight (3 / 2) u * a ^ (3 / 2 : ℝ) ∧
    gammaWeight (3 / 2) u * a ^ (3 / 2 : ℝ) ≤ gammaWeight (3 / 2) u
  exact ⟨mul_le_mul_of_nonneg_left (hl.trans hr) hg,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr' hg⟩

private theorem besselI_two_gamma {x : ℝ} (hx : 0 < x) :
    (besselI 2 (x : ℂ)).re = outerBesselEnvelope x * (4 / (3 * Real.sqrt Real.pi)) *
      (∫ u in Ioi (0 : ℝ), outerGammaWeight x u) := by
  let f : ℝ → ℝ := fun t => Real.exp (x * t) * (1 - t ^ 2) ^ (3 / 2 : ℝ)
  let g : ℝ → ℝ := fun u => 1 - u / x
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg (u : ℝ) : HasDerivAt g (-(x⁻¹)) u := by
    exact (hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).div_const x) |>.congr_deriv (by simp)
  have hsub := integral_deriv_smul_comp (a := (0 : ℝ)) (b := 2 * x)
    (fun u _ => hg u) (continuousOn_const (c := -(x⁻¹))) hf
  have h₀ : g 0 = 1 := by simp [g]
  have h₂ : g (2 * x) = -1 := by dsimp [g]; field_simp; norm_num
  rw [h₀, h₂, integral_symm (-1 : ℝ) 1] at hsub
  simp only [smul_eq_mul, Function.comp_apply] at hsub
  rw [intervalIntegral.integral_const_mul, neg_mul] at hsub
  have hpoint (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) (2 * x)) :
      f (g u) = (Real.exp x * (2 / x) ^ (3 / 2 : ℝ)) * outerGammaWeight x u := by
    rw [uIcc_of_le (show 0 ≤ 2 * x by positivity)] at hu
    have hU : 0 ≤ 1 - u / (2 * x) := sub_nonneg.mpr
      ((div_le_one (show 0 < 2*x by positivity)).mpr hu.2)
    have hp : 1 - g u ^ 2 = (2 / x) * u * (1 - u / (2 * x)) := by
      dsimp [g]
      field_simp
      <;> ring
    have hE : x * g u = x + -u := by dsimp [g]; field_simp; ring
    change Real.exp (x * g u) * (1 - g u ^ 2) ^ (3 / 2 : ℝ) = _
    rw [hE, Real.exp_add, hp, Real.mul_rpow (mul_nonneg (by positivity) hu.1) hU,
      Real.mul_rpow (by positivity) hu.1, outerGammaWeight, gammaWeight, max_eq_right hU]
    ring
  have hInt : (∫ t in (-1 : ℝ)..1, f t) =
      (Real.exp x * (2 / x) ^ (3 / 2 : ℝ)) / x *
        (∫ u in Ioi (0 : ℝ), outerGammaWeight x u) := by
    have hh : (∫ u in (0 : ℝ)..2 * x, f (g u)) =
        ∫ u in (0 : ℝ)..2 * x, (Real.exp x * (2 / x) ^ (3 / 2 : ℝ)) * outerGammaWeight x u :=
      intervalIntegral.integral_congr hpoint
    rw [hh, intervalIntegral.integral_const_mul] at hsub
    have hz : (∫ u in Ioi (0 : ℝ), outerGammaWeight x u) = ∫ u in Ioc (0 : ℝ) (2 * x), outerGammaWeight x u :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ hu => hu.1)
        (fun u hu => outerGammaWeight_zero hx (by
          by_contra! hab
          exact hu.2 ⟨hu.1, hab.le⟩))
    rw [integral_of_le (show (0 : ℝ) ≤ 2 * x by positivity), ← hz] at hsub
    rw [div_eq_mul_inv]
    linarith [hsub]
  have heq : (besselI 2 (x : ℂ)).re = x ^ 2 / (3 * Real.pi) * (∫ t in (-1 : ℝ)..1, f t) := by
    rw [besselI_two_integral]
    have hreal : (((x ^ 2 / (3 * Real.pi) : ℝ) : ℂ)) = (x : ℂ) ^ 2 / (3 * (Real.pi : ℂ)) := by push_cast; rfl
    rw [← hreal]
    simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hroot : Real.sqrt (2 / x) * Real.sqrt (2 * Real.pi * x) = 2 * Real.sqrt Real.pi := by
    have he : 2 / x * (2 * Real.pi * x) = 4 * Real.pi := by field_simp; ring
    rw [← Real.sqrt_mul (by positivity), he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [heq, hInt, rpow_three_halves (by positivity), outerBesselEnvelope, ← mul_assoc]
  congr 1
  have hπ : 0 < Real.sqrt Real.pi := by positivity
  have h2πx : 0 < Real.sqrt (2 * Real.pi * x) := by positivity
  field_simp [hx.ne', hπ.ne', h2πx.ne', Real.pi_ne_zero]
  rw [show x * Real.pi * 2 = 2 * Real.pi * x by ring]
  rw [mul_assoc 2 (Real.sqrt (2 / x)) (Real.sqrt (2 * Real.pi * x)), hroot]
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

private theorem gammaWeight_integrable {ν : ℝ} (hν : -1 < ν) :
    IntegrableOn (gammaWeight ν) (Ioi (0 : ℝ)) := by
  change IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ν) (Ioi 0)
  simpa using Real.GammaIntegral_convergent (show 0 < ν + 1 by linarith)

private theorem gammaWeight_integral (ν : ℝ) (hν : -1 < ν) :
    (∫ u in Ioi (0 : ℝ), gammaWeight ν u) = Real.Gamma (ν + 1) := by
  rw [Real.Gamma_eq_integral (show 0 < ν + 1 by linarith)]
  simp [gammaWeight]

private theorem gammaWeight_five_halves :
    (∫ u in Ioi (0 : ℝ), gammaWeight (5 / 2) u) = 15 * Real.sqrt Real.pi / 8 := by
  rw [gammaWeight_integral _ (by norm_num), show (5 / 2 + 1 : ℝ) = (3 / 2 + 1) + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (3 / 2 + 1 : ℝ) ≠ 0),
    Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0),
    show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  ring

private theorem gammaWeight_three_halves :
    (∫ u in Ioi (0 : ℝ), gammaWeight (3 / 2) u) = 3 * Real.sqrt Real.pi / 4 := by
  rw [gammaWeight_integral _ (by norm_num), Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0),
    show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  ring

/-- The two-sided first-order estimate for I₂(x) used in Lemma 4.2. -/
theorem besselI_two_asymptotic_bounds {x : ℝ} (hx : 0 < x) :
    outerBesselEnvelope x * (1 - 15 / (8 * x)) ≤ (besselI 2 (x : ℂ)).re ∧
      (besselI 2 (x : ℂ)).re ≤ outerBesselEnvelope x := by
  let c : ℝ := 3 / (4 * x)
  let μ := volume.restrict (Ioi (0 : ℝ))
  have h₁ := gammaWeight_integrable (show -1 < (3 / 2 : ℝ) by norm_num)
  have h₂ := gammaWeight_integrable (show -1 < (5 / 2 : ℝ) by norm_num)
  have hI : Integrable (outerGammaWeight x) μ := by
    refine Integrable.mono' h₁ ((continuous_outerGammaWeight x).aestronglyMeasurable) ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Filter.Eventually.of_forall fun u hu => by
      have hu₀ : 0 < u := hu
      have hn : 0 ≤ outerGammaWeight x u := by unfold outerGammaWeight gammaWeight; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact (outerGammaWeight_bounds hx hu₀).2
  have hl (u : ℝ) (hu : 0 < u) :
      gammaWeight (3 / 2) u - c * gammaWeight (5 / 2) u =
        gammaWeight (3 / 2) u * (1 - 3 * u / (4 * x)) := by
    have he : u ^ (5 / 2 : ℝ) = u ^ (3 / 2 : ℝ) * u := by
      rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hu, Real.rpow_one]
    simp only [gammaWeight, he, c]
    ring
  have ht₁ := integral_mono_ae (μ := μ) (h₁.sub (h₂.const_mul c)) hI
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => by
      dsimp
      rw [hl u hu]
      exact (outerGammaWeight_bounds hx hu).1))
  have ht₂ := integral_mono_ae hI h₁
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu =>
      (outerGammaWeight_bounds hx hu).2))
  change (∫ u in Ioi (0 : ℝ), gammaWeight (3 / 2) u - c * gammaWeight (5 / 2) u) ≤ _ at ht₁
  rw [MeasureTheory.integral_sub h₁ (h₂.const_mul c), MeasureTheory.integral_const_mul] at ht₁
  change (∫ u in Ioi (0 : ℝ), gammaWeight (3 / 2) u) -
    c * (∫ u in Ioi (0 : ℝ), gammaWeight (5 / 2) u) ≤
      (∫ u in Ioi (0 : ℝ), outerGammaWeight x u) at ht₁
  change (∫ u in Ioi (0 : ℝ), outerGammaWeight x u) ≤
    (∫ u in Ioi (0 : ℝ), gammaWeight (3 / 2) u) at ht₂
  rw [gammaWeight_three_halves, gammaWeight_five_halves] at ht₁
  rw [gammaWeight_three_halves] at ht₂
  rw [besselI_two_gamma hx]
  have hp : 0 < outerBesselEnvelope x * (4 / (3 * Real.sqrt Real.pi)) := by
    unfold outerBesselEnvelope
    positivity
  have hπ : 0 < Real.sqrt Real.pi := by positivity
  constructor
  · refine le_trans ?_ (mul_le_mul_of_nonneg_left ht₁ hp.le)
    dsimp [c]
    field_simp [hπ.ne', hx.ne']
    ring_nf
    exact le_rfl
  · refine (mul_le_mul_of_nonneg_left ht₂ hp.le).trans_eq ?_
    field_simp [hπ.ne']

end DurfeeCCS.Step10
