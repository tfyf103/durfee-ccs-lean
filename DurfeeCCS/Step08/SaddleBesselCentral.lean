module

public import DurfeeCCS.Step08.SaddleBesselLaplace
public import DurfeeCCS.Step08.SaddleBesselRadicals
public import DurfeeCCS.Step07.FirstSaddleErrors
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-! The half-integer Gamma integrals in the error budget of Lemma 3.4. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Set MeasureTheory DurfeeCCS.Step06 DurfeeCCS.Step07

private theorem bessel_argument_factor_le {ω : ℝ} {z : ℂ} (hω : 0 < ω)
    (hnorm : ‖z‖ ≤ 3.35 * ω) (hre : 1.35 * ω ≤ z.re) :
    3 * ‖z‖ ^ (3 / 2 : ℝ) / (4 * z.re ^ (5 / 2 : ℝ)) ≤ 2.2 / ω := by
  have hz : 0 < z.re := (show 0 < 1.35 * ω by positivity).trans_le hre
  rw [div_le_div_iff₀ (by positivity) hω]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have h₁ : (‖z‖ ^ (3 / 2 : ℝ)) ^ 2 = ‖z‖ ^ 3 := by
    rw [← Real.rpow_natCast (‖z‖ ^ (3 / 2 : ℝ)), ← Real.rpow_mul (norm_nonneg _)]
    norm_num [Real.rpow_natCast]
  have h₂ : (z.re ^ (5 / 2 : ℝ)) ^ 2 = z.re ^ 5 := by
    rw [← Real.rpow_natCast (z.re ^ (5 / 2 : ℝ)), ← Real.rpow_mul hz.le]
    norm_num [Real.rpow_natCast]
  simp only [mul_pow, h₁, h₂]
  calc
    _ ≤ 3 ^ 2 * (3.35 * ω) ^ 3 * ω ^ 2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 3) (by norm_num))
      (sq_nonneg _)
    _ ≤ (2.2 : ℝ) ^ 2 * (4 ^ 2 * (1.35 * ω) ^ 5) := by
      have h := mul_le_mul_of_nonneg_right
        (show (3 : ℝ) ^ 2 * 3.35 ^ 3 ≤ 2.2 ^ 2 * (4 ^ 2 * 1.35 ^ 5) by norm_num)
        (show 0 ≤ ω ^ 5 by positivity)
      convert h using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hre 5) (by norm_num))
      (by norm_num)

/-- The order-one Bessel approximation with the central-arc relative constant. -/
theorem besselI_one_central_error {ω : ℝ} {z : ℂ} (hω : 0 < ω)
    (hnorm : ‖z‖ ≤ 3.35 * ω) (hre : 1.35 * ω ≤ z.re) :
    ‖besselI 1 z - Complex.exp z / Complex.sqrt (2 * (Real.pi : ℂ) * z)‖ ≤
      ‖Complex.exp z / Complex.sqrt (2 * (Real.pi : ℂ) * z)‖ * (2.2 / ω) := by
  have hz : 0 < z.re := (show 0 < 1.35 * ω by positivity).trans_le hre
  have hnorm_eq :
      ‖Complex.exp z / Complex.sqrt (2 * (Real.pi : ℂ) * z)‖ =
        Real.exp z.re / Real.sqrt (2 * Real.pi * ‖z‖) := by
    rw [norm_div, Complex.norm_exp, norm_principalSqrt, norm_mul, norm_mul]
    norm_num [Complex.norm_of_nonneg Real.pi_pos.le]
  rw [hnorm_eq]
  exact (besselI_one_half_plane_error hz).trans
    (mul_le_mul_of_nonneg_left (bessel_argument_factor_le hω hnorm hre) (by positivity))

/-- The central-arc error density after comparison with the linear exponent. -/
def saddleCentralErrorDensity (ω γ ψ : ℝ) : ℝ :=
  Real.exp (-(γ * ω) * ψ) * ψ ^ (-1 / 2 : ℝ) *
    (2.46 * ω * ψ ^ 2 + 0.87 * ψ + 2.7742 / ω)

private theorem saddleCentralErrorDensity_expand (ω γ ψ : ℝ) (hψ : 0 < ψ) :
    saddleCentralErrorDensity ω γ ψ =
      (2.46 * ω) * (Real.exp (-(γ * ω) * ψ) * ψ ^ (3 / 2 : ℝ)) +
      0.87 * (Real.exp (-(γ * ω) * ψ) * ψ ^ (1 / 2 : ℝ)) +
      (2.7742 / ω) * (Real.exp (-(γ * ω) * ψ) * ψ ^ (-1 / 2 : ℝ)) := by
  unfold saddleCentralErrorDensity
  rw [show (3 / 2 : ℝ) = -1 / 2 + 2 by norm_num, Real.rpow_add hψ, Real.rpow_two,
    show (1 / 2 : ℝ) = -1 / 2 + 1 by norm_num, Real.rpow_add hψ, Real.rpow_one]
  ring

theorem integrable_saddleCentralErrorDensity {ω γ : ℝ} (hω : 0 < ω) (hγ : 0 < γ) :
    IntegrableOn (saddleCentralErrorDensity ω γ) (Ioi 0) := by
  have ha := mul_pos hγ hω
  have h₀ := (real_laplace_moment_integrable ha (p := -1 / 2) (by norm_num)).const_mul
    (2.7742 / ω)
  have h₁ := (real_laplace_moment_integrable ha (p := 1 / 2) (by norm_num)).const_mul 0.87
  have h₂ := (real_laplace_moment_integrable ha (p := 3 / 2) (by norm_num)).const_mul (2.46 * ω)
  refine ((h₂.add h₁).add h₀).congr ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with ψ hψ
  exact (saddleCentralErrorDensity_expand ω γ ψ hψ).symm

/-- The central error polynomial integrates to the exact coefficient in the paper. -/
theorem integral_saddleCentralErrorDensity {ω γ : ℝ} (hω : 0 < ω) (hγ : 0 < γ) :
    Real.sqrt (1.5 * ω / Real.pi) *
      (∫ ψ in Ioi 0, saddleCentralErrorDensity ω γ ψ) = firstSaddleC γ / ω := by
  let a := γ * ω
  have ha : 0 < a := mul_pos hγ hω
  have h₀ := real_laplace_moment_integrable ha (p := -1 / 2) (by norm_num)
  have h₁ := real_laplace_moment_integrable ha (p := 1 / 2) (by norm_num)
  have h₂ := real_laplace_moment_integrable ha (p := 3 / 2) (by norm_num)
  have hsplit : (∫ ψ in Ioi 0, saddleCentralErrorDensity ω γ ψ) =
      (2.46 * ω) * (∫ ψ in Ioi 0, Real.exp (-a * ψ) * ψ ^ (3 / 2 : ℝ)) +
      0.87 * (∫ ψ in Ioi 0, Real.exp (-a * ψ) * ψ ^ (1 / 2 : ℝ)) +
      (2.7742 / ω) * (∫ ψ in Ioi 0, Real.exp (-a * ψ) * ψ ^ (-1 / 2 : ℝ)) := by
    calc
      _ = ∫ ψ in Ioi 0, ((2.46 * ω) * (Real.exp (-a * ψ) * ψ ^ (3 / 2 : ℝ)) +
          0.87 * (Real.exp (-a * ψ) * ψ ^ (1 / 2 : ℝ))) +
          (2.7742 / ω) * (Real.exp (-a * ψ) * ψ ^ (-1 / 2 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        exact fun ψ hψ => saddleCentralErrorDensity_expand ω γ ψ hψ
      _ = _ := by
        have hsum := integral_add ((h₂.const_mul (2.46 * ω)).add (h₁.const_mul 0.87))
          (h₀.const_mul (2.7742 / ω))
        simp only [Pi.add_apply] at hsum
        rw [hsum, integral_add (h₂.const_mul (2.46 * ω)) (h₁.const_mul 0.87)]
        simp only [integral_const_mul]
  have hind : (∫ ψ in Ioi 0, saddleCentralErrorDensity ω γ ψ) =
      (Real.sqrt Real.pi / Real.sqrt a) *
        (1.845 / γ ^ 2 + 0.435 / γ + 2.7742) / ω := by
    rw [hsplit, integral_laplace_rpow_real ha (show -1 < (3 / 2 : ℝ) by norm_num),
      integral_laplace_rpow_real ha (show -1 < (1 / 2 : ℝ) by norm_num),
      integral_laplace_rpow_real ha (show -1 < (-1 / 2 : ℝ) by norm_num),
      show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num, gamma_five_halves,
      show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, gamma_three_halves,
      show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.Gamma_one_half_eq,
      show (5 / 2 : ℝ) = 1 / 2 + 2 by norm_num, Real.rpow_add ha, Real.rpow_two,
      show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add ha, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have hs := (Real.sqrt_pos.mpr ha).ne'
    dsimp [a] at hs ⊢
    field_simp
    ring
  rw [hind, firstSaddleC, Real.sqrt_div (by positivity : 0 ≤ 1.5 * ω),
    Real.sqrt_mul (by norm_num : 0 ≤ (1.5 : ℝ))]
  rw [show a = γ * ω by rfl, Real.sqrt_mul hγ.le]
  have hπ := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hω' := (Real.sqrt_pos.mpr hω).ne'
  have hγ' := (Real.sqrt_pos.mpr hγ).ne'
  field_simp

/-- Restricting the central error integral to the cutoff only reduces its mass. -/
theorem integral_saddleCentralErrorDensity_truncated {ω γ : ℝ} (hω : 0 < ω) (hγ : 0 < γ) :
    Real.sqrt (1.5 * ω / Real.pi) *
      (∫ ψ in (0 : ℝ)..0.3, saddleCentralErrorDensity ω γ ψ) ≤ firstSaddleC γ / ω := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_saddleCentralErrorDensity hω hγ]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hsub : Ioc (0 : ℝ) 0.3 ⊆ Ioi 0 := fun _ h => h.1
  apply setIntegral_mono_set (integrable_saddleCentralErrorDensity hω hγ) _
    (Filter.Eventually.of_forall hsub)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with ψ hψ
  have hψ' : 0 < ψ := hψ
  unfold saddleCentralErrorDensity
  positivity

/-- The normalized linear-model tail beyond the cutoff at `0.3`. -/
theorem saddleModel_tail_le {ω γ : ℝ} (hω : 0 < ω) (hγ : 0.55 ≤ γ) :
    Real.sqrt (1.5 * ω / Real.pi) *
      (∫ ψ in Ioi (0.3 : ℝ), Real.exp (-(γ * ω) * ψ) / Real.sqrt ψ) ≤
          (2.4 / Real.sqrt ω) * Real.exp (-0.3 * γ * ω) := by
  let a := γ * ω
  have hγ' : 0 < γ := (by norm_num : (0 : ℝ) < 0.55).trans_le hγ
  have ha : 0 < a := mul_pos hγ' hω
  have h03 : 0 < Real.sqrt 0.3 := Real.sqrt_pos.mpr (by norm_num)
  have hω' : 0 < Real.sqrt ω := Real.sqrt_pos.mpr hω
  have hi : IntegrableOn (fun ψ : ℝ => Real.exp (-a * ψ) / Real.sqrt 0.3)
      (Ioi 0.3) := by
    exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0.3).div_const (Real.sqrt 0.3)
  have hbound : (∫ ψ in Ioi (0.3 : ℝ), Real.exp (-a * ψ) / Real.sqrt ψ) ≤
      ∫ ψ in Ioi (0.3 : ℝ), Real.exp (-a * ψ) / Real.sqrt 0.3 := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with ψ hψ
    have hψ' : (0.3 : ℝ) < ψ := hψ
    rw [Real.norm_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (Real.exp_nonneg _) h03 (Real.sqrt_le_sqrt hψ'.le)
  have hval : (∫ ψ in Ioi (0.3 : ℝ), Real.exp (-a * ψ) / Real.sqrt 0.3) =
      (Real.exp (-a * 0.3) / a) / Real.sqrt 0.3 := by
    simp only [div_eq_mul_inv, integral_mul_const]
    rw [integral_exp_mul_Ioi (neg_neg_of_pos ha), neg_div_neg_eq, div_eq_mul_inv]
  have hroot : Real.sqrt (1.5 * ω / Real.pi) =
      Real.sqrt (5 / Real.pi) * Real.sqrt 0.3 * Real.sqrt ω := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 5 / Real.pi),
      ← Real.sqrt_mul (by positivity : 0 ≤ 5 / Real.pi * 0.3)]
    congr 1
    ring
  have hc : Real.sqrt (5 / Real.pi) / γ ≤ 2.4 := by
    apply (div_le_iff₀ hγ').mpr
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hb : 5 / Real.pi ≤ (5 / 3 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_three.le
    refine hb.trans ?_
    have hg : (1.32 : ℝ) ≤ 2.4 * γ := by linarith
    exact (show (5 / 3 : ℝ) ≤ 1.32 ^ 2 by norm_num).trans
      (pow_le_pow_left₀ (by norm_num) hg 2)
  calc
    _ ≤ Real.sqrt (1.5 * ω / Real.pi) * ((Real.exp (-a * 0.3) / a) / Real.sqrt 0.3) :=
      mul_le_mul_of_nonneg_left (hbound.trans_eq hval) (by positivity)
    _ = (Real.sqrt (5 / Real.pi) / γ / Real.sqrt ω) * Real.exp (-0.3 * γ * ω) := by
      rw [hroot, show -a * 0.3 = -0.3 * γ * ω by dsimp [a]; ring]
      have hsq := Real.sq_sqrt hω.le
      dsimp [a]
      field_simp
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hc hω'.le) (Real.exp_nonneg _)

end DurfeeCCS.Step08
