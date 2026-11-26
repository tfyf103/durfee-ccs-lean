module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import DurfeeCCS.Step08.SaddleBesselAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The angular substitution at the central saddle. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Set MeasureTheory intervalIntegral

/-- The angular boundary corresponding to the cutoff at `ψ = 0.3`. -/
def saddleBesselCutoff : ℝ := Real.arccos 0.7

theorem saddleBesselCutoff_nonneg : 0 ≤ saddleBesselCutoff := Real.arccos_nonneg _

theorem saddleBesselCutoff_le : saddleBesselCutoff ≤ Real.pi / 2 :=
  Real.arccos_le_pi_div_two.mpr (by norm_num)

/-- Substitution of `ψ = 1 - cos θ` on the symmetric central arc, including the
factor from its two halves. This gives the Jacobian in (36). -/
theorem integral_saddleBessel_angle_change (f : ℝ → ℂ) (hf : Continuous f) (heven : Function.Even f)
    {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ Real.pi / 2) :
    (∫ θ in -c..c, f θ) = (Real.sqrt 2 : ℂ) *
      ∫ ψ in (0 : ℝ)..(1 - Real.cos c),
        f (Real.arccos (1 - ψ)) / ((Real.sqrt ψ * Real.sqrt (1 - ψ / 2) : ℝ) : ℂ) := by
  let x (θ : ℝ) := 1 - Real.cos θ
  let g (ψ : ℝ) := f (Real.arccos (1 - ψ)) /
    ((Real.sqrt ψ * Real.sqrt (1 - ψ / 2) : ℝ) : ℂ)
  have hx : Continuous x := continuous_const.sub Real.continuous_cos
  have hxd (θ : ℝ) : HasDerivAt x (Real.sin θ) θ := by
    simpa [x] using (Real.hasDerivAt_cos θ).const_sub (1 : ℝ)
  have hcp : c ≤ Real.pi := by linarith [Real.pi_pos]
  have hs (θ : ℝ) (hθ : θ ∈ Ioo (min 0 c) (max 0 c)) : 0 ≤ Real.sin θ := by
    rw [min_eq_left hc, max_eq_right hc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (hθ.2.le.trans hcp)
  have hsub := integral_deriv_smul_comp_of_deriv_nonneg (a := 0) (b := c) (g := g)
    hx.continuousOn (fun θ _ => hxd θ) hs
  have hfore : (∫ θ in (0 : ℝ)..c, Real.sin θ • (g ∘ x) θ) =
      (Real.sqrt 2 : ℂ) * ∫ θ in (0 : ℝ)..c, f θ := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr_Ioo_of_le hc
    intro θ hθ
    have hθπ : θ ≤ Real.pi := hθ.2.le.trans hcp
    have ht : 0 < x θ := by
      have ht' := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ hθ.1
      rw [Real.cos_zero] at ht'
      exact sub_pos.mpr ht'
    have hcθ : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le.trans hc'⟩
    have ht' : 0 < 1 - x θ / 2 := by dsimp [x]; linarith
    have hsin : Real.sin θ = Real.sqrt 2 * (Real.sqrt (x θ) * Real.sqrt (1 - x θ / 2)) := by
      rw [Real.sin_eq_sqrt_one_sub_cos_sq hθ.1.le hθπ,
        ← Real.sqrt_mul ht.le, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      dsimp [x]
      ring
    have harc : Real.arccos (1 - x θ) = θ := by
      rw [show 1 - x θ = Real.cos θ by dsimp [x]; ring, Real.arccos_cos hθ.1.le hθπ]
    have hn : ((Real.sqrt (x θ) * Real.sqrt (1 - x θ / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (Real.sqrt_pos.mpr ht) (Real.sqrt_pos.mpr ht')).ne'
    simp only [Function.comp_apply, g, harc, Complex.real_smul, hsin, Complex.ofReal_mul]
    push_cast at hn
    rw [mul_assoc, mul_div_cancel₀ _ hn]
  rw [show x 0 = 0 by simp [x], hfore] at hsub
  have hleft : (∫ θ in -c..(0 : ℝ), f θ) = ∫ θ in (0 : ℝ)..c, f θ := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := c) f
    rw [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    exact fun θ _ => heven θ
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num), Complex.ofReal_ofNat]
  change (∫ θ in -c..c, f θ) = (Real.sqrt 2 : ℂ) * ∫ ψ in (0 : ℝ)..x c, g ψ
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-c) 0)
    (hf.intervalIntegrable 0 c), hleft, ← hsub, ← mul_assoc, hsq]
  ring

end DurfeeCCS.Step08
