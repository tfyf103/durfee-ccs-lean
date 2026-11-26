module

public import DurfeeCCS.Step10.OuterErrorSum
public import DurfeeCCS.Step10.OuterBesselTransform
import Mathlib.Tactic.Linarith

/-! Applying the estimates for the explicit integral to the Bessel kernel itself. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real

/-- The absolute transform sum in equation (74). -/
theorem outerTransformAbsSum {y₀ y h : ℝ} (hy₀ : 80 < y₀)
    (hy : (9 / 10 : ℝ) * y₀ ≤ y) (hh : 8.76 < h) (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    Summable (fun p : ℤ => ‖kernelTransform y (outerZeta h (outerFrequency p))‖) ∧
      (∑' p : ℤ, ‖kernelTransform y (outerZeta h (outerFrequency p))‖) <
        1.42 * outerTransformAmplitude y h := by
  have hy₀' : 0 ≤ y := by linarith
  have hh₀ : 0 < h := by linarith
  have hmode (p : ℤ) : kernelTransform y (outerZeta h (outerFrequency p)) = outerIntegralMode y h p :=
    kernelTransformIntegral hy₀' (by simpa only [outerZeta_re] using hh₀)
  simp only [hmode]
  exact outerTransformIntegralAbsSum hy₀ hy hh hcap

/-- The two leading frequencies approximate the transform sum as in equation (75). -/
theorem outerTransformLeadingPair {y₀ h : ℝ} (hy₀ : 80 < y₀) (hh : 8.76 < h)
    (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    ‖(∑' p : ℤ, kernelTransform y₀ (outerZeta h (outerFrequency p))) -
        ((2 * (outerMainMode y₀ h π).re : ℝ) : ℂ)‖ < 0.130 * outerTransformAmplitude y₀ h := by
  have hy₀' : 0 ≤ y₀ := by linarith
  have hh₀ : 0 < h := by linarith
  have hmode (p : ℤ) : kernelTransform y₀ (outerZeta h (outerFrequency p)) = outerIntegralMode y₀ h p :=
    kernelTransformIntegral hy₀' (by simpa only [outerZeta_re] using hh₀)
  simp only [hmode]
  exact outerTransformIntegralLeadingPair hy₀ hh hcap

/-- The error in the low-frequency approximation, including the lower endpoint. -/
theorem outerLowFrequencyErrors {y h v : ℝ} (hy : 72 < y) (hh : 8.76 < h)
    (hscale : h / y ≤ 0.240) (hyh : 1 ≤ y * h) (hv : |v| ≤ h) :
    ‖kernelTransform y (outerZeta h v) - outerMainMode y h v‖ ≤
      ‖outerMainMode y h v‖ * (1 / (y * h) + 2 * Real.exp (-2 * (y * h))) +
        2 / h * Real.exp (y * h) := by
  rw [kernelTransformIntegral (by linarith : 0 ≤ y) (by simpa only [outerZeta_re] using
    (show 0 < h by linarith))]
  exact outerLow_transform_error hy hh hscale hyh hv

/-- The absolute sum at frequencies of magnitude greater than h, normalized by A_y(h). -/
theorem outerHighFrequencySum {y h : ℝ} (hy : 72 ≤ y) (hh : 8.76 < h) :
    let T (p : ℤ) := if h < |outerFrequency p| then
      ‖kernelTransform y (outerZeta h (outerFrequency p))‖ /
        outerTransformAmplitude y h else 0
    Summable T ∧ (∑' p, T p) <
      29 * y ^ 3 / h ^ 2 *
        Real.exp (-(4 * π ^ 2 * y / (3 * h)) * max 0.152 (1 / 4 - 8.4 / h ^ 2)) := by
  dsimp only
  have he (p : ℤ) : kernelTransform y (outerZeta h (outerFrequency p)) =
      kernelTransformIntegralFormula y (outerZeta h (outerFrequency p)) :=
    kernelTransformIntegral (by linarith) (by simpa only [outerZeta_re] using
      (show 0 < h by linarith))
  simp only [he]
  exact outerHigh_relative_sum hy hh

end DurfeeCCS.Step10
