module

public import DurfeeCCS.Step14.RademacherMultiplier
public import DurfeeCCS.Step14.RademacherContour
public import DurfeeCCS.Step14.RademacherPolarCompletion
public import DurfeeCCS.Step14.RademacherNonpolar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Polar subtraction of the actual coefficient integrand on one Ford arc. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step14

open Complex MeasureTheory
open DurfeeCCS.Step06 DurfeeCCS.Step08

/-- The coefficient integrand multiplied by the derivative of the forward
Ford arc parameter, in the real inverse coordinate. -/
def fordCoefficientIntegrand (n h k : ℕ) (v : ℝ) : ℂ :=
  let w := verticalPoint 1 v
  twoColourFareyIntegrand n ((h : ℂ) / k + I / ((k : ℂ) ^ 2 * w)) /
    ((k : ℂ) ^ 2 * w ^ 2)

theorem fordCoefficientIntegrand_split (n : ℕ) {h k : ℕ} (hk : 0 < k) (hg : h.Coprime k) :
    ∃ a : ℤ, ∀ v : ℝ,
      fordCoefficientIntegrand n h k v = twoColourPhase n h k *
        (fordPolarIntegrand n k v +
          fordNonpolarKernel (2 * Real.pi * (a : ℝ) / k) (fordPolarB n k) (verticalPoint 1 v) /
            (k : ℂ) ^ 3) := by
  obtain ⟨a, hsplit⟩ := twoColourCoefficient_inverse_cusp_dedekind n hk hg
  refine ⟨a, ?_⟩
  intro v
  let w := verticalPoint 1 v
  have hw : 0 < w.re := by simp [w]
  have hq : 2 * (Real.pi : ℂ) * I * ((a : ℂ) / k + I * w) =
      (↑(2 * Real.pi * (a : ℝ) / k : ℝ) : ℂ) * I - ((2 * Real.pi : ℝ) : ℂ) * w := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  unfold fordCoefficientIntegrand twoColourFareyIntegrand
  dsimp only
  rw [mul_comm]
  simp only [neg_mul]
  rw [hsplit hw]
  change _ =
    twoColourPhase n h k * (fordPolarIntegrand n k v +
      fordNonpolarKernel (2 * Real.pi * (a : ℝ) / k) (fordPolarB n k) w / (k : ℂ) ^ 3)
  rw [hq]
  unfold fordPolarIntegrand fordNonpolarKernel fordPolarB
  change
    twoColourPhase n h k *
      (rademacherPolarKernel _ _ w / (k : ℂ) ^ 3) * _ =
    twoColourPhase n h k *
      (rademacherPolarKernel _ _ w / (k : ℂ) ^ 3 +
        rademacherPolarKernel _ _ w * (_ - 1) / (k : ℂ) ^ 3)
  ring

/-- Integration of the exact polar/nonpolar split over a finite Ford arc. -/
theorem integral_fordCoefficientIntegrand_split {n h k : ℕ} (hn : 0 < n)
    (hk : 0 < k) (hg : h.Coprime k) :
    ∃ a : ℤ, ∀ l r : ℝ,
      (∫ v in l..r, fordCoefficientIntegrand n h k v) = twoColourPhase n h k *
        ((∫ v in l..r, fordPolarIntegrand n k v) +
          (∫ v in l..r, fordNonpolarKernel (2 * Real.pi * (a : ℝ) / k)
            (fordPolarB n k) (verticalPoint 1 v)) / (k : ℂ) ^ 3) := by
  obtain ⟨a, ha⟩ := fordCoefficientIntegrand_split n hk hg
  refine ⟨a, ?_⟩
  intro l r
  have hP := integrable_fordPolarIntegrand hn hk
  have hN := integrable_fordNonpolar_vertical (2 * Real.pi * (a : ℝ) / k)
    (fordPolarB n k) (c := 1) le_rfl
  simp_rw [ha]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hP.intervalIntegrable (hN.div_const _).intervalIntegrable,
    intervalIntegral.integral_div]

end DurfeeCCS.Step14
