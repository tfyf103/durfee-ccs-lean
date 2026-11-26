module

public import DurfeeCCS.Step10.OuterBesselKernel

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The weighted integral of the order-zero function in the outer kernel. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Complex Set MeasureTheory intervalIntegral Filter DurfeeCCS.Step06

private theorem integral_bessel_weight_moment (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t * (1 - t ^ 2) * t ^ (2 * k)) =
      1 / (2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have h₁ : Continuous (fun t : ℝ => t ^ (2 * k + 1)) := by fun_prop
  have h₃ : Continuous (fun t : ℝ => t ^ (2 * k + 3)) := by fun_prop
  calc
    _ = ∫ t in (0 : ℝ)..1, t ^ (2 * k + 1) - t ^ (2 * k + 3) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [pow_add t (2 * k), pow_one]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (h₁.intervalIntegrable _ _) (h₃.intervalIntegrable _ _),
        integral_pow, integral_pow]
      simp only [one_pow, zero_pow (by omega : 2 * k + 1 + 1 ≠ 0),
        zero_pow (by omega : 2 * k + 3 + 1 ≠ 0), sub_zero]
      push_cast
      field_simp
      ring

/-- The regularized order-two Bessel series is the weighted order-zero integral. -/
theorem kernelBesselIntegral (z : ℂ) :
    (besselAuxSeries 2).sum ((z / 2) ^ 2) =
      2 * ∫ t in (0 : ℝ)..1, ((t * (1 - t ^ 2) : ℝ) : ℂ) * besselI 0 (z * (t : ℂ)) := by
  let A (t : ℝ) : ℝ := t * (1 - t ^ 2)
  let F (k : ℕ) (t : ℝ) : ℂ := (A t : ℂ) * besselITerm 0 k (z * (t : ℂ))
  let C (k : ℕ) : ℝ := ‖besselITerm 0 k z‖
  have hF (k : ℕ) : Continuous (F k) := by dsimp [F, A, besselITerm]; fun_prop
  have ht (k : ℕ) (t : ℝ) :
      besselITerm 0 k (z * (t : ℂ)) = besselITerm 0 k z * (t : ℂ) ^ (2 * k) := by
    simp only [besselITerm, Nat.add_zero]
    rw [show z * (t : ℂ) / 2 = z / 2 * (t : ℂ) by ring, mul_pow]
    ring
  have hbound (k : ℕ) (t : ℝ) (ht' : t ∈ uIoc (0 : ℝ) 1) : ‖F k t‖ ≤ C k := by
    rw [uIoc_of_le zero_le_one] at ht'
    have hp : 0 ≤ t := ht'.1.le
    have hq : t ≤ 1 := ht'.2
    have hs : 0 ≤ 1 - t ^ 2 := by nlinarith
    have hA : 0 ≤ A t := mul_nonneg hp hs
    have hA' : A t ≤ 1 := (mul_le_of_le_one_right hp (by nlinarith)).trans hq
    simp only [F, C, ht, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hp, abs_of_nonneg hA]
    calc
      _ ≤ 1 * (‖besselITerm 0 k z‖ * 1) := by
        gcongr
        exact pow_le_one₀ hp hq
      _ = _ := by simp
  have hlim (t : ℝ) : HasSum (fun k => F k t) ((A t : ℂ) * besselI 0 (z * (t : ℂ))) :=
    (summable_besselITerm 0 (z * (t : ℂ))).hasSum.mul_left _
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := volume) (F := F)
    (fun k _ => C k) (fun k => (hF k).aestronglyMeasurable)
    (fun k => Eventually.of_forall (hbound k))
    (Eventually.of_forall (fun _ _ => summable_norm_besselITerm 0 z)) intervalIntegrable_const
    (Eventually.of_forall (fun t _ => hlim t))
  have hterm (k : ℕ) :
      2 * (∫ t in (0 : ℝ)..1, F k t) =
        (besselAuxSeries 2) k (fun _ => (z / 2) ^ 2) := by
    have hi : (∫ t in (0 : ℝ)..1, F k t) =
        besselITerm 0 k z * Complex.ofReal (∫ t in (0 : ℝ)..1, A t * t ^ (2 * k)) := by
      have hcast : Complex.ofReal (∫ t in (0 : ℝ)..1, A t * t ^ (2 * k)) =
          ∫ t in (0 : ℝ)..1, ((A t * t ^ (2 * k) : ℝ) : ℂ) := by
        exact (intervalIntegral.integral_ofReal (f := fun t => A t * t ^ (2 * k))).symm
      rw [hcast, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [F, ht, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    rw [hi, show (∫ t in (0 : ℝ)..1, A t * t ^ (2 * k)) =
      1 / (2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) from integral_bessel_weight_moment k]
    rw [besselAuxSeries, FormalMultilinearSeries.ofScalars_apply_eq, besselAuxCoeff, besselITerm,
      Nat.add_zero, pow_mul, Nat.factorial_succ (k + 1), Nat.factorial_succ k]
    push_cast
    simp only [smul_eq_mul]
    field_simp
    ring_nf
  rw [FormalMultilinearSeries.sum]
  exact ((hsum.mul_left 2).congr_fun (fun k => (hterm k).symm)).tsum_eq

/-- The compact kernel's smooth core as a weighted integral with its constant mode removed. -/
theorem outerBesselCore_eq_weighted {u : ℝ} (hu : 0 ≤ u) :
    (outerBesselCore u : ℂ) =
      ((Real.pi : ℂ) ^ 3 / 9) *
        ∫ t in (0 : ℝ)..1,
          ((t * (1 - t ^ 2) : ℝ) : ℂ) *
            (besselI 0 ((2 * Real.pi / Real.sqrt 3 * Real.sqrt u * t : ℝ) : ℂ) - 1) := by
  let z : ℝ := 2 * Real.pi / Real.sqrt 3 * Real.sqrt u
  let A (t : ℝ) : ℂ := ((t * (1 - t ^ 2) : ℝ) : ℂ)
  let f (t : ℝ) : ℂ := A t * besselI 0 (z * (t : ℂ))
  have hs : (z / 2) ^ 2 = Real.pi ^ 2 / 3 * u := by
    dsimp [z]
    rw [show (2 * Real.pi / Real.sqrt 3 * Real.sqrt u / 2 : ℝ) =
      Real.pi / Real.sqrt 3 * Real.sqrt u by ring, mul_pow, div_pow]
    rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt hu]
  have hz : ((z : ℂ) / 2) ^ 2 = ((Real.pi ^ 2 / 3 * u : ℝ) : ℂ) := by exact_mod_cast hs
  have hreal (v : ℝ) : besselI 0 (v : ℂ) = ((besselI 0 (v : ℂ)).re : ℂ) := by
    let G (k : ℕ) : ℝ :=
      (v / 2) ^ (2 * k) / ((k.factorial : ℝ) * (k.factorial : ℝ))
    have h : (besselI 0 (v : ℂ)) = Complex.ofReal (∑' k, G k) := by
      rw [besselI, Complex.ofReal_tsum]
      apply tsum_congr
      intro k
      simp only [G, besselITerm, Nat.add_zero]
      push_cast
      rfl
    rw [h, Complex.ofReal_re]
  have hf_im (t : ℝ) : f t = Complex.ofReal (f t).re := by
    dsimp [f]
    rw [← Complex.ofReal_mul, hreal (z * t), ← Complex.ofReal_mul, Complex.ofReal_re]
  have hcast : ∫ t in (0 : ℝ)..1, f t =
      Complex.ofReal (∫ t in (0 : ℝ)..1, (f t).re) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _
    exact hf_im t
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hB : Continuous (besselI 0) :=
    continuous_iff_continuousAt.mpr fun x => (analyticAt_besselI 0 x).continuousAt
  have hf : Continuous f := hA.mul (hB.comp (by fun_prop))
  have hAint : (∫ t in (0 : ℝ)..1, A t) = 1 / 4 := by
    have he : (∫ t in (0 : ℝ)..1, t * (1 - t ^ 2)) = (1 / 4 : ℝ) := by
      convert integral_bessel_weight_moment 0 using 1 <;> norm_num
    dsimp [A]
    rw [intervalIntegral.integral_ofReal, he]
    norm_num
  have hdiff : (∫ t in (0 : ℝ)..1, A t * (besselI 0 ((z * t : ℝ) : ℂ) - 1)) =
      (∫ t in (0 : ℝ)..1, f t) - 1 / 4 := by
    rw [← hAint, ← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hA.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [f, Complex.ofReal_mul, mul_sub, mul_one]
  simp only [outerBesselCore, ← hz, kernelBesselIntegral]
  change Complex.ofReal (Real.pi ^ 3 / 18 * (2 * ∫ t in (0 : ℝ)..1, f t).re - Real.pi ^ 3 / 36) =
    (Real.pi : ℂ) ^ 3 / 9 * ∫ t in (0 : ℝ)..1, A t * (besselI 0 ((z * t : ℝ) : ℂ) - 1)
  rw [hdiff, hcast, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.ofReal_re]
  push_cast
  ring

end DurfeeCCS.Step10
