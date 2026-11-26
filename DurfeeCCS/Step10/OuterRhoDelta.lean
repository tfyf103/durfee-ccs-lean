module

public import DurfeeCCS.Step10.OuterRho
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The quadratic identity and its derivative in the squared frequency, (71)–(72). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real

/-- The square-root discriminant in the quadratic equation for the outer frequency. -/
def outerFrequencyDiscriminant (h a u : ℝ) : ℝ :=
  Real.sqrt ((h ^ 2 + u - a) ^ 2 + 4 * a * h ^ 2)

/-- The positive solution of the quadratic equation in the squared frequency u. -/
def outerFrequencyDelta (h a u : ℝ) : ℝ :=
  (outerFrequencyDiscriminant h a u - (h ^ 2 + u - a)) / 2

theorem outerFrequencyDiscriminant_pos {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (u : ℝ) :
    0 < outerFrequencyDiscriminant h a u := by
  unfold outerFrequencyDiscriminant
  positivity

theorem outerFrequencyDelta_pos {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (u : ℝ) :
    0 < outerFrequencyDelta h a u := by
  unfold outerFrequencyDelta outerFrequencyDiscriminant
  apply div_pos _ (by norm_num)
  apply sub_pos.mpr
  apply lt_of_le_of_lt (le_abs_self (h ^ 2 + u - a))
  apply (Real.lt_sqrt (abs_nonneg _)).2
  rw [sq_abs]
  have hp : 0 < 4 * a * h ^ 2 := by positivity
  linarith

theorem outerFrequencyDiscriminant_eq (h a u : ℝ) :
    outerFrequencyDiscriminant h a u = h ^ 2 + u - a + 2 * outerFrequencyDelta h a u := by
  unfold outerFrequencyDelta
  ring

/-- The discriminant is the norm of the squared principal root at a real frequency. -/
theorem outerFrequencyDiscriminant_eq_norm_sq (h a v : ℝ) :
    outerFrequencyDiscriminant h a (v ^ 2) = ‖outerRhoAt h v a ^ 2‖ := by
  let ρ := outerRhoAt h v a
  have hN₂ : ‖ρ ^ 2‖ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hR : ρ.re ^ 2 - ρ.im ^ 2 = h ^ 2 + a - v ^ 2 := outerRhoAt_re_sq_sub_im_sq h v a
  have hI : ρ.re * ρ.im = h * v := outerRhoAt_re_mul_im h v a
  have hρ : ‖ρ ^ 2‖ ^ 2 = (h ^ 2 + v ^ 2 - a) ^ 2 + 4 * a * h ^ 2 := by
    rw [hN₂]
    calc
      _ = (ρ.re ^ 2 - ρ.im ^ 2) ^ 2 + 4 * (ρ.re * ρ.im) ^ 2 := by ring
      _ = _ := by rw [hR, hI]; ring
  unfold outerFrequencyDiscriminant
  rw [← hρ, Real.sqrt_sq (norm_nonneg _)]

/-- At a real frequency, the quadratic solution is the difference of the two squared real parts. -/
theorem outerFrequencyDelta_eq (h a v : ℝ) :
    outerFrequencyDelta h a (v ^ 2) = (outerRhoAt h v a).re ^ 2 - h ^ 2 := by
  let ρ := outerRhoAt h v a
  have hN₂ : ‖ρ ^ 2‖ = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  unfold outerFrequencyDelta
  rw [outerFrequencyDiscriminant_eq_norm_sq h a v, hN₂]
  linarith [outerRhoAt_re_sq_sub_im_sq h v a]

/-- Equation (71), allowing an arbitrary positive squared Bessel scale. -/
theorem outerFrequencyDelta_quadratic {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (u : ℝ) :
    outerFrequencyDelta h a u * (h ^ 2 + u - a + outerFrequencyDelta h a u) = a * h ^ 2 := by
  have hd : outerFrequencyDiscriminant h a u ^ 2 = (h ^ 2 + u - a) ^ 2 + 4 * a * h ^ 2 := by
    unfold outerFrequencyDiscriminant
    rw [Real.sq_sqrt (by positivity)]
  unfold outerFrequencyDelta
  linear_combination hd / 4

theorem outerFrequencyDelta_le {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (v : ℝ) :
    outerFrequencyDelta h a (v ^ 2) ≤ a := by
  let ρ := outerRhoAt h v a
  have hr : h < ρ.re := outerRhoAt_re_gt hh ha
  have him : |ρ.im| ≤ |v| := by
    change |(outerRhoAt h v a).im| ≤ |v|
    rw [outerRhoAt_im_eq hh ha, abs_div, abs_mul, abs_of_pos hh, abs_of_pos (hh.trans hr),
      div_le_iff₀ (hh.trans hr)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hr.le (abs_nonneg v)
  have him₂ := pow_le_pow_left₀ (abs_nonneg _) him 2
  simp only [sq_abs] at him₂
  rw [outerFrequencyDelta_eq h a v]
  linarith [outerRhoAt_re_sq_sub_im_sq h v a]

/-- The discriminant identity and the two coordinates of the principal root in (71). -/
theorem outerFrequencyQuadratic {h : ℝ} (hh : 0 < h) (v : ℝ) :
    let a : ℝ := 4 * π ^ 2 / 3
    let D := (outerRho h v).re ^ 2 - h ^ 2
    D * (h ^ 2 + v ^ 2 - a + D) = a * h ^ 2 ∧
      (outerRho h v).im = h * v / (outerRho h v).re ∧
      0 < D ∧ D ≤ a ∧ h ^ 2 + v ^ 2 - a + 2 * D = ‖outerRho h v ^ 2‖ := by
  dsimp only
  let a : ℝ := 4 * π ^ 2 / 3
  have ha : 0 < a := by dsimp [a]; positivity
  have he : outerFrequencyDelta h a (v ^ 2) = (outerRho h v).re ^ 2 - h ^ 2 :=
    outerFrequencyDelta_eq h a v
  rw [← he]
  exact ⟨outerFrequencyDelta_quadratic hh ha _, outerRho_im_eq hh,
    outerFrequencyDelta_pos hh ha _, outerFrequencyDelta_le hh ha v,
    (outerFrequencyDiscriminant_eq _ _ _).symm.trans (outerFrequencyDiscriminant_eq_norm_sq h a v)⟩

/-- Equation (72), with a smooth extension in the squared frequency through zero. -/
theorem hasDerivAt_outerFrequencyDelta {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (u : ℝ) :
    HasDerivAt (outerFrequencyDelta h a)
      (-outerFrequencyDelta h a u / outerFrequencyDiscriminant h a u) u := by
  let q (u : ℝ) := h ^ 2 + u - a
  let R (u : ℝ) := q u ^ 2 + 4 * a * h ^ 2
  have hq : HasDerivAt q 1 u := ((hasDerivAt_id u).const_add (h ^ 2)).sub_const a
  have hR : HasDerivAt R (2 * q u) u := by
    convert (hq.pow 2).add_const (4 * a * h ^ 2) using 1
    simp
  have hP : 0 < R u := by dsimp [R, q]; positivity
  have hD : HasDerivAt (outerFrequencyDiscriminant h a)
      (q u / outerFrequencyDiscriminant h a u) u := by
    convert (Real.hasDerivAt_sqrt hP.ne').comp u hR using 1
    · rfl
    · change q u / Real.sqrt (R u) = (1 / (2 * Real.sqrt (R u))) * (2 * q u)
      field_simp
  convert (hD.sub hq).div_const 2 using 1
  · rfl
  · unfold outerFrequencyDelta
    change -((outerFrequencyDiscriminant h a u - q u) / 2) / outerFrequencyDiscriminant h a u =
      (q u / outerFrequencyDiscriminant h a u - 1) / 2
    have hS := outerFrequencyDiscriminant_pos hh ha u
    field_simp
    ring

theorem outerFrequencyDelta_deriv_neg {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (u : ℝ) :
    deriv (outerFrequencyDelta h a) u =
      -outerFrequencyDelta h a u / (h ^ 2 + u - a + 2 * outerFrequencyDelta h a u) ∧
    deriv (outerFrequencyDelta h a) u < 0 := by
  have hd := (hasDerivAt_outerFrequencyDelta hh ha u).deriv
  refine ⟨hd.trans (congrArg (-outerFrequencyDelta h a u / ·)
    (outerFrequencyDiscriminant_eq h a u)), ?_⟩
  rw [hd]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (outerFrequencyDelta_pos hh ha u))
    (outerFrequencyDiscriminant_pos hh ha u)

end DurfeeCCS.Step10
