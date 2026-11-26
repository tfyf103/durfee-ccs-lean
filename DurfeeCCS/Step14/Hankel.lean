module

public import DurfeeCCS.Step06.Nemes
import all DurfeeCCS.Step06.Nemes

/-!
# Positive-axis Hankel formula

For orders zero and one the outgoing Hankel integral can be taken on the ray
\(1+i(0,\infty)\). The substitution \(\zeta=i-y\) in the Laplace contour
from \(-\infty+i\) to \(i\) gives this normalization. See
[Matsuo, Mathematical Physics II, (5.67)](https://www-hep.phys.s.u-tokyo.ac.jp/~matsuo/file/Bussu2-2024.pdf).
The theorem 'hankelFirstKindVertical_eq_laplaceContour' checks that coordinate
and principal-power conversion in Lean.

The ray integral is specified independently of the Gamma amplitude and remainder.
The exact complex formula below follows by evaluating the ray with the change of
variable \(t=xy\). Its real part agrees with the existing series for \(J_\nu\).
-/

@[expose] public noncomputable section

namespace DurfeeCCS.Step14

open DurfeeCCS.Step06 MeasureTheory Set

/-- Outgoing Hankel function on the positive real axis in vertical-ray form,
with the normalization for orders zero and one. -/
def hankelFirstKindVertical (ν : ℕ) (x : ℝ) : ℂ :=
  ((2 * x ^ ν / Real.pi : ℝ) : ℂ) *
    ((-Complex.I) * ∫ y in Ioi (0 : ℝ), poissonKernel ν x (1 + (y : ℂ) * Complex.I))

/-- The same Hankel function expressed using the Laplace contour
\(\zeta=i-y\) oriented from \(-\infty+i\) to \(i\). -/
theorem hankelFirstKindVertical_eq_laplaceContour (ν : ℕ) (hν : ν = 0 ∨ ν = 1)
    (x : ℝ) :
    hankelFirstKindVertical ν x =
      ((2 * (x / 2) ^ ν / (Real.sqrt Real.pi * Real.Gamma ((ν : ℝ) + 1 / 2)) : ℝ) : ℂ) *
        ((-Complex.I) * ∫ y in Ioi (0 : ℝ),
          (1 + (Complex.I - (y : ℂ)) ^ (2 : ℕ)) ^ ((ν : ℂ) - 1 / 2) *
            Complex.exp ((x : ℂ) * (Complex.I - (y : ℂ)))) := by
  have hsquare : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    rw [← pow_two, Real.sq_sqrt Real.pi_pos.le]
  have hΓ₁ : Real.Gamma (1 + 1 / 2) = Real.sqrt Real.pi / 2 := by
    rw [add_comm (1 : ℝ) (1 / 2), Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hcoef : 2 * x ^ ν / Real.pi =
      2 * (x / 2) ^ ν / (Real.sqrt Real.pi * Real.Gamma ((ν : ℝ) + 1 / 2)) := by
    rcases hν with rfl | rfl
    · simp only [pow_zero, mul_one, Nat.cast_zero, zero_add, Real.Gamma_one_half_eq, hsquare]
    · simp only [pow_one, Nat.cast_one, hΓ₁, mul_div_assoc]
      field_simp [Real.pi_ne_zero]
      rw [Real.sq_sqrt Real.pi_pos.le]
  unfold hankelFirstKindVertical
  rw [hcoef]
  apply congrArg (fun value : ℂ =>
    ((2 * (x / 2) ^ ν / (Real.sqrt Real.pi * Real.Gamma ((ν : ℝ) + 1 / 2)) : ℝ) : ℂ) *
      ((-Complex.I) * value))
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  have hphase : (x : ℂ) * Complex.I * (1 + (y : ℂ) * Complex.I) =
      (x : ℂ) * (Complex.I - (y : ℂ)) := by
    linear_combination (x : ℂ) * (y : ℂ) * Complex.I_sq
  have hbase : 1 - (1 + (y : ℂ) * Complex.I) ^ (2 : ℕ) =
      1 + (Complex.I - (y : ℂ)) ^ (2 : ℕ) := by
    linear_combination -(1 + (y : ℂ) ^ (2 : ℕ)) * Complex.I_sq
  unfold poissonKernel
  dsimp only
  rw [hphase, mul_comm, hbase]
  congr 1
  rcases hν with rfl | rfl
  · simp only [ite_true, Complex.sqrt, ← Complex.cpow_neg, one_div, Nat.cast_zero, zero_sub]
  · simp only [one_ne_zero, ite_false, Complex.sqrt, Nat.cast_one]
    congr 1
    norm_num

/-- The first \(K_\nu\) remainder from the Gamma integral, at the two orders in
the manuscript. The half-power uses the principal square root. -/
def nemesKFirstRemainder (ν : ℕ) (w : ℂ) : ℂ :=
  (∫ t in Ioi (0 : ℝ), (hankelGammaWeight ((ν : ℝ) + 1 / 2) t : ℂ) *
    (if ν = 0 then (Complex.sqrt (1 + (t : ℂ) / (2 * w)))⁻¹
      else Complex.sqrt (1 + (t : ℂ) / (2 * w)))) /
    (Real.Gamma ((ν : ℝ) + 1 / 2) : ℂ) - 1

theorem arg_neg_axis_rotation {x : ℝ} (hx : 0 < x) :
    Complex.arg (-(x : ℂ) * Complex.I) = -(Real.pi / 2) := by
  rw [neg_mul, ← mul_neg, Complex.arg_real_mul _ hx, Complex.arg_neg_I]

theorem nemesKFirstRemainder_neg_mul_I (ν : ℕ) {x : ℝ} (hx : 0 < x) :
    nemesKFirstRemainder ν (-(x : ℂ) * Complex.I) = hankelGammaAmplitude ν x - 1 := by
  have hI (t : ℝ) :
      (t : ℂ) / (2 * (-(x : ℂ) * Complex.I)) = ((t / (2 * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    field_simp [hxC, Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring
  simp only [nemesKFirstRemainder, hankelGammaAmplitude, hankelHalfPower, hI]

theorem norm_nemesKFirstRemainder_neg_mul_I_le (ν : ℕ) (hν : ν = 0 ∨ ν = 1)
    {x : ℝ} (hx : 0 < x) :
    ‖nemesKFirstRemainder ν (-(x : ℂ) * Complex.I)‖ ≤ |4 * (ν : ℝ) ^ 2 - 1| / (8 * x) := by
  rw [nemesKFirstRemainder_neg_mul_I ν hx]
  refine (norm_hankelGammaAmplitude_sub_one_le ν hx).trans_eq ?_
  rcases hν with rfl | rfl <;> push_cast <;> norm_num <;> ring

private theorem hankelVertical_zero_normalized {x : ℝ} (hx : 0 < x) :
    (Real.sqrt (Real.pi * x / 2) : ℂ) * hankelFirstKindVertical 0 x =
      Complex.exp ((besselPhase 0 x : ℂ) * Complex.I) * hankelGammaAmplitude 0 x := by
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
  have hG : Real.sqrt (Real.pi * x / 2) * (2 / Real.pi) *
      (Real.Gamma (1 / 2) / Real.sqrt x) = Real.sqrt 2 := by
    rw [← gamma_prefactor_zero hx, div_eq_mul_inv]
    ring
  rw [hankelFirstKindVertical, pow_zero, mul_one, hQ, hP]
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hG]

private theorem hankelVertical_one_normalized {x : ℝ} (hx : 0 < x) :
    (Real.sqrt (Real.pi * x / 2) : ℂ) * hankelFirstKindVertical 1 x =
      Complex.exp ((besselPhase 1 x : ℂ) * Complex.I) * hankelGammaAmplitude 1 x := by
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
  have hG : Real.sqrt (Real.pi * x / 2) * (2 * x / Real.pi) *
      (Real.Gamma (1 + 1 / 2) / (x * Real.sqrt x)) = Real.sqrt 2 / 2 := by
    rw [← gamma_prefactor_one hx]
    ring
  rw [hankelFirstKindVertical, pow_one, hQ, hP]
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hG]

theorem hankelFirstKindVertical_normalized (ν : ℕ) (hν : ν = 0 ∨ ν = 1)
    {x : ℝ} (hx : 0 < x) :
    (Real.sqrt (Real.pi * x / 2) : ℂ) * hankelFirstKindVertical ν x =
      Complex.exp ((besselPhase ν x : ℂ) * Complex.I) * hankelGammaAmplitude ν x := by
  rcases hν with rfl | rfl
  · exact hankelVertical_zero_normalized hx
  · exact hankelVertical_one_normalized hx

/-- The complex expansion with the explicit first omitted term at \(-ix\). -/
theorem hankelFirstKindVertical_nemes (ν : ℕ) (hν : ν = 0 ∨ ν = 1)
    {x : ℝ} (hx : 0 < x) :
    hankelFirstKindVertical ν x =
      (Real.sqrt (2 / (Real.pi * x)) : ℂ) * Complex.exp ((besselPhase ν x : ℂ) * Complex.I) *
        (1 + nemesKFirstRemainder ν (-(x : ℂ) * Complex.I)) := by
  have hS : 0 < Real.sqrt (Real.pi * x / 2) := by positivity
  have hinv : (Real.sqrt (Real.pi * x / 2))⁻¹ = Real.sqrt (2 / (Real.pi * x)) := by
    rw [← Real.sqrt_inv]
    congr 1
    field_simp [Real.pi_ne_zero, hx.ne']
  rw [nemesKFirstRemainder_neg_mul_I ν hx, ← hinv, Complex.ofReal_inv,
    show (1 + (hankelGammaAmplitude ν x - 1) : ℂ) = hankelGammaAmplitude ν x by ring,
    mul_assoc, ← hankelFirstKindVertical_normalized ν hν hx, inv_mul_cancel_left₀
      (Complex.ofReal_ne_zero.mpr hS.ne')]

theorem hankelFirstKindVertical_re_eq_besselJ (ν : ℕ) (hν : ν = 0 ∨ ν = 1)
    {x : ℝ} (hx : 0 < x) :
    (hankelFirstKindVertical ν x).re = (besselJ ν (x : ℂ)).re := by
  have h1 := congrArg Complex.re (hankelFirstKindVertical_normalized ν hν hx)
  rw [Complex.re_ofReal_mul] at h1
  have h2 : Real.sqrt (Real.pi * x / 2) * (besselJ ν (x : ℂ)).re =
      (Complex.exp ((besselPhase ν x : ℂ) * Complex.I) * hankelGammaAmplitude ν x).re := by
    rcases hν with rfl | rfl
    · exact besselJ_zero_hankelGamma hx
    · exact besselJ_one_hankelGamma hx
  exact mul_left_cancel₀ (by positivity) (h1.trans h2.symm)

/-- The contour integral exists at both orders, including the singular endpoint
of the order-zero kernel. -/
theorem integrableOn_hankelFirstKindVertical_kernel (ν : ℕ) (hν : ν = 0 ∨ ν = 1)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => poissonKernel ν x (1 + (y : ℂ) * Complex.I)) (Ioi 0) := by
  rcases hν with rfl | rfl
  · exact integrableOn_poissonKernel_right_zero hx
  · exact integrableOn_poissonKernel_vertical 1 hx le_rfl (Or.inl one_ne_zero) (abs_one : |(1 : ℝ)| = 1)

end DurfeeCCS.Step14
