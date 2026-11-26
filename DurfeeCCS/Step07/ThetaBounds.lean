module

public import DurfeeCCS.Step07.ThetaBoundsIntervals
public import DurfeeCCS.Step07.SqrtInterval
public import DurfeeCCS.Step07.TrigonometricBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import DurfeeCCS.Step07.ThetaBoundsIntervals
public meta import DurfeeCCS.Step07.SqrtInterval

/-!
# Rational error certificates for the finite rows of Lemma 3.8

The budget below is the sum of the five error terms on pages 29–30. All row
data and all interval endpoints used in the certificates are exact rationals.
-/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open Real

/-- The fourth root written as two square roots for rational enclosures. -/
def thetaFourthRoot (x : ℝ) : ℝ := √(√x)

theorem thetaFourthRoot_pow (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    thetaFourthRoot x ^ m = x ^ ((m : ℝ) / 4) := by
  rw [thetaFourthRoot, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- The constant from the logarithmic midpoint-rule error (56). -/
def theta38K (h : ℝ) : ℝ :=
  let d := (π / 2 - h) / 2
  (sin d ^ 2)⁻¹ + (exp (2 * d / 3) - 1)⁻¹

/-- The worst slope ratio on a row, denoted by `ϱ₊` in the paper. -/
def theta38Rho (aMin bMax : ℝ) : ℝ := bMax / aMin

def theta38Delta (aMin bMax : ℝ) : ℝ :=
  (3 / 2 - theta38Rho aMin bMax) ^ 2 / (13 / 4)

def theta38DeltaThree (aMin bMax : ℝ) : ℝ :=
  (3 - theta38Rho aMin bMax) ^ 2 / 10

def theta38Z (eps aMax h : ℝ) : ℝ :=
  h ^ 2 / ((13 / 4) * (aMax / 80) * (1 + eps ^ 2))

/-- The finite-row bound `R` assembled from (58), (59), and the bound for (60). -/
def theta38Error (ell aMin aMax bMin bMax h kappa : ℝ) : ℝ :=
  let eps := exp (-ell)
  let q := aMax / 80
  let z := theta38Z eps aMax h
  let δ := theta38Delta aMin bMax
  let δ₃ := theta38DeltaThree aMin bMax
  let quartic := (3 / 4) * kappa * eps * q *
    thetaFourthRoot (13 / 4) ^ 7 * thetaFourthRoot (1 + eps ^ 2) ^ 9
  let multiplier := thetaFourthRoot ((13 / 4) * (1 + eps ^ 2)) *
    (exp ((13 / 16) * theta38K h * eps * q + √(13 / 4) * q / 12 + 1 / 10 ^ 20) - 1)
  let angle := (119 / 10) * thetaFourthRoot ((13 / 4) * (1 + eps ^ 2)) *
    exp (-z) / √(π * z)
  let gaussian := (160 * aMin)⁻¹ + (1 + (160 * aMin)⁻¹) * exp (-320 * aMin) +
    8 * √(80 * aMax) * (exp (-80 * bMin ^ 2 / aMax) + exp (-80 * aMin * δ))
  let tail := 96 * √(80 * aMin) * exp (-80 * aMin * δ) +
    57000 * √(80 * aMin) * exp (-80 * aMin * δ₃)
  (243 / 100) * (quartic + multiplier + angle) + gaussian + tail

/-- One finite interval and its error data in the table on page 30. -/
structure Theta38Row where
  ell : ℝ
  hi : ℝ
  aMin : ℝ
  aMax : ℝ
  bMin : ℝ
  bMax : ℝ
  h : ℝ
  kappa : ℝ
  target : ℝ

def theta38Row (i : Fin 9) : Theta38Row :=
  match i.val with
  | 0 => ⟨0, 0.0625, 1.06975, 1.10495, 0.85623, 0.87428, 3 / 4, 0.426, 0.876⟩
  | 1 => ⟨0.0625, 0.125, 1.10494, 1.14106, 0.87427, 0.89219, 3 / 4, 0.426, 0.788⟩
  | 2 => ⟨0.125, 0.25, 1.14105, 1.21600, 0.89218, 0.92752, 3 / 4, 0.426, 0.742⟩
  | 3 => ⟨0.25, 0.5, 1.21599, 1.37623, 0.92751, 0.99542, 3 / 4, 0.426, 0.672⟩
  | 4 => ⟨0.5, 1, 1.37622, 1.73266, 0.99541, 1.11586, 3 / 4, 0.426, 0.584⟩
  | 5 => ⟨1, 2, 1.73265, 2.54406, 1.11585, 1.28797, 3 / 4, 0.426, 0.519⟩
  | 6 => ⟨2, 3, 2.54405, 3.42799, 1.28796, 1.38921, 3 / 4, 0.426, 0.421⟩
  | 7 => ⟨3, 4, 3.42798, 4.34983, 1.38920, 1.44868, 3 / 4, 0.426, 0.629⟩
  | 8 => ⟨4, 5, 4.34982, 5.29407, 1.44867, 1.48482, 1, 0.547, 0.199⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def Theta38Row.error (row : Theta38Row) : ℝ :=
  theta38Error row.ell row.aMin row.aMax row.bMin row.bMax row.h row.kappa

/-- The finite rows cover the entire closed interval of logarithmic radii. -/
theorem theta38_rows_cover {x : ℝ} (h₀ : 0 ≤ x) (h₅ : x ≤ 5) :
    ∃ i : Fin 9, x ∈ Set.Icc (theta38Row i).ell (theta38Row i).hi := by
  rcases le_or_gt x 0.0625 with h₁ | h₁
  · exact ⟨0, h₀, h₁⟩
  rcases le_or_gt x 0.125 with h₂ | h₂
  · exact ⟨1, h₁.le, h₂⟩
  rcases le_or_gt x 0.25 with h₃ | h₃
  · exact ⟨2, h₂.le, h₃⟩
  rcases le_or_gt x 0.5 with h₄ | h₄
  · exact ⟨3, h₃.le, h₄⟩
  rcases le_or_gt x 1 with h₆ | h₆
  · exact ⟨4, h₄.le, h₆⟩
  rcases le_or_gt x 2 with h₇ | h₇
  · exact ⟨5, h₆.le, h₇⟩
  rcases le_or_gt x 3 with h₈ | h₈
  · exact ⟨6, h₇.le, h₈⟩
  rcases le_or_gt x 4 with h₉ | h₉
  · exact ⟨7, h₈.le, h₉⟩
  exact ⟨8, h₉.le, h₅⟩

theorem theta38_rows_admissible (i : Fin 9) :
    let row := theta38Row i
    0 < row.aMin ∧ 0 < row.aMax ∧ theta38Rho row.aMin row.bMax < 0.82 ∧
      (1 / 2 : ℝ) < 80 * row.aMin * theta38Delta row.aMin row.bMax ∧
      (1 / 2 : ℝ) < 80 * row.bMin ^ 2 / row.aMax := by
  fin_cases i <;> norm_num [theta38Row, theta38Rho, theta38Delta]

private theorem pi_mem : π ∈ Set.Icc 3.14159265358979323846 3.14159265358979323847 :=
  ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩

private theorem k_three_quarters : theta38K (3 / 4) ∈ Set.Icc 0 9.4601 := by
  unfold theta38K
  dsimp only
  let d : ℝ := (π / 2 - 3 / 4) / 2
  have hpi := pi_mem
  have hd : d ∈ Set.Icc 0.4103981633974 0.4103981633975 := by
    dsimp only [d]
    dyadic_interval [prec := 64]
  have hs : sin d ∈ Set.Icc 0.3989744 1 := by
    refine ⟨le_trans ?_ (sin_taylor_seven_lower (by linarith [hd.1])
        (by dyadic_interval [prec := 64])),
      Real.sin_le_one _⟩
    dyadic_interval [prec := 64]
  change (sin d ^ 2)⁻¹ + (exp (2 * d / 3) - 1)⁻¹ ∈ Set.Icc 0 9.4601
  dyadic_interval [prec := 64]

private theorem k_one : theta38K 1 ∈ Set.Icc 0 17.390 := by
  unfold theta38K
  dsimp only
  let d : ℝ := (π / 2 - 1) / 2
  have hpi := pi_mem
  have hd : d ∈ Set.Icc 0.2853979 0.2853983 := by
    dsimp only [d]
    dyadic_interval [prec := 64]
  have hs : sin d ∈ Set.Icc 0.281522 1 := by
    refine ⟨le_trans ?_ (Real.sin_ge_sub_cube (by linarith [hd.1])), Real.sin_le_one _⟩
    dyadic_interval [prec := 64]
  change (sin d ^ 2)⁻¹ + (exp (2 * d / 3) - 1)⁻¹ ∈ Set.Icc 0 17.390
  dyadic_interval [prec := 64]

/-- The nine strict error budgets on page 30. -/
theorem theta38_error_rows (i : Fin 9) : (theta38Row i).error < (theta38Row i).target := by
  fin_cases i <;> norm_num only [Theta38Row.error, theta38Row]
  all_goals
    have hpi := pi_mem
    have hk₀ := k_three_quarters
    have hk₁ := k_one
    unfold theta38Error
    dsimp only [theta38Z, theta38Delta, theta38DeltaThree, theta38Rho, thetaFourthRoot]
    generalize theta38K (3 / 4) = k₀ at hk₀ ⊢
    generalize theta38K 1 = k₁ at hk₁ ⊢
    dyadic_interval [prec := 48]

theorem theta38_error_row_one : theta38Error 0 1.06975 1.10495 0.85623 0.87428 (3 / 4) 0.426 <
    0.876 := theta38_error_rows 0

/-- The tail budget rounded outwards at the base value √n = 80. -/
theorem theta38_error_tail_upper : theta38Error 5 5.29406 5.76 1.48481 (π / 2) 1 0.547 < 0.212 := by
  have hpi := pi_mem
  have hk := k_one
  unfold theta38Error
  dsimp only [theta38Z, theta38Delta, theta38DeltaThree, theta38Rho, thetaFourthRoot]
  generalize theta38K 1 = k at hk ⊢
  dyadic_interval [prec := 48]

end DurfeeCCS.Step07
