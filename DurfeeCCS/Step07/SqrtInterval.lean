module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Outward dyadic rounding of the real square root by the integer square root. -/

@[expose] public section

namespace Inclusion.IntervalDyadicReal

/-- The grid index at precision `prec` of the lower square-root endpoint. -/
def sqrtGrid (d : Dyadic) (prec : ℕ) : ℕ :=
  Nat.sqrt ⌊max d.toRat 0 * (2 : ℚ) ^ (2 * prec)⌋₊

private theorem toReal_of_grid (i p : ℕ) :
    Dyadic.toReal (Dyadic.ofIntWithPrec (i : ℤ) (p : ℤ)) = (i : ℝ) / 2 ^ p := by
  rw [Dyadic.toReal, Dyadic.toRat_ofIntWithPrec_eq_mkRat]
  have hp : (-(p : ℤ)).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
  rw [Rat.cast_mkRat_of_ne_zero]
  · simp [hp, Nat.shiftLeft_eq]
  · simp [Nat.shiftLeft_eq]

theorem sqrtGrid_bounds (d : Dyadic) (prec : ℕ) :
    Dyadic.toReal (Dyadic.ofIntWithPrec (sqrtGrid d prec : ℤ) (prec : ℤ)) ≤ Real.sqrt (Dyadic.toReal d) ∧
      Real.sqrt (Dyadic.toReal d) ≤
        Dyadic.toReal (Dyadic.ofIntWithPrec ((sqrtGrid d prec + 1 : ℕ) : ℤ) (prec : ℤ)) := by
  let m : ℚ := max d.toRat 0 * (2 : ℚ) ^ (2 * prec)
  have hm : 0 ≤ m := by positivity
  have hfloor := Nat.floor_le hm
  have hfloor' := Nat.lt_floor_add_one m
  have hlo := Nat.sqrt_le' ⌊m⌋₊
  have hhi := Nat.lt_succ_sqrt' ⌊m⌋₊
  have hb : ((sqrtGrid d prec : ℕ) : ℚ) ^ 2 ≤ m := by
    exact le_trans (by exact_mod_cast hlo) hfloor
  have ht : m < ((sqrtGrid d prec : ℚ) + 1) ^ 2 := by
    apply hfloor'.trans_le
    exact_mod_cast hhi
  have hbR : (sqrtGrid d prec : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hb
  have htR : (m : ℝ) ≤ ((sqrtGrid d prec : ℝ) + 1) ^ 2 := by exact_mod_cast ht.le
  have hmR : (m : ℝ) = max (Dyadic.toReal d) 0 * (2 : ℝ) ^ (2 * prec) := by
    simp [m, Dyadic.toReal, Rat.cast_max]
  rw [hmR, mul_comm 2 prec, pow_mul] at hbR htR
  rw [toReal_of_grid, toReal_of_grid]
  have hd : Real.sqrt (max (Dyadic.toReal d) 0) = Real.sqrt (Dyadic.toReal d) := by
    by_cases h : 0 ≤ Dyadic.toReal d
    · rw [max_eq_left h]
    · rw [max_eq_right (le_of_not_ge h), Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
  rw [← hd, Nat.cast_add, Nat.cast_one]
  constructor
  · apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact hbR
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact htR

/-- Apply integer square-root rounding to each finite endpoint. -/
def sqrtInterval (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic where
  lb := match I.lb with
    | some l => Dyadic.ofIntWithPrec (sqrtGrid l prec) prec
    | ⊥ => 0
  ub := match I.ub with
    | some u => Dyadic.ofIntWithPrec ((sqrtGrid u prec + 1 : ℕ) : ℤ) prec
    | ⊤ => ⊤

@[inclusion_op interval_dyadic_real]
theorem sqrt_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.sqrt x ∈ sqrtInterval I prec := by
  rw [mem_iff_mem_map, Interval.mem_map_iff] at hx ⊢
  rcases I with ⟨l, u⟩
  constructor
  · intro d hd
    cases l with
    | bot =>
      simp [sqrtInterval] at hd
      rw [hd, show Dyadic.toReal 0 = 0 from map_zero Dyadic.toRealAddMonoidHom]
      exact Real.sqrt_nonneg x
    | coe l =>
      simp [sqrtInterval] at hd
      rw [← hd]
      exact (sqrtGrid_bounds l prec).1.trans (Real.sqrt_le_sqrt (hx.1 l rfl))
  · intro d hd
    cases u with
    | top => simp [sqrtInterval] at hd
    | coe u =>
      simp [sqrtInterval] at hd
      rw [← hd]
      exact (Real.sqrt_le_sqrt (hx.2 u rfl)).trans (sqrtGrid_bounds u prec).2

end Inclusion.IntervalDyadicReal
