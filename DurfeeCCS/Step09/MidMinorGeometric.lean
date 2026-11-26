module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The geometric decomposition of the angular modes in (61). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex
open scoped ComplexConjugate

def midMinorWeight (j : ℕ) (u t : ℝ) (m : ℤ) : ℝ :=
  Real.exp (-(j : ℝ) * |((m : ℝ) + 1 / 2) * u - t|)

def midMinorPhase (x : ℝ) : ℂ := exp ((x : ℂ) * I)

def midMinorTerm (j : ℕ) (u t v : ℝ) (m : ℤ) : ℂ :=
  (midMinorWeight j u t m : ℂ) * midMinorPhase ((j : ℝ) * m * v)

def midMinorMode (j : ℕ) (u t v : ℝ) : ℂ :=
  ∑' m : ℕ, midMinorTerm j u t v m

theorem midMinorPhase_add (x y : ℝ) :
    midMinorPhase (x + y) = midMinorPhase x * midMinorPhase y := by
  simp only [midMinorPhase, Complex.ofReal_add, add_mul, exp_add]

@[simp] theorem midMinorPhase_zero : midMinorPhase 0 = 1 := by simp [midMinorPhase]

theorem conj_midMinorPhase (x : ℝ) : conj (midMinorPhase x) = midMinorPhase (-x) := by
  rw [midMinorPhase, ← exp_conj]
  simp [midMinorPhase]

theorem midMinorPhase_nat_mul (x : ℝ) (m : ℕ) :
    midMinorPhase ((m : ℝ) * x) = midMinorPhase x ^ m := by
  rw [midMinorPhase, midMinorPhase, ← exp_nat_mul]
  congr 1
  push_cast
  ring

@[simp] theorem norm_midMinorPhase (x : ℝ) : ‖midMinorPhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

@[simp] theorem norm_midMinorTerm (j : ℕ) (u t v : ℝ) (m : ℤ) :
    ‖midMinorTerm j u t v m‖ = midMinorWeight j u t m := by
  rw [midMinorTerm, norm_mul, norm_midMinorPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_pos (Real.exp_pos _)

theorem summable_midMinorWeight {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u) (t : ℝ) :
    Summable (fun m : ℕ => midMinorWeight j u t m) := by
  let a : ℝ := (j : ℝ) * u
  have ha : 0 < a := mul_pos (by exact_mod_cast hj) hu
  have hq : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  apply ((summable_geometric_of_lt_one (Real.exp_nonneg _) hq).mul_left
    (Real.exp ((j : ℝ) * (t - u / 2)))).of_nonneg_of_le (fun _ => Real.exp_nonneg _)
  intro m
  change Real.exp (-(j : ℝ) * |((m : ℝ) + 1 / 2) * u - t|) ≤
    Real.exp ((j : ℝ) * (t - u / 2)) * Real.exp (-a) ^ m
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonpos_left (le_abs_self (((m : ℝ) + 1 / 2) * u - t))
    (neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) j))
  dsimp [a]
  nlinarith only [h]

theorem summable_norm_midMinorTerm {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u)
    (t v : ℝ) : Summable (fun m : ℕ => ‖midMinorTerm j u t v m‖) := by
  simpa using summable_midMinorWeight hj hu t

theorem midMinorMode_neg (j : ℕ) (u t v : ℝ) :
    midMinorMode j u t (-v) = conj (midMinorMode j u t v) := by
  rw [midMinorMode, midMinorMode, Complex.conj_tsum]
  apply tsum_congr
  intro m
  simp only [midMinorTerm, map_mul, Complex.conj_ofReal, conj_midMinorPhase]
  congr 2
  ring

theorem midMinorMode_zero (j : ℕ) (u t : ℝ) :
    midMinorMode j u t 0 = ((∑' m : ℕ, midMinorWeight j u t m : ℝ) : ℂ) := by
  rw [midMinorMode, Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  simp [midMinorTerm]

theorem norm_midMinorMode_le_zero {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u) (t v : ℝ) :
    ‖midMinorMode j u t v‖ ≤ ∑' m : ℕ, midMinorWeight j u t m := by
  simpa only [midMinorMode, norm_midMinorTerm] using
    norm_tsum_le_tsum_norm (summable_norm_midMinorTerm hj hu t v)

private def centeredTerm (a τ b : ℝ) (m : ℤ) : ℂ :=
  (Real.exp (-a * |(m : ℝ) - τ|) : ℂ) * midMinorPhase ((m : ℝ) * b)

private theorem centeredTerm_nonpos {a τ b : ℝ} (hτ : 0 ≤ τ) (k : ℕ) :
    centeredTerm a τ b (-(k : ℤ)) =
      (Real.exp (-a * τ) : ℂ) * ((Real.exp (-a) : ℂ) * midMinorPhase (-b)) ^ k := by
  have h : -(k : ℝ) - τ ≤ 0 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  simp only [centeredTerm, Int.cast_neg, Int.cast_natCast, abs_of_nonpos h, mul_pow]
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, ← midMinorPhase_nat_mul]
  have h₁ : -a * (-(-(k : ℝ) - τ)) = -a * τ + (k : ℝ) * -a := by ring
  rw [h₁, Real.exp_add, Complex.ofReal_mul]
  have h₂ : -(k : ℝ) * b = (k : ℝ) * -b := by ring
  rw [h₂, mul_assoc]

private theorem centeredTerm_pos {a τ b : ℝ} (hτ : τ ≤ 1) (k : ℕ) :
    centeredTerm a τ b ((k : ℤ) + 1) =
      ((Real.exp (-a * (1 - τ)) : ℂ) * midMinorPhase b) *
        ((Real.exp (-a) : ℂ) * midMinorPhase b) ^ k := by
  have h : 0 ≤ (k : ℝ) + 1 - τ := by linarith [Nat.cast_nonneg (α := ℝ) k]
  simp only [centeredTerm, Int.cast_add, Int.cast_one, Int.cast_natCast, abs_of_nonneg h, mul_pow]
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, ← midMinorPhase_nat_mul]
  have h₁ : -a * ((k : ℝ) + 1 - τ) = -a * (1 - τ) + (k : ℝ) * -a := by ring
  rw [h₁, Real.exp_add, Complex.ofReal_mul]
  have h₂ : ((k : ℝ) + 1) * b = b + (k : ℝ) * b := by ring
  rw [h₂, midMinorPhase_add]
  ring

private theorem norm_midMinorRatio {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ‖(Real.exp (-a) : ℂ) * midMinorPhase b‖ < 1 := by
  rw [norm_mul, norm_midMinorPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_lt_one_iff.mpr (by linarith)

private theorem centeredTerm_sum {a τ b : ℝ} (ha : 0 < a) (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 1) :
    HasSum (centeredTerm a τ b)
      ((Real.exp (-a * τ) : ℂ) / (1 - (Real.exp (-a) : ℂ) * midMinorPhase (-b)) +
       (Real.exp (-a * (1 - τ)) : ℂ) * midMinorPhase b /
        (1 - (Real.exp (-a) : ℂ) * midMinorPhase b)) := by
  have hp := (hasSum_geometric_of_norm_lt_one (norm_midMinorRatio ha b)).mul_left
    ((Real.exp (-a * (1 - τ)) : ℂ) * midMinorPhase b)
  have hn := (hasSum_geometric_of_norm_lt_one (norm_midMinorRatio ha (-b))).mul_left
    (Real.exp (-a * τ) : ℂ)
  have hp' : HasSum (fun m : ℕ => centeredTerm a τ b ((m : ℤ) + 1))
      ((Real.exp (-a * (1 - τ)) : ℂ) * midMinorPhase b /
        (1 - (Real.exp (-a) : ℂ) * midMinorPhase b)) := by
    simpa only [centeredTerm_pos hτ₁, div_eq_mul_inv] using hp
  have hn' : HasSum (fun m : ℕ => centeredTerm a τ b (-(m : ℤ)))
      ((Real.exp (-a * τ) : ℂ) / (1 - (Real.exp (-a) : ℂ) * midMinorPhase (-b))) := by
    simpa only [centeredTerm_nonpos hτ₀, div_eq_mul_inv] using hn
  let f := centeredTerm a τ b
  apply (Equiv.neg ℤ).hasSum_iff.mp
  refine HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => f (-k)) hn' ?_
  simpa only [neg_neg] using hp'

theorem midMinor_denominator (a b : ℝ) :
    Real.cosh a - Real.cos b =
      2 * Real.sinh (a / 2) ^ 2 + 2 * Real.sin (b / 2) ^ 2 := by
  have hC : Real.cosh a = 1 + 2 * Real.sinh (a / 2) ^ 2 := by
    have h := Real.cosh_add (a / 2) (a / 2)
    rw [show a / 2 + a / 2 = a by ring] at h
    nlinarith only [h, Real.cosh_sq_sub_sinh_sq (a / 2)]
  have hc : Real.cos b = 1 - 2 * Real.sin (b / 2) ^ 2 := by
    simpa only [show 2 * (b / 2) = b by ring] using Real.cos_two_mul_eq_one_sub (b / 2)
  rw [hC, hc]
  ring

theorem midMinor_denominator_pos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    0 < Real.cosh a - Real.cos b := by
  have hc := Real.one_lt_cosh.mpr ha.ne'
  linarith [Real.cos_le_one b]

private theorem midMinorPhase_sum (b : ℝ) :
    midMinorPhase b + midMinorPhase (-b) = 2 * (Real.cos b : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  simp only [midMinorPhase, Complex.ofReal_neg, neg_mul]
  ring

private theorem denominator_product (a b : ℝ) :
    (1 - (Real.exp (-a) : ℂ) * midMinorPhase (-b)) *
      (1 - (Real.exp (-a) : ℂ) * midMinorPhase b) =
    ((2 * Real.exp (-a) * (Real.cosh a - Real.cos b) : ℝ) : ℂ) := by
  let q : ℂ := Real.exp (-a)
  let X := midMinorPhase b
  let Y := midMinorPhase (-b)
  have hXY : Y * X = 1 := by rw [← midMinorPhase_add, neg_add_cancel, midMinorPhase_zero]
  have hsum := midMinorPhase_sum b
  have hq : (Real.exp (-a) : ℂ) * (Real.exp a : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  calc
    _ = 1 - q * (X + Y) + q ^ 2 * (Y * X) := by
      change (1 - q * Y) * (1 - q * X) = _
      ring
    _ = _ := by
      rw [hXY, show X + Y = _ from hsum, Real.cosh_eq]
      dsimp only [q]
      simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_div,
        Complex.ofReal_add]
      linear_combination -hq

private theorem centeredTerm_sum_sinh {a τ b : ℝ} (ha : 0 < a) (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 1) :
    HasSum (centeredTerm a τ b)
      (((Real.sinh (a * (1 - τ)) : ℂ) + midMinorPhase b * (Real.sinh (a * τ) : ℂ)) /
        (↑(Real.cosh a - Real.cos b) : ℂ)) := by
  convert centeredTerm_sum (b := b) ha hτ₀ hτ₁ using 1
  symm
  let q : ℂ := Real.exp (-a)
  let X := midMinorPhase b
  let Y := midMinorPhase (-b)
  let A : ℂ := Real.exp (-a * τ)
  let B : ℂ := Real.exp (-a * (1 - τ))
  let D : ℂ := (↑(Real.cosh a - Real.cos b) : ℂ)
  have hXY : X * Y = 1 := by rw [← midMinorPhase_add, add_neg_cancel, midMinorPhase_zero]
  have hq : q ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hD : D ≠ 0 := Complex.ofReal_ne_zero.mpr (midMinor_denominator_pos ha b).ne'
  have hX : 1 - q * X ≠ 0 := sub_ne_zero_of_ne (fun he => by
    have h := norm_midMinorRatio ha b
    change ‖q * X‖ < 1 at h
    rw [← he, norm_one] at h
    exact (lt_irrefl _ h))
  have hY : 1 - q * Y ≠ 0 := sub_ne_zero_of_ne (fun he => by
    have h := norm_midMinorRatio ha (-b)
    change ‖q * Y‖ < 1 at h
    rw [← he, norm_one] at h
    exact (lt_irrefl _ h))
  have hprod : (1 - q * Y) * (1 - q * X) = 2 * q * D := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using denominator_product a b
  have hSinh (x : ℝ) : (2 : ℝ) * Real.exp (-a) * Real.sinh x =
      Real.exp (-a+x) - Real.exp (-a-x) := by
    rw [Real.sinh_eq, Real.exp_add, sub_eq_add_neg (-a), Real.exp_add]
    ring
  have hA : A - B * q = 2 * q * (Real.sinh (a * (1 - τ)) : ℂ) := by
    have h : Real.exp (-a * τ) - Real.exp (-a * (1-τ)) * Real.exp (-a) =
        2 * Real.exp (-a) * Real.sinh (a*(1-τ)) := by
      rw [hSinh, ← Real.exp_add]
      congr 1 <;> congr 1 <;> ring
    simpa only [A, B, q, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat]
      using congrArg Complex.ofReal h
  have hB : B - A * q = 2 * q * (Real.sinh (a * τ) : ℂ) := by
    have h : Real.exp (-a * (1-τ)) - Real.exp (-a * τ) * Real.exp (-a) =
        2 * Real.exp (-a) * Real.sinh (a*τ) := by
      rw [hSinh, ← Real.exp_add]
      congr 1 <;> congr 1 <;> ring
    simpa only [A, B, q, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat]
      using congrArg Complex.ofReal h
  change A / (1 - q * Y) + B * X / (1 - q * X) = _
  rw [div_add_div _ _ hY hX, hprod]
  have hn : A * (1 - q * X) + (1 - q * Y) * (B * X) = (A - B * q) + X * (B - A * q) := by
    calc
      _ = A + B * X - A * q * X - B * q * (X * Y) := by ring
      _ = _ := by rw [hXY]; ring
  rw [hn, hA, hB]
  change _ = ((Real.sinh (a * (1 - τ)) : ℂ) + X * (Real.sinh (a * τ) : ℂ)) / D
  field_simp

private theorem midMinorTerm_shift (j : ℕ) {u : ℝ} (hu : 0 < u) (t v : ℝ)
    (k m : ℤ) (τ : ℝ) (hτ : t / u - 1 / 2 = (k : ℝ) + τ) :
    midMinorTerm j u t v (m + k) =
      midMinorPhase ((j : ℝ) * k * v) * centeredTerm ((j : ℝ) * u) τ ((j : ℝ) * v) m := by
  have ht : t = ((k : ℝ) + τ + 1 / 2) * u := by
    have h : t / u = (k : ℝ) + τ + 1 / 2 := by linarith only [hτ]
    exact (div_eq_iff hu.ne').mp h
  have hArg : (((m + k : ℤ) : ℝ) + 1 / 2) * u - t = ((m : ℝ) - τ) * u := by
    push_cast
    rw [ht]
    ring
  have hAng : (j : ℝ) * ((m + k : ℤ) : ℝ) * v =
      (j : ℝ) * k * v + (m : ℝ) * ((j : ℝ) * v) := by push_cast; ring
  rw [midMinorTerm, midMinorWeight, centeredTerm, hArg, abs_mul, abs_of_pos hu, hAng,
    midMinorPhase_add]
  have hEx : -(j : ℝ) * (|(m : ℝ) - τ| * u) = -((j : ℝ) * u) * |(m : ℝ) - τ| := by ring
  rw [hEx]
  ring

theorem midMinor_bilateral {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u) (t v : ℝ) :
    let k := ⌊t / u - 1 / 2⌋
    let τ := t / u - 1 / 2 - (k : ℝ)
    let a := (j : ℝ) * u
    let b := (j : ℝ) * v
    HasSum (midMinorTerm j u t v)
      (midMinorPhase ((j : ℝ) * k * v) *
        ((Real.sinh (a * (1 - τ)) : ℂ) + midMinorPhase b * (Real.sinh (a * τ) : ℂ)) /
        (↑(Real.cosh a - Real.cos b) : ℂ)) := by
  let k := ⌊t / u - 1 / 2⌋
  let τ := t / u - 1 / 2 - (k : ℝ)
  let a := (j : ℝ) * u
  let b := (j : ℝ) * v
  have ha : 0 < a := mul_pos (by exact_mod_cast hj) hu
  have hτ : 0 ≤ τ := sub_nonneg.mpr (Int.floor_le _)
  have hτ₁ : τ ≤ 1 := by
    exact (Int.fract_lt_one (t / u - 1 / 2)).le
  have hc := (centeredTerm_sum_sinh (b := b) ha hτ hτ₁).mul_left
    (midMinorPhase ((j : ℝ) * k * v))
  have hshift (m : ℤ) := midMinorTerm_shift j hu t v k m τ (by dsimp only [τ]; ring)
  apply (Equiv.addRight k).hasSum_iff.mp
  change HasSum (fun m => midMinorTerm j u t v (m + k)) _
  simp_rw [hshift, mul_div_assoc]
  exact hc

theorem midMinor_negative_half {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u)
    {t : ℝ} (ht : 0 ≤ t) (v : ℝ) :
    let a := (j : ℝ) * u
    let b := (j : ℝ) * v
    HasSum (fun m : ℕ => midMinorTerm j u t v (-((m : ℤ) + 1)))
      ((Real.exp (-(j : ℝ) * t - a / 2) : ℂ) * midMinorPhase (-b) /
        (1 - (Real.exp (-a) : ℂ) * midMinorPhase (-b))) := by
  let a := (j : ℝ) * u
  let b := (j : ℝ) * v
  have ha : 0 < a := mul_pos (by exact_mod_cast hj) hu
  have hG := (hasSum_geometric_of_norm_lt_one (norm_midMinorRatio ha (-b))).mul_left
    ((Real.exp (-(j : ℝ) * t - a / 2) : ℂ) * midMinorPhase (-b))
  convert hG using 1
  · funext m
    simp only [midMinorTerm, midMinorWeight, Int.cast_neg, Int.cast_add, Int.cast_natCast,
      Int.cast_one, mul_pow, ← Complex.ofReal_pow, ← Real.exp_nat_mul, ← midMinorPhase_nat_mul]
    have hn : (-(↑m + 1 : ℝ) + 1 / 2) * u - t ≤ 0 := by
      have hm := Nat.cast_nonneg (α := ℝ) m
      nlinarith only [mul_nonneg hm hu.le, hu,ht]
    rw [abs_of_nonpos hn]
    have hEx : -(j : ℝ) * (-((-(↑m + 1 : ℝ) + 1 / 2) * u - t)) =
        -(j : ℝ) * t - a / 2 + (m : ℝ) * -a := by dsimp only [a]; ring
    have hAngle : (j : ℝ) * (-(↑m + 1 : ℝ)) * v = -b + (m : ℝ) * -b := by dsimp only [b]; ring
    rw [hEx,hAngle, Real.exp_add, Complex.ofReal_mul, midMinorPhase_add]
    ring
  · exact div_eq_mul_inv _ _

private theorem radius_denominator_norm_sq (a b : ℝ) :
    ‖1 - (Real.exp (-a) : ℂ) * midMinorPhase (-b)‖ ^ 2 =
      2 * Real.exp (-a) * (Real.cosh a - Real.cos b) := by
  let z : ℂ := 1 - (Real.exp (-a) : ℂ) * midMinorPhase (-b)
  have h := Complex.mul_conj z
  rw [Complex.normSq_eq_norm_sq] at h
  have hz : conj z = 1 - (Real.exp (-a) : ℂ) * midMinorPhase b := by
    simp only [z, map_sub, map_one, map_mul, Complex.conj_ofReal, conj_midMinorPhase, neg_neg]
  rw [hz] at h
  apply Complex.ofReal_injective
  change ((‖z‖ ^ 2 : ℝ) : ℂ) = _
  rw [← h]
  exact denominator_product a b

private theorem scale_half_exp (a : ℝ) :
    1 - Real.exp (-a) = Real.exp (-a / 2) * (2 * Real.sinh (a / 2)) := by
  rw [Real.sinh_eq, show (2:ℝ) * ((Real.exp (a/2) - Real.exp (-(a/2))) / 2) =
    Real.exp (a/2) - Real.exp (-(a/2)) by ring, mul_sub, ← Real.exp_add, ← Real.exp_add]
  rw [show -a/2 + a/2 = 0 by ring, Real.exp_zero, show -a/2 + -(a/2) = -a by ring]

private theorem negative_half_norm {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u)
    {t : ℝ} (ht : 0 ≤ t) (v : ℝ) :
    ‖∑' m : ℕ, midMinorTerm j u t v (-((m : ℤ) + 1))‖ =
      Real.exp (-(j : ℝ) * t) /
        Real.sqrt (2 * (Real.cosh ((j : ℝ) * u) - Real.cos ((j : ℝ) * v))) := by
  let a := (j : ℝ) * u
  let b := (j : ℝ) * v
  have ha : 0 < a := mul_pos (by exact_mod_cast hj) hu
  have hD : 0 < Real.cosh a - Real.cos b := midMinor_denominator_pos ha b
  let z : ℂ := 1 - (Real.exp (-a) : ℂ) * midMinorPhase (-b)
  have hz : ‖z‖ = Real.exp (-a / 2) * Real.sqrt (2 * (Real.cosh a - Real.cos b)) := by
    have h : ‖z‖ ^ 2 = (Real.exp (-a / 2) * Real.sqrt (2 * (Real.cosh a - Real.cos b))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
      change ‖1 - (Real.exp (-a) : ℂ) * midMinorPhase (-b)‖ ^ 2 = _
      rw [radius_denominator_norm_sq, Nat.cast_ofNat, show (2:ℝ) * (-a/2) = -a by ring]
      ring
    exact le_antisymm ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h.le)
      ((sq_le_sq₀ (by positivity) (norm_nonneg _)).mp h.ge)
  rw [(midMinor_negative_half hj hu ht v).tsum_eq, norm_div, norm_mul,
    norm_midMinorPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
  change |Real.exp (-(j : ℝ) * t - a / 2)| / ‖z‖ =
    Real.exp (-(j : ℝ) * t) / Real.sqrt (2 * (Real.cosh a - Real.cos b))
  rw [abs_of_pos (Real.exp_pos _), sub_eq_add_neg, ← neg_div, Real.exp_add, hz]
  field_simp

private theorem negative_half_zero {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑' m : ℕ, midMinorTerm j u t 0 (-((m : ℤ) + 1))) =
      (↑(Real.exp (-(j : ℝ) * t) / (2 * Real.sinh ((j : ℝ) * u / 2))) : ℂ) := by
  let a := (j : ℝ) * u
  have ha : 0 < a := mul_pos (by exact_mod_cast hj) hu
  have hs : 0 < Real.sinh (a/2) := Real.sinh_pos_iff.mpr (by positivity)
  rw [(midMinor_negative_half hj hu ht 0).tsum_eq]
  simp only [mul_zero, neg_zero, midMinorPhase_zero, mul_one]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div]
  congr 1
  change Real.exp (-(j : ℝ) * t - a / 2) / (1 - Real.exp (-a)) = _
  rw [scale_half_exp, sub_eq_add_neg, ← neg_div, Real.exp_add]
  dsimp only [a]
  field_simp

private theorem midMinor_split {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u) {t : ℝ}
    (ht : 0 ≤ t) (v : ℝ) :
    (∑' m : ℤ, midMinorTerm j u t v m) =
      midMinorMode j u t v + ∑' m : ℕ, midMinorTerm j u t v (-((m : ℤ) + 1)) :=
  tsum_of_nat_of_neg_add_one (summable_norm_midMinorTerm hj hu t v).of_norm
    (midMinor_negative_half hj hu ht v).summable

private theorem midMinor_sinh_split {a τ : ℝ} (ha : 0 ≤ a) (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 1) :
    Real.sinh (a * (1 - τ)) + Real.sinh (a * τ) ≤ Real.sinh a := by
  have hx : 0 ≤ a * (1 - τ) := by positivity
  have hy : 0 ≤ a * τ := by positivity
  have h := Real.sinh_add (a * (1 - τ)) (a * τ)
  rw [show a * (1 - τ) + a * τ = a by ring] at h
  have h₁ := mul_le_mul_of_nonneg_left (Real.one_le_cosh (a*τ)) (Real.sinh_nonneg_iff.mpr hx)
  have h₂ := mul_le_mul_of_nonneg_right (Real.one_le_cosh (a*(1-τ))) (Real.sinh_nonneg_iff.mpr hy)
  simp only [one_mul, mul_one] at h₁ h₂
  linarith only [h,h₁,h₂]

private theorem midMinor_bilateral_norm {j : ℕ} (hj : 0 < j) {u : ℝ}
    (hu : 0 < u) (t v : ℝ) :
    ‖∑' m : ℤ, midMinorTerm j u t v m‖ ≤
      Real.sinh ((j : ℝ) * u) / (Real.cosh ((j : ℝ) * u) - Real.cos ((j : ℝ) * v)) := by
  let k := ⌊t / u - 1 / 2⌋
  let τ := t / u - 1 / 2 - (k : ℝ)
  let a := (j : ℝ) * u
  let b := (j : ℝ) * v
  have ha : 0 < a := mul_pos (by exact_mod_cast hj) hu
  have hτ : 0 ≤ τ := sub_nonneg.mpr (Int.floor_le _)
  have hτ₁ : τ ≤ 1 := by
    exact (Int.fract_lt_one (t / u - 1 / 2)).le
  have hx : 0 ≤ Real.sinh (a * (1 - τ)) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hy : 0 ≤ Real.sinh (a * τ) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hD := midMinor_denominator_pos ha b
  rw [(midMinor_bilateral hj hu t v).tsum_eq, norm_div, norm_mul, norm_midMinorPhase, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  apply div_le_div_of_nonneg_right _ hD.le
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_midMinorPhase, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg hy]
  exact midMinor_sinh_split ha.le hτ hτ₁

/-- The oscillatory bound in (61). -/
theorem norm_midMinorMode_le_oscillatory {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u)
    {t : ℝ} (ht : 0 ≤ t) (v : ℝ) :
    let a := (j : ℝ) * u
    let b := (j : ℝ) * v
    let D := Real.cosh a - Real.cos b
    ‖midMinorMode j u t v‖ ≤
      Real.sinh a / D + Real.exp (-(j : ℝ) * t) / Real.sqrt (2 * D) := by
  dsimp only
  have he := midMinor_split hj hu ht v
  have h := norm_sub_le (∑' m : ℤ, midMinorTerm j u t v m)
    (∑' m : ℕ, midMinorTerm j u t v (-((m : ℤ) + 1)))
  rw [eq_sub_of_add_eq he.symm]
  exact h.trans (add_le_add (midMinor_bilateral_norm hj hu t v) (negative_half_norm hj hu ht v).le)

/-- The upper bound from the positive sums at zero in (61). -/
theorem norm_midMinorMode_le_positive {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u)
    {t : ℝ} (ht : 0 ≤ t) (v : ℝ) :
    let a := (j : ℝ) * u
    ‖midMinorMode j u t v‖ ≤ Real.cosh (a / 2) / Real.sinh (a / 2) -
      Real.exp (-(j : ℝ) * t) / (2 * Real.sinh (a / 2)) := by
  let a := (j : ℝ) * u
  have ha : 0 < a := mul_pos (by exact_mod_cast hj) hu
  have hs : 0 < Real.sinh (a/2) := Real.sinh_pos_iff.mpr (by positivity)
  have h := midMinor_split hj hu ht 0
  rw [midMinorMode_zero, negative_half_zero hj hu ht] at h
  have hn := midMinor_bilateral_norm hj hu t 0
  rw [h, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs] at hn
  have hnon : 0 ≤ (∑' m : ℕ, midMinorWeight j u t m) +
      Real.exp (-(j : ℝ) * t) / (2 * Real.sinh (a / 2)) :=
    add_nonneg (tsum_nonneg (fun _ => Real.exp_nonneg _))
      (div_nonneg (Real.exp_nonneg _) (by positivity))
  rw [abs_of_nonneg hnon] at hn
  have hC : Real.sinh a / (Real.cosh a - Real.cos ((j : ℝ) * 0)) =
      Real.cosh (a / 2) / Real.sinh (a / 2) := by
    rw [mul_zero, midMinor_denominator, zero_div, Real.sin_zero]
    have hS : Real.sinh a = 2 * Real.sinh (a/2) * Real.cosh (a/2) := by
      have ha' := Real.sinh_add (a/2) (a/2)
      rw [show a/2+a/2=a by ring] at ha'
      linarith only [ha']
    rw [hS]
    norm_num
    field_simp
  change _ ≤ Real.sinh a / (Real.cosh a - Real.cos ((j : ℝ) * 0)) at hn
  rw [hC] at hn
  exact (norm_midMinorMode_le_zero hj hu t v).trans (le_sub_iff_add_le.mpr hn)

/-- Both estimates in (61), with (a=ju) and (b=jv). -/
theorem norm_midMinorMode_le_min {j : ℕ} (hj : 0 < j) {u : ℝ} (hu : 0 < u) {t : ℝ}
    (ht : 0 ≤ t) (v : ℝ) :
    let a := (j : ℝ) * u
    let b := (j : ℝ) * v
    let D := Real.cosh a - Real.cos b
    ‖midMinorMode j u t v‖ ≤
      min (Real.cosh (a/2) / Real.sinh (a/2) - Real.exp (-(j:ℝ)*t) / (2 * Real.sinh (a/2)))
        (Real.sinh a / D + Real.exp (-(j:ℝ)*t) / Real.sqrt (2 * D)) :=
  le_min (norm_midMinorMode_le_positive hj hu ht v) (norm_midMinorMode_le_oscillatory hj hu ht v)

end DurfeeCCS.Step09
