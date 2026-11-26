module

public import DurfeeCCS.Step10.OuterReplacement
public import DurfeeCCS.Step10.OuterCoeff
public import DurfeeCCS.Step10.OuterFarData
public import DurfeeCCS.Step10.OuterEulerTail

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Cauchy–Schwarz and the concave square-root majorant in the preprocessing estimates. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step10

open Real Finset

/-- The two-variable Cauchy–Schwarz inequality used with the shifted Durfee index. -/
theorem outerPreprocessing_cauchy {h c x t V : ℝ}
    (hh : 0 ≤ h) (hc : 0 ≤ c) (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hV : x ^ 2 + t = V) :
    h * x + c * sqrt t ≤ sqrt (h ^ 2 + c ^ 2) * sqrt V := by
  have hV₀ : 0 ≤ V := hV ▸ add_nonneg (sq_nonneg _) ht
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hV₀, ← hV]
  have hs := sq_nonneg (h * sqrt t - c * x)
  have hEq : (h ^ 2 + c ^ 2) * (x ^ 2 + t) - (h * x + c * sqrt t) ^ 2 =
      (h * sqrt t - c * x) ^ 2 := by
    linear_combination -(h ^ 2 + c ^ 2) * Real.sq_sqrt ht
  linarith only [hEq, hs]

private theorem sqrt_baseRadius_bounds {Y N : ℝ} (hY : 80 ≤ Y)
    (hN : N = Y ^ 2 + 1 / 12) :
    sqrt N ≤ Y + 1 / (24 * Y) ∧ sqrt N ≤ (1001 / 1000) * Y := by
  have hY₀ : 0 < Y := by linarith
  have hN₀ : 0 ≤ N := by rw [hN]; positivity
  have hs : (sqrt N) ^ 2 = N := Real.sq_sqrt hN₀
  have h₁ : sqrt N ≤ Y + 1 / (24 * Y) := by
    have ht := sq_nonneg (sqrt N - Y)
    have haux : sqrt N - Y ≤ 1 / (24 * Y) := by
      apply (le_div_iff₀ (by positivity : 0 < 24 * Y)).mpr
      nlinarith only [ht, hs, hN]
    linarith only [haux]
  have h₂ : 1 / (24 * Y) ≤ (1 / 1000) * Y := by
    have hYsq : (80 : ℝ) ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (by norm_num) hY 2
    apply (div_le_iff₀ (by positivity : 0 < 24 * Y)).mpr
    nlinarith only [hYsq]
  exact ⟨h₁, by linarith only [h₁, h₂]⟩

/-- A uniform concave majorant for the shifted radius, split at the coefficient index.
Here `N` is the unshifted size and `Y² = N - 1/12`. -/
theorem outerSwap_sqrtRadius_le {Y N γ j : ℝ}
    (hY : 80 ≤ Y) (hN : N = Y ^ 2 + 1 / 12) (hj : 0 ≤ j) (hγ : j ≤ γ)
    (hNγ : 0 ≤ N - γ) :
    sqrt (N - γ) ≤ Y + 1 / (24 * Y) - j / (3 * Y) := by
  have hY₀ : 0 < Y := by linarith
  have hN₀ : 0 < N := by rw [hN]; positivity
  have hNγ₀ := Real.sq_sqrt hNγ
  have hNs := Real.sq_sqrt hN₀.le
  have hS : 0 < sqrt N := Real.sqrt_pos.mpr hN₀
  obtain ⟨hUpper, hUpper'⟩ := sqrt_baseRadius_bounds hY hN
  have hC : sqrt (N - γ) - sqrt N ≤ -γ / (2 * sqrt N) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * sqrt N)).mpr
    nlinarith only [sq_nonneg (sqrt (N - γ) - sqrt N), hNγ₀, hNs]
  have hDiv : j / (3 * Y) ≤ γ / (2 * sqrt N) := by
    apply div_le_div₀ (hj.trans hγ) hγ (by positivity)
    linarith only [hUpper', hY₀]
  rw [neg_div] at hC
  linarith only [hC, hDiv, hUpper]

/-- The coefficient-minus-kernel term at a negative shifted index vanishes exactly. -/
theorem outerKernelReplacement_neg_index {Y x : ℝ} {t : ℤ}
    (ht : t < 0) (hIndex : Y ^ 2 - x ^ 2 = (t : ℝ) - 1 / 12) :
    clippedTwoColour t - outerBesselKernel Y x = 0 := by
  have htR : (t : ℝ) < 0 := by exact_mod_cast ht
  have hK : ¬ x ^ 2 ≤ Y ^ 2 := by linarith only [hIndex, htR]
  simp [clippedTwoColour, not_le.mpr ht, outerBesselKernel, hK]

/-- The Cauchy–Schwarz majorant for each term in the kernel replacement, before
summing over (d). -/
theorem outerSwap_weighted_term_le {n a b j d : ℕ} {y h : ℝ} {t : ℤ}
    (hY : 80 ≤ outerY n) (hN : (n : ℝ) = (outerY n) ^ 2 + 1 / 12)
    (hh : 0 < h) (hy : 0 ≤ y)
    (hySq : y ^ 2 = (outerY n) ^ 2 - outerGamma a b j)
    (hIndex : y ^ 2 - ((d : ℝ) + ((a : ℝ) + b) / 2) ^ 2 = (t : ℝ) - 1 / 12) :
    exp (h * (d : ℝ)) *
      |clippedTwoColour t - outerBesselKernel y ((d : ℝ) + ((a : ℝ) + b) / 2)| ≤
      (π ^ 3 / 18) *
        exp (((outerY n) + 1 / (24 * (outerY n))) * sqrt (h ^ 2 + π ^ 2 / 3)) *
        (exp (-h / 2)) ^ (a + b) *
        (exp (-(sqrt (h ^ 2 + π ^ 2 / 3) / (3 * (outerY n))))) ^ j := by
  let Y := outerY n
  let c := π / sqrt 3
  let u := sqrt (h ^ 2 + π ^ 2 / 3)
  let x := (d : ℝ) + ((a : ℝ) + b) / 2
  have hY₀ : 0 < Y := by linarith
  have hc : 0 ≤ c := by positivity
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hx : 0 ≤ x := by positivity
  by_cases ht : t < 0
  · rw [outerKernelReplacement_neg_index ht hIndex, abs_zero, mul_zero]
    positivity
  have ht' : 0 ≤ t := le_of_not_gt ht
  have htR : 0 ≤ (t : ℝ) := by exact_mod_cast ht'
  have htC : (t.toNat : ℝ) = t := by exact_mod_cast Int.toNat_of_nonneg ht'
  have hcSq : c ^ 2 = π ^ 2 / 3 := by
    unfold c
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have htSq : x ^ 2 + (t : ℝ) = (n : ℝ) - outerGamma a b j := by
    change y ^ 2 - x ^ 2 = (t : ℝ) - 1 / 12 at hIndex
    linarith only [hIndex, hN, hySq]
  have hV : 0 ≤ (n : ℝ) - outerGamma a b j := htSq ▸ add_nonneg (sq_nonneg _) htR
  have hΓ : (j : ℝ) ≤ outerGamma a b j :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ ((a : ℝ) + b) / 2)).trans
      (outerGamma_lower a b j)
  have hCau := outerPreprocessing_cauchy hh.le hc hx htR htSq
  rw [hcSq] at hCau
  have hCau' : h * x + c * sqrt (t : ℝ) ≤ u * ((Y + 1 / (24 * Y)) - (j : ℝ) / (3 * Y)) :=
    hCau.trans (mul_le_mul_of_nonneg_left
      (outerSwap_sqrtRadius_le hY hN (by positivity) hΓ hV) hu)
  have hArg : π * sqrt ((t.toNat : ℝ) / 3) = c * sqrt (t : ℝ) := by
    rw [htC, Real.sqrt_div htR]
    simp only [c]
    ring
  have hExp : h * (d : ℝ) + π * sqrt ((t.toNat : ℝ) / 3) ≤
      (Y + 1 / (24 * Y)) * u + (a + b : ℕ) * (-h / 2) + (j : ℝ) * -(u / (3 * Y)) := by
    rw [hArg, Nat.cast_add]
    calc
      _ = h * x + c * sqrt (t : ℝ) - h * ((a : ℝ) + b) / 2 := by dsimp [x]; ring
      _ ≤ u * ((Y + 1 / (24 * Y)) - (j : ℝ) / (3 * Y)) -
          h * ((a : ℝ) + b) / 2 := sub_le_sub_right hCau' _
      _ = _ := by ring
  have hRep := outerKernelReplacement (fun k hk => twoColour_bessel_error_unconditional hk) hy hIndex
  refine (mul_le_mul_of_nonneg_left hRep (Real.exp_nonneg _)).trans ?_
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  calc
    _ = (π ^ 3 / 18) * exp (h * (d : ℝ) + π * sqrt ((t.toNat : ℝ) / 3)) := by
      rw [Real.exp_add]
      ring
    _ ≤ (π ^ 3 / 18) * exp ((Y + 1 / (24 * Y)) * u +
        (a + b : ℕ) * (-h / 2) + (j : ℝ) * -(u / (3 * Y))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) (by positivity)
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

/-- The total error for one triple, bounded by the number of available positive
Durfee indices and the same geometric weight as the pointwise bound. -/
theorem outerSwap_weighted_sum_le {n a b j : ℕ} {y h : ℝ} {t : ℕ → ℤ}
    (hY : 80 ≤ outerY n) (hN : (n : ℝ) = (outerY n) ^ 2 + 1 / 12)
    (hh : 0 < h) (hy : 0 ≤ y)
    (hySq : y ^ 2 = (outerY n) ^ 2 - outerGamma a b j)
    (hIndex : ∀ d ∈ Finset.Icc 1 n.sqrt,
      y ^ 2 - ((d : ℝ) + ((a : ℝ) + b) / 2) ^ 2 = (t d : ℝ) - 1 / 12) :
    ∑ d ∈ Finset.Icc 1 n.sqrt, exp (h * (d : ℝ)) *
        |clippedTwoColour (t d) - outerBesselKernel y ((d : ℝ) + ((a : ℝ) + b) / 2)| ≤
      (2 * outerY n) * exp ((outerY n + 1 / (24 * outerY n)) * sqrt (h ^ 2 + π ^ 2 / 3)) *
        (exp (-h / 2)) ^ (a + b) *
        (exp (-(sqrt (h ^ 2 + π ^ 2 / 3) / (3 * outerY n)))) ^ j := by
  let Y := outerY n
  let u := sqrt (h ^ 2 + π ^ 2 / 3)
  let W := exp ((Y + 1 / (24 * Y)) * u) *
    (exp (-h / 2)) ^ (a + b) * (exp (-(u / (3 * Y)))) ^ j
  have hB : ((n.sqrt : ℕ) : ℝ) ≤ sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have h := Nat.sqrt_le n
    rw [pow_two]
    exact_mod_cast h
  have hN' : ((n.sqrt : ℕ) : ℝ) ≤ (1001 / 1000) * Y :=
    hB.trans (sqrt_baseRadius_bounds hY hN).2
  have hπ : (π : ℝ) ^ 3 / 18 ≤ (3.2 : ℝ) ^ 3 / 18 := by
    gcongr
    linarith only [Real.pi_lt_d4]
  have hSize : ((n.sqrt : ℕ) : ℝ) * (π ^ 3 / 18) ≤ 2 * Y := by
    calc
      _ ≤ ((1001 / 1000) * Y) * ((3.2 : ℝ) ^ 3 / 18) := by gcongr
      _ ≤ _ := by nlinarith only [hY]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 n.sqrt, (π ^ 3 / 18) * W := by
      apply Finset.sum_le_sum
      intro d hd
      have h := outerSwap_weighted_term_le hY hN hh hy hySq (hIndex d hd)
      simpa only [Y, u, W, mul_assoc] using h
    _ = (((n.sqrt : ℕ) : ℝ) * (π ^ 3 / 18)) * W := by
      rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
      ring
    _ ≤ (2 * Y) * W := mul_le_mul_of_nonneg_right hSize (by positivity)
    _ = _ := by dsimp only [W, u, Y]; ring

end DurfeeCCS.Step10
