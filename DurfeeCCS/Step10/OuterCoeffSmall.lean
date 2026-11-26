module

public import DurfeeCCS.Step10.OuterCoeffData
public import DurfeeCCS.Step06.TwoColour
import DurfeeCCS.Step05.Columns
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! The small positive coefficients in (68), by rational series bounds. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Step06

private def outerSeriesTerm (a : ℝ) (k : ℕ) : ℝ :=
  a ^ k / ((k.factorial : ℝ) * ((k + 2).factorial : ℝ))

private theorem outerMain_hasSum {y : ℝ} (hy : 0 < y) :
    HasSum (fun k => Real.pi ^ 3 / 18 * outerSeriesTerm (Real.pi ^ 2 * y ^ 2 / 3) k)
      (outerBesselMain y) := by
  let s := Real.sqrt (3 : ℝ)
  let x := 2 * Real.pi * y / s
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : s ≠ 0 := by dsimp [s]; positivity
  have ha : (x / 2) ^ 2 = Real.pi ^ 2 * y ^ 2 / 3 := by
    dsimp [x]
    rw [show 2 * Real.pi * y / s / 2 = Real.pi * y / s by ring, div_pow, mul_pow, hs]
  have hg := (Complex.hasSum_re (summable_besselITerm 2 (x : ℂ)).hasSum).mul_left
    (Real.pi / (6 * y ^ 2))
  have heq : Real.pi / (6 * y ^ 2) * (∑' k : ℕ, besselITerm 2 k (x : ℂ)).re = outerBesselMain y := by
    simp [outerBesselMain, besselI, x, s, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [heq] at hg
  refine hg.congr_fun (fun k => ?_)
  symm
  have he : besselITerm 2 k (x : ℂ) =
        ((((x / 2) ^ (2 * k + 2) / ((k.factorial : ℝ) * ((k + 2).factorial : ℝ))) : ℝ) : ℂ) := by
      unfold besselITerm
      push_cast
      rfl
  rw [he, Complex.ofReal_re, pow_add, pow_mul, ha, outerSeriesTerm]
  field_simp [hy.ne']
  ring

private theorem outerSeriesTerm_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    0 ≤ outerSeriesTerm a k := by unfold outerSeriesTerm; positivity

private theorem outerSeriesTerm_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : ℕ) :
    outerSeriesTerm a k ≤ outerSeriesTerm b k := by unfold outerSeriesTerm; gcongr

private theorem outerSeriesTerm_succ (a : ℝ) (k : ℕ) :
    outerSeriesTerm a (k + 1) =
      outerSeriesTerm a k * (a / ((k + 1 : ℝ) * (k + 3 : ℝ))) := by
  unfold outerSeriesTerm
  rw [show k + 1 + 2 = k + 2 + 1 by omega, Nat.factorial_succ k, Nat.factorial_succ (k + 2), pow_succ]
  push_cast
  have h₁ : (k : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (k : ℝ) + 2 + 1 ≠ 0 := by positivity
  have h₃ : (k : ℝ) + 3 ≠ 0 := by positivity
  field_simp [h₁, h₂, h₃,
    show (k.factorial : ℝ) ≠ 0 by positivity, show ((k + 2).factorial : ℝ) ≠ 0 by positivity]
  ring

private theorem outerSeriesTerm_tail {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 50) (k : ℕ) :
    outerSeriesTerm a (k + 24) ≤ outerSeriesTerm a 24 * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + 24 = k + 24 + 1 by omega, outerSeriesTerm_succ, pow_succ, ← mul_assoc]
    refine mul_le_mul ih ?_ (by positivity) (by
      exact mul_nonneg (outerSeriesTerm_nonneg ha _) (by positivity))
    apply (div_le_iff₀ (by positivity)).mpr
    have hk : 0 ≤ (k : ℝ) := by positivity
    push_cast
    nlinarith

private def rationalOuterSeriesTerm (a : ℚ) (k : ℕ) : ℚ :=
  a ^ k / ((k.factorial : ℚ) * ((k + 2).factorial : ℚ))

private def rationalOuterSum (p t : ℚ) : ℚ :=
  (p ^ 3 / 18) * ∑ k ∈ Finset.range 24, rationalOuterSeriesTerm (p ^ 2 * (t - 1 / 12) / 3) k

private def rationalOuterTail (p t : ℚ) : ℚ :=
  (p ^ 3 / 18) * 2 * rationalOuterSeriesTerm (p ^ 2 * (t - 1 / 12) / 3) 24

private def smallTwoColourCount (t : ℕ) : ℤ :=
  (Step05.coefficientColumn15[t + 225]?).getD 0

private theorem smallTwoColourCount_eq {t : ℕ} (ht' : t ≤ 15) :
    smallTwoColourCount t = twoColourPartitionCount t := by
  have hi : t + 225 < Step05.coefficientColumn15.length := by
    rw [Step05.coefficientColumn15_length]
    omega
  rw [smallTwoColourCount, List.getElem?_eq_getElem hi, Option.getD_some,
    Step05.coefficientColumn15_spec _ hi,
    p_eq_coeff_restrictedPairSeries (d := 15) (by omega)]
  norm_num
  exact (twoColourPartitionCount_eq_coeff_restricted t 15 ht').symm

private abbrev piLower : ℚ := 3.141592
private abbrev piUpper : ℚ := 3.141593

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem outerSmallCertificate {t : ℕ} (ht : 0 < t) (ht' : t ≤ 15) :
    (smallTwoColourCount t : ℚ) - 3 ≤ rationalOuterSum piLower t ∧
      rationalOuterSum piUpper t + rationalOuterTail piUpper t ≤ (smallTwoColourCount t : ℚ) + 3 := by
  interval_cases t <;> simp only [rationalOuterSum, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    decide +kernel

private theorem outerMain_bounds {t : ℕ} (ht : 0 < t) (ht' : t ≤ 15) :
    ((rationalOuterSum piLower t : ℚ) : ℝ) ≤ outerBesselMain (twoColourShift t) ∧
      outerBesselMain (twoColourShift t) ≤
        ((rationalOuterSum piUpper t + rationalOuterTail piUpper t : ℚ) : ℝ) := by
  let y := twoColourShift t
  let a := Real.pi ^ 2 * y ^ 2 / 3
  let lo := (piLower : ℝ)
  let hi := (piUpper : ℝ)
  have hy := twoColourShift_pos ht
  have h₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have h₁₅ : (t : ℝ) ≤ 15 := by exact_mod_cast ht'
  have hy₂ : y ^ 2 = (t : ℝ) - 1 / 12 := twoColourShift_sq ht
  have hlo₀ : 0 ≤ lo := by dsimp [lo, piLower]; norm_num
  have hlo : lo ≤ Real.pi := by
    dsimp [lo, piLower]
    apply (le_of_lt ?_).trans Real.pi_gt_d20.le
    norm_num
  have hhi : Real.pi ≤ hi := by
    apply Real.pi_lt_d20.le.trans
    dsimp [hi, piUpper]
    norm_num
  have hloA : lo ^ 2 * ((t : ℝ) - 1 / 12) / 3 ≤ a := by
    dsimp [a]
    rw [hy₂]
    gcongr <;> linarith
  have hhiA : a ≤ hi ^ 2 * ((t : ℝ) - 1 / 12) / 3 := by
    dsimp [a]
    rw [hy₂]
    gcongr <;> linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha' : a ≤ 50 := hhiA.trans (by
    have he : hi ^ 2 * ((t : ℝ) - 1 / 12) / 3 ≤ hi ^ 2 * (15 - 1 / 12) / 3 := by gcongr
    exact he.trans (by dsimp [hi, piUpper]; norm_num))
  have hsum := outerMain_hasSum hy
  change HasSum (fun k => Real.pi ^ 3 / 18 * outerSeriesTerm a k) (outerBesselMain y) at hsum
  have htail : (∑' k, Real.pi ^ 3 / 18 * outerSeriesTerm a (k + 24)) ≤
      Real.pi ^ 3 / 18 * 2 * outerSeriesTerm a 24 := by
    have hge := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    calc
      _ ≤ ∑' k, (Real.pi ^ 3 / 18 * outerSeriesTerm a 24) * (1 / 2 : ℝ) ^ k :=
        ((summable_nat_add_iff 24).mpr hsum.summable).tsum_le_tsum
          (fun k => by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (outerSeriesTerm_tail ha ha' k) (by positivity)) (hge.mul_left _)
      _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        ring_nf
  push_cast
  simp only [rationalOuterSum, rationalOuterTail, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, Rat.cast_sum,
    rationalOuterSeriesTerm]
  change lo ^ 3 / 18 * (∑ k ∈ Finset.range 24, outerSeriesTerm (lo ^ 2 * ((t : ℝ) - 1 / 12) / 3) k) ≤
      outerBesselMain y ∧ outerBesselMain y ≤
    hi ^ 3 / 18 * (∑ k ∈ Finset.range 24, outerSeriesTerm (hi ^ 2 * ((t : ℝ) - 1 / 12) / 3) k) +
      hi ^ 3 / 18 * 2 * outerSeriesTerm (hi ^ 2 * ((t : ℝ) - 1 / 12) / 3) 24
  have hsplit := hsum.summable.sum_add_tsum_nat_add 24
  rw [hsum.tsum_eq, ← Finset.mul_sum] at hsplit
  rw [← hsplit]
  constructor
  · calc
      _ ≤ Real.pi ^ 3 / 18 * (∑ k ∈ Finset.range 24, outerSeriesTerm a k) := by
        gcongr with k hk
        · exact Finset.sum_nonneg (fun k _ => outerSeriesTerm_nonneg (by
            have h : (0 : ℝ) ≤ t - 1 / 12 := by linarith
            positivity) k)
        · exact outerSeriesTerm_le (by
            have h : (0 : ℝ) ≤ t - 1 / 12 := by linarith
            positivity) hloA k
      _ ≤ _ := le_add_of_nonneg_right (tsum_nonneg (fun k =>
        mul_nonneg (by positivity) (outerSeriesTerm_nonneg ha (k + 24))))
  · refine add_le_add ?_ (htail.trans ?_)
    · gcongr with k hk
      · exact Finset.sum_nonneg (fun k _ => outerSeriesTerm_nonneg ha k)
      · exact outerSeriesTerm_le ha hhiA k
    · refine mul_le_mul ?_ (outerSeriesTerm_le ha hhiA 24) (outerSeriesTerm_nonneg ha 24) ?_
      · gcongr
      · positivity

/-- The order-two Bessel coefficient approximation has error at most three for indices 1–15. -/
theorem twoColour_bessel_error_small_three {t : ℕ} (ht : 0 < t) (ht' : t ≤ 15) :
    |(twoColourPartitionCount t : ℝ) - outerBesselMain (twoColourShift t)| ≤ 3 := by
  obtain ⟨hl, hu⟩ := outerSmallCertificate ht ht'
  have hl' : (twoColourPartitionCount t : ℝ) - 3 ≤ (rationalOuterSum piLower t : ℚ) := by
    rw [← smallTwoColourCount_eq ht']
    exact_mod_cast hl
  have hu' : ((rationalOuterSum piUpper t + rationalOuterTail piUpper t : ℚ) : ℝ) ≤
      (twoColourPartitionCount t : ℝ) + 3 := by
    rw [← smallTwoColourCount_eq ht']
    exact_mod_cast hu
  obtain ⟨hlo, hhi⟩ := outerMain_bounds ht ht'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Manuscript (68) for the first fifteen positive indices. -/
theorem twoColour_bessel_error_small {t : ℕ} (ht : 0 < t) (ht' : t ≤ 15) :
    |(twoColourPartitionCount t : ℝ) - outerBesselMain (twoColourShift t)| ≤
      Real.pi ^ 3 / 36 * Real.exp (Real.pi * Real.sqrt ((t : ℝ) / 3)) := by
  refine (twoColour_bessel_error_small_three ht ht').trans ?_
  have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt ((t : ℝ) / 3) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hE : Real.exp (3 / 2 : ℝ) ≤ Real.exp (Real.pi * Real.sqrt ((t : ℝ) / 3)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = (3 : ℝ) * (1 / 2) := by ring
      _ ≤ _ := by gcongr
  have hpoly := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 4
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ] at hpoly
  calc
    (3 : ℝ) ≤ 3 ^ 3 / 36 * Real.exp (3 / 2) := by linarith
    _ ≤ _ := by gcongr

end DurfeeCCS.Step10
