module

public import DurfeeCCS.Step09.MidPhase
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Algebra.Order.Floor.Ring

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Frequency counts and the summable Gaussian majorant in Lemma 3.10. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Real Set Filter

theorem midFrequency_abs_ge_three_half {p : ℤ} (hp₀ : p ≠ 0) (hpneg : p ≠ -1) :
    3 * π / 2 ≤ |midFrequency p| := by
  have h : (3 / 2 : ℝ) ≤ |(p : ℝ) + 1 / 2| := by
    rcases le_total 0 p with hp | hp
    · have h₀ : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
      exact (show (3 / 2 : ℝ) ≤ (p : ℝ) + 1 / 2 by linarith).trans (le_abs_self _)
    · have h₀ : (p : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast (show p ≤ -2 by omega)
      exact (show (3 / 2 : ℝ) ≤ -((p : ℝ) + 1 / 2) by linarith).trans (neg_le_abs _)
  rw [midFrequency, abs_mul, abs_of_pos pi_pos]
  nlinarith only [mul_le_mul_of_nonneg_left h pi_pos.le]

theorem midFrequency_abs_ge_five_half {p : ℤ} (hp₀ : p ≠ 0) (hpneg : p ≠ -1)
    (h₁ : p ≠ 1) (h₂ : p ≠ -2) : 5 * π / 2 ≤ |midFrequency p| := by
  have h : (5 / 2 : ℝ) ≤ |(p : ℝ) + 1 / 2| := by
    rcases le_total 0 p with hp | hp
    · have h₀ : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 2 ≤ p by omega)
      exact (show (5 / 2 : ℝ) ≤ (p : ℝ) + 1 / 2 by linarith).trans (le_abs_self _)
    · have h₀ : (p : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast (show p ≤ -3 by omega)
      exact (show (5 / 2 : ℝ) ≤ -((p : ℝ) + 1 / 2) by linarith).trans (neg_le_abs _)
  rw [midFrequency, abs_mul, abs_of_pos pi_pos]
  nlinarith only [mul_le_mul_of_nonneg_left h pi_pos.le]

def midOtherNearModes (a : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌊13 * a⌋ - 1) ⌊13 * a⌋).filter
    (fun p => |midFrequency p| ≤ 40 * a ∧ p ≠ 0 ∧ p ≠ -1)

theorem mem_midOtherNearModes {a : ℝ} (ha : 0 ≤ a) (p : ℤ) :
    p ∈ midOtherNearModes a ↔ |midFrequency p| ≤ 40 * a ∧ p ≠ 0 ∧ p ≠ -1 := by
  unfold midOtherNearModes
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨And.right, fun hp => ⟨?_, hp⟩⟩
  have hm : |(p : ℝ) + 1 / 2| ≤ 13*a := by
    have h := hp.1
    rw [midFrequency, abs_mul, abs_of_pos pi_pos] at h
    have hA : (40 : ℝ) ≤ π*13 := by linarith [pi_gt_d6]
    by_contra! he
    have h₁ := mul_lt_mul_of_pos_left he pi_pos
    have h₂ := mul_le_mul_of_nonneg_right hA ha
    linarith only [h, h₁, h₂]
  constructor
  · have hm' : (-p - 1 : ℤ) ≤ ⌊13*a⌋ :=
      Int.le_floor.mpr (by
        push_cast
        linarith only [(abs_le.mp hm).1])
    omega
  · apply Int.le_floor.mpr
    linarith only [(abs_le.mp hm).2]

theorem midOtherNearModes_card_le {a : ℝ} (ha : 0 ≤ a) :
    ((midOtherNearModes a).card : ℝ) ≤ 26 * a + 2 := by
  let m := ⌊13 * a⌋
  have hm : 0 ≤ m := Int.floor_nonneg.mpr (by positivity)
  have hI : (Finset.Icc (-m-1) m).card = (2*m+2).toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  have hcard : (midOtherNearModes a).card ≤ (Finset.Icc (-m-1) m).card :=
    Finset.card_filter_le _ _
  have hcard' : ((midOtherNearModes a).card : ℝ) ≤ (2 * (m : ℝ) + 2) := by
    have h : ((midOtherNearModes a).card : ℝ) ≤ ((Finset.Icc (-m-1) m).card : ℝ) := by
      exact_mod_cast hcard
    have hcast : ((2 * m + 2).toNat : ℝ) = 2 * (m : ℝ) + 2 := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    rw [hI, hcast] at h
    exact h
  exact hcard'.trans (by
    have h := Int.floor_le (13 * a)
    change (m : ℝ) ≤ _ at h
    linarith only [h])

theorem midOtherNearModes_sum_le {a U V : ℝ} (ha : 0 ≤ a) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (W : ℤ → ℝ)
    (hU' : ∀ p ∈ midOtherNearModes a, p = 1 ∨ p = -2 → W p ≤ U)
    (hV' : ∀ p ∈ midOtherNearModes a, p ≠ 1 → p ≠ -2 → W p ≤ V) :
    (∑ p ∈ midOtherNearModes a, W p) ≤ 2 * U + (26*a+2)*V := by
  let L := midOtherNearModes a
  let e : Finset ℤ := {1,-2}
  let S := L.filter (fun p => p ∈ e)
  let T := L.filter (fun p => p ∉ e)
  have hSeq : (∑ p ∈ L, W p) = (∑ p ∈ S, W p) + ∑ p ∈ T, W p := by
    unfold S T
    symm
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hSc : S.card ≤ 2 := by
    have h := Finset.card_le_card (show S ⊆ e from fun p hp => (Finset.mem_filter.mp hp).2)
    simpa [e] using h
  have hTc : (T.card : ℝ) ≤ 26*a+2 :=
    (Nat.cast_le.mpr (Finset.card_filter_le _ _) : (T.card : ℝ) ≤ L.card).trans
      (midOtherNearModes_card_le ha)
  have h₁ : (∑ p ∈ S, W p) ≤ 2 * U := by
    calc
      _ ≤ ∑ _p ∈ S, U := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpL,hpe⟩ := Finset.mem_filter.mp hp
        exact hU' p hpL (by simpa [e] using hpe)
      _ = (S.card : ℝ) * U := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hSc) hU
  have h₂ : (∑ p ∈ T, W p) ≤ (26*a+2)*V := by
    calc
      _ ≤ ∑ _p ∈ T, V := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpL,hpe⟩ := Finset.mem_filter.mp hp
        have he : p ≠ 1 ∧ p ≠ -2 := by simpa [e] using hpe
        exact hV' p hpL he.1 he.2
      _ = (T.card : ℝ) * V := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hTc hV
  rw [hSeq]
  exact add_le_add h₁ h₂

def midOtherFarWeight (u : ℝ) (p : ℤ) : ℝ :=
  exp (-(midFrequency p)^2 / (400 * u))

/-- The Gaussian series can be bounded by a geometric series on the two
half-integer rays.  This gives the stronger constant 5 in place of 6. -/
theorem midOtherFarWeight_sum {u : ℝ} (hu : 0 < u) (hU : u ≤ 0.072) :
    Summable (midOtherFarWeight u) ∧ (∑' p : ℤ, midOtherFarWeight u p) ≤ 5 := by
  let f := midOtherFarWeight u
  have hp : π ^ 2 / (400*u) ≥ 1/3 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hk := pow_le_pow_left₀ (by norm_num : 0 ≤ (3.141592 : ℝ)) pi_gt_d6.le 2
    linarith only [hk,hU]
  have hQ : exp (-(2 / 3 : ℝ)) ≤ 3/5 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    have h := add_one_le_exp (2 / 3 : ℝ)
    linarith only [h]
  have hbase (j : ℕ) : f j ≤ (3/5 : ℝ)^j := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hSq : 2 * (j : ℝ) ≤ ((j : ℝ) + 1/2)^2 := by
      nlinarith only [sq_nonneg ((j : ℝ) - 1/2)]
    calc
      _ = exp (-(π ^ 2 / (400*u))*((j : ℝ) + 1/2)^2) := by
        unfold f midOtherFarWeight midFrequency
        push_cast
        congr 1
        ring
      _ ≤ exp (-(2/3 : ℝ) * j) := by
        apply exp_le_exp.mpr
        have h := mul_le_mul hp hSq (by positivity)
          (by positivity : 0 ≤ π ^ 2 / (400*u))
        nlinarith only [h]
      _ = exp (-(2/3 : ℝ))^j := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ (exp_nonneg _) hQ j
  have hEven (j : ℕ) : f (-(j+1 : ℤ)) = f j := by
    have hf : midFrequency (-(j+1 : ℤ)) = -midFrequency j := by
      unfold midFrequency
      push_cast
      ring
    unfold f midOtherFarWeight
    rw [hf, neg_sq]
  have hgeom : Summable (fun j : ℕ => (3/5 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hL := hgeom.of_nonneg_of_le (fun j => (exp_pos _).le : ∀ j : ℕ, 0 ≤ f j) hbase
  have hR : Summable (fun j : ℕ => f (-(j+1 : ℤ))) := hL.congr (fun j => (hEven j).symm)
  refine ⟨Summable.of_nat_of_neg_add_one hL hR, ?_⟩
  change (∑' p : ℤ, f p) ≤ _
  rw [tsum_of_nat_of_neg_add_one hL hR]
  simp_rw [hEven]
  have hsum := hL.tsum_le_tsum hbase hgeom
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hsum
  linarith only [hsum]

end DurfeeCCS.Step09
