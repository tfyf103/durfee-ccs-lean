module

public import DurfeeCCS.Step09.MidOtherNear
public import DurfeeCCS.Step09.MidOtherIntegrals
public import DurfeeCCS.Step09.MidPhaseSymmetry

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Combining the finite and absolutely summable parts of the integer frequencies. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Real DurfeeCCS.Step06

private theorem principal_not_far {a : ℝ} (ha : 1 < a) {p : ℤ}
    (hp : p = 0 ∨ p = -1) : |midFrequency p| ≤ 40*a := by
  rcases hp with rfl | rfl
  · rw [midFrequency_zero, abs_of_nonneg (by positivity)]
    linarith [Real.pi_lt_d6]
  · rw [midFrequency_neg_one, abs_neg, abs_of_nonneg (by positivity)]
    linarith [Real.pi_lt_d6]

private theorem split_nonprincipal_mass {a : ℝ} (ha : 1 < a) (M : ℤ → ℝ) (p : ℤ) :
    (if p = 0 ∨ p = -1 then 0 else M p) =
      (if p ∈ midOtherNearModes a then M p else 0) +
        (if 40*a < |midFrequency p| then M p else 0) := by
  have ha₀ : 0 ≤ a := by linarith
  by_cases hP : p = 0 ∨ p = -1
  · have hN : p ∉ midOtherNearModes a := by
      intro hp
      have h := (mem_midOtherNearModes ha₀ p).mp hp
      exact hP.elim h.2.1 h.2.2
    simp [hP, hN, not_lt.mpr (principal_not_far ha hP)]
  · have h0 : p ≠ 0 := fun h => hP (Or.inl h)
    have h1 : p ≠ -1 := fun h => hP (Or.inr h)
    by_cases hF : 40*a < |midFrequency p|
    · have hN : p ∉ midOtherNearModes a := by
        intro hp
        exact (not_le_of_gt hF) ((mem_midOtherNearModes ha₀ p).mp hp).1
      simp [h0, h1, hF, hN]
    · have hN : p ∈ midOtherNearModes a :=
        (mem_midOtherNearModes ha₀ p).mpr ⟨le_of_not_gt hF, h0, h1⟩
      simp [h0, h1, hF, hN]

private theorem sum_nonprincipal_mass {a : ℝ} (ha : 1 < a) (M : ℤ → ℝ)
    (hs : Summable (fun p : ℤ => if 40*a < |midFrequency p| then M p else 0)) :
    Summable (fun p : ℤ => if p = 0 ∨ p = -1 then 0 else M p) ∧
      (∑' p : ℤ, if p = 0 ∨ p = -1 then 0 else M p) =
        (∑ p ∈ midOtherNearModes a, M p) + ∑' p : ℤ, if 40*a < |midFrequency p| then M p else 0 := by
  have hN : Summable (fun p : ℤ => if p ∈ midOtherNearModes a then M p else 0) := by
    apply summable_of_ne_finset_zero (s := midOtherNearModes a)
    intro p hp
    simp [hp]
  have hEqN : (∑' p : ℤ, if p ∈ midOtherNearModes a then M p else 0) =
      ∑ p ∈ midOtherNearModes a, M p := by
    rw [tsum_eq_sum (s := midOtherNearModes a) (fun p hp => by simp [hp])]
    exact Finset.sum_congr rfl (fun p hp => by simp [hp])
  have hsplit := split_nonprincipal_mass ha M
  refine ⟨(hN.add hs).congr (fun p => (hsplit p).symm), ?_⟩
  simp_rw [hsplit]
  rw [hN.tsum_add hs, hEqN]

/-- The series of nonprincipal normalized frequency masses, split at the paper's far threshold. -/
theorem midOther_nonprincipal_sum_bound {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) :
    let M (p : ℤ) := if p = 0 ∨ p = -1 then 0 else midOtherNormalizedMass n r p
    Summable M ∧ (∑' p : ℤ, M p) <
      (if Real.log r < 1 then 0.000002 else if Real.log r < 5 then 0.000231 else 0.000981) := by
  dsimp only
  have ha := (midSaddle_data hn hr hmax).1
  obtain ⟨hF, hFbound⟩ := midOther_far_bound hn hr hmax
  obtain ⟨hN, hEq⟩ := sum_nonprincipal_mass ha (midOtherNormalizedMass n r) hF
  have hNbound := midOther_near_sum_lt hn hr hmax
  refine ⟨hN, ?_⟩
  rw [hEq]
  dsimp only at hNbound hFbound
  by_cases h₁ : Real.log r < 1
  · rw [ite_eq_left h₁] at hNbound ⊢
    exact (add_lt_add hNbound hFbound).trans_le (by norm_num)
  · rw [ite_eq_right h₁] at hNbound ⊢
    by_cases h₅ : Real.log r < 5
    · rw [ite_eq_left h₅] at hNbound ⊢
      exact (add_lt_add hNbound hFbound).trans_le (by norm_num)
    · rw [ite_eq_right h₅] at hNbound ⊢
      exact (add_lt_add hNbound hFbound).trans_le (by norm_num)

/-- Absolute summability for all frequencies after adding back the two
principal terms. -/
theorem summable_mid_frequency_integral_norm {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) :
    Summable (fun p : ℤ => midOtherMass n r p (-8) 8) := by
  have hf : 0 < midOtherMassFactor n r := midOtherMassFactor_pos (by omega) (by linarith)
  let E : Finset ℤ := {0, -1}
  have hE : Summable (fun p : ℤ => if p ∈ E then midOtherNormalizedMass n r p else 0) := by
    apply summable_of_ne_finset_zero (s := E)
    intro p hp
    simp [hp]
  have hM := (midOther_nonprincipal_sum_bound hn hr hmax).1
  have hAll : Summable (midOtherNormalizedMass n r) := by
    refine (hM.add hE).congr (fun p => ?_)
    have h : p ∈ E ↔ p = 0 ∨ p = -1 := by simp [E]
    by_cases hP : p = 0 ∨ p = -1
    · simp only [ite_eq_left hP, ite_eq_left (h.mpr hP), zero_add]
    · have hNot : p ∉ E := fun hp => hP (h.mp hp)
      simp only [ite_eq_right hP, ite_eq_right hNot, add_zero]
  refine (hAll.mul_left (midOtherMassFactor n r)⁻¹).congr (fun p => ?_)
  rw [midOtherNormalizedMass, ← mul_assoc, inv_mul_cancel₀ hf.ne', one_mul]

end DurfeeCCS.Step09
