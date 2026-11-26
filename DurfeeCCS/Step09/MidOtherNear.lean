module

public import DurfeeCCS.Step09.MidOtherIntegrals
public import DurfeeCCS.Step07.SaddleEndpointGrid

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The finite frequency groups in the central arc. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Real Set DurfeeCCS.Step06 DurfeeCCS.Step07

private theorem midSaddleRe_le_one_log {r : ℝ} (hr : 1 ≤ r) (ht : log r ≤ 1) :
    (saddleS r).re ≤ 1.733 := by
  have hrp : 0 < r := by linarith
  have hr' := exp_le_exp.mpr ht
  rw [Real.exp_log hrp] at hr'
  have hEnd : (saddleS (exp 1)).re ≤ 1.73266 := by
    simpa [saddleEndpointData,Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (13 : Fin 21)).re_upper
  exact (monotoneOn_saddleS_re hrp (Real.exp_pos _) hr').trans (by linarith only [hEnd])

private theorem midSaddleRe_le_five_log {r : ℝ} (hr : 1 ≤ r) (ht : log r ≤ 5) :
    (saddleS r).re ≤ 5.295 := by
  have hrp : 0 < r := by linarith
  have hr' := exp_le_exp.mpr ht
  rw [Real.exp_log hrp] at hr'
  have hEnd : (saddleS (exp 5)).re ≤ 5.29407 := by
    simpa [saddleEndpointData,Rat.cast_ofScientific] using
      (saddleEndpointData_bounds (19 : Fin 21)).re_upper
  exact (monotoneOn_saddleS_re hrp (Real.exp_pos _) hr').trans (by linarith only [hEnd])

private theorem midOther_gap_to_mass_large {n : ℕ} {r δ : ℝ} {p : ℤ} (hn : 6400 ≤ n)
    (hr : 1 ≤ r) (hmax : r ≤ exp 1 * √(n : ℝ)) (hδ : δ ≤ √(n : ℝ) * midModeGap r |midFrequency p|) :
    midOtherNormalizedMass n r p ≤ 109000 * √(midOmega n r) * exp (-δ) := by
  have H := (midOther_full_gauss_bound (δ := δ) (p := p) (by omega : 0 < n) hr
    (by norm_num) midOtherGaussian_constant_large
    (fun η hη χ => (norm_midMultiplier_lt_2100 hn hr hmax hη p χ).le)
    (fun η hη χ => (midRe_exponent_nonprincipal (by omega : 0 < n) hr hη p).trans
      (by linarith only [hδ]))).2
  convert H using 1 <;> ring

private theorem midOther_gap_to_mass_small {n : ℕ} {r δ : ℝ} {p : ℤ} (hn : 6400 ≤ n)
    (hr : 1 ≤ r) (hmax : r ≤ exp 1 * √(n : ℝ)) (ht : 1 ≤ log r)
    (hδ : δ ≤ √(n : ℝ) * midModeGap r |midFrequency p|) :
    midOtherNormalizedMass n r p ≤ 110 * √(midOmega n r) * exp (-δ) := by
  have H := (midOther_full_gauss_bound (δ := δ) (p := p) (by omega : 0 < n) hr
    (by norm_num) midOtherGaussian_constant_small
    (fun η hη χ => (norm_midMultiplier_lt_two hn hr hmax ht hη p χ).le)
    (fun η hη χ => (midRe_exponent_nonprincipal (by omega : 0 < n) hr hη p).trans
      (by linarith only [hδ]))).2
  convert H using 1 <;> ring

theorem midOther_near_sum_lt {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ exp 1 * √(n : ℝ)) :
    let a := (saddleS r).re
    (∑ p ∈ midOtherNearModes a, midOtherNormalizedMass n r p) <
      if log r < 1 then 0.000001 else if log r < 5 then 0.00023 else 0.00098 := by
  let a := (saddleS r).re
  let x := √(n : ℝ)
  let ω := midOmega n r
  let t := log r
  let P := midOtherNearModes a
  have hω : ω = a * x := by rfl
  have hrp : 0 < r := by linarith
  have hx : 80 ≤ x := by apply le_sqrt_of_sq_le; exact_mod_cast hn
  have hx' : 0 ≤ x := by positivity
  have H := midSaddle_data hn hr hmax
  have ha : 0 < a := by linarith only [H.1]
  have haUp : a ≤ theta38Growth x := H.2.1
  change (∑ p ∈ P, midOtherNormalizedMass n r p) < if t < 1 then _ else _
  by_cases ht₁ : t < 1
  · rw [ite_eq_left ht₁]
    let B := 109000 * √ω * exp (-0.44*x)
    have hPoint (p : ℤ) (hp : p ∈ P) : midOtherNormalizedMass n r p ≤ B := by
      obtain ⟨_,hn₀,hn₁⟩ := (mem_midOtherNearModes ha.le p).mp hp
      have hg := midModeGap_low_log hr ht₁.le (midFrequency_abs_ge_three_half hn₀ hn₁)
      have hδ : 0.44*x ≤ x*midModeGap r |midFrequency p| := by
        rw [mul_comm 0.44 x]
        exact mul_le_mul_of_nonneg_left hg.le hx'
      simpa only [B,neg_mul] using midOther_gap_to_mass_large hn hr hmax hδ
    have hc : ∑ p ∈ P, midOtherNormalizedMass n r p ≤ (26*a+2)*B := by
      calc
        _ ≤ ∑ _p ∈ P, B := Finset.sum_le_sum hPoint
        _ = (P.card : ℝ)*B := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (midOtherNearModes_card_le ha.le) (by unfold B; positivity)
    refine hc.trans_lt ?_
    have hb := midOther_small_near_budget_lt hx ha.le (midSaddleRe_le_one_log hr ht₁.le)
    unfold B
    rw [hω]
    change _ < (0.000001 : ℝ)
    convert hb using 1 <;> ring
  · rw [ite_eq_right ht₁]
    have ht₀ : 1 ≤ t := le_of_not_gt ht₁
    by_cases ht₅ : t < 5
    · rw [ite_eq_left ht₅]
      let U := 110 * √ω * exp (-0.21*x)
      let V := 110 * √ω * exp (-0.36*x)
      have hFirst (p : ℤ) (hp : p ∈ P) (_ : p = 1 ∨ p = -2) : midOtherNormalizedMass n r p ≤ U := by
        obtain ⟨_,hn₀,hn₁⟩ := (mem_midOtherNearModes ha.le p).mp hp
        have hg := midModeGap_middle_log false hr ht₀ ht₅.le (midFrequency_abs_ge_three_half hn₀ hn₁)
        have hδ : 0.21*x ≤ x*midModeGap r |midFrequency p| := by
          rw [mul_comm 0.21 x]
          exact mul_le_mul_of_nonneg_left hg.le hx'
        simpa only [U,neg_mul] using midOther_gap_to_mass_small hn hr hmax ht₀ hδ
      have hRest (p : ℤ) (hp : p ∈ P) (hp₁ : p ≠ 1) (hp₂ : p ≠ -2) :
          midOtherNormalizedMass n r p ≤ V := by
        obtain ⟨_,hn₀,hn₁⟩ := (mem_midOtherNearModes ha.le p).mp hp
        have hg := midModeGap_middle_log true hr ht₀ ht₅.le (midFrequency_abs_ge_five_half hn₀ hn₁ hp₁ hp₂)
        have hδ : 0.36*x ≤ x*midModeGap r |midFrequency p| := by
          rw [mul_comm 0.36 x]
          exact mul_le_mul_of_nonneg_left hg.le hx'
        simpa only [V,neg_mul] using midOther_gap_to_mass_small hn hr hmax ht₀ hδ
      have h := midOtherNearModes_sum_le ha.le (show 0 ≤ U by unfold U; positivity)
        (show 0 ≤ V by unfold V; positivity) (midOtherNormalizedMass n r) hFirst hRest
      refine h.trans_lt ?_
      have hb := midOther_intermediate_near_budget_lt hx ha.le (midSaddleRe_le_five_log hr ht₅.le)
      unfold U V
      rw [hω]
      change _ < (0.00023 : ℝ)
      convert hb using 1 <;> ring
    · rw [ite_eq_right ht₅]
      have ht₅' : 5 ≤ t := le_of_not_gt ht₅
      let δ₁ := 59.5*x/(a*(t^2+25.5))
      let δ₂ := 178*x/(a*(t^2+65))
      let U := 110 * √ω * exp (-δ₁)
      let V := 110 * √ω * exp (-δ₂)
      have hFirst (p : ℤ) (hp : p ∈ P) (_ : p = 1 ∨ p = -2) : midOtherNormalizedMass n r p ≤ U := by
        obtain ⟨_,hn₀,hn₁⟩ := (mem_midOtherNearModes ha.le p).mp hp
        have hg := midModeGap_high_log false hr ht₅' (midFrequency_abs_ge_three_half hn₀ hn₁)
        apply midOther_gap_to_mass_small hn hr hmax ht₀
        calc
          _ = x * (midModeHighNumerator false / (a*(t^2+midModeHighDenominator false))) := by
            unfold δ₁ midModeHighNumerator midModeHighDenominator
            simp
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hg hx'
      have hRest (p : ℤ) (hp : p ∈ P) (hp₁ : p ≠ 1) (hp₂ : p ≠ -2) :
          midOtherNormalizedMass n r p ≤ V := by
        obtain ⟨_,hn₀,hn₁⟩ := (mem_midOtherNearModes ha.le p).mp hp
        have hg := midModeGap_high_log true hr ht₅' (midFrequency_abs_ge_five_half hn₀ hn₁ hp₁ hp₂)
        apply midOther_gap_to_mass_small hn hr hmax ht₀
        calc
          _ = x * (midModeHighNumerator true / (a*(t^2+midModeHighDenominator true))) := by
            unfold δ₂ midModeHighNumerator midModeHighDenominator
            simp
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hg hx'
      have h := midOtherNearModes_sum_le ha.le (show 0 ≤ U by unfold U; positivity)
        (show 0 ≤ V by unfold V; positivity) (midOtherNormalizedMass n r) hFirst hRest
      have htMax : t ≤ log x + 1 := by
        have hx0 : 0 < x := by linarith
        have h := Real.log_le_log hrp hmax
        change log r ≤ log (exp 1*x) at h
        rw [Real.log_mul (Real.exp_ne_zero _) hx0.ne', Real.log_exp] at h
        linarith only [h]
      refine h.trans_lt ?_
      have hb := midOther_large_near_budget_lt hx ha haUp (by linarith only [ht₅'] : 0 ≤ t) htMax
      unfold U V δ₁ δ₂
      rw [hω]
      change _ < (0.00098 : ℝ)
      dsimp only at hb
      convert hb using 1 <;> ring

end DurfeeCCS.Step09
