module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Reindexing and angular interval tiling in the proof of equation (47). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open MeasureTheory Set

/-- In coordinates \((p,m)\), the difference \(k_1-k_2\) is \(p+2m\). -/
def midPoissonIndex : ℤ × ℤ ≃ ℤ × ℤ where
  toFun v := (v.1 + v.2, -v.2)
  invFun v := (v.1 + v.2, -v.2)
  left_inv := by rintro ⟨a,b⟩; ext <;> dsimp <;> omega
  right_inv := by rintro ⟨a,b⟩; ext <;> dsimp <;> omega

/-- A full period translated by each lattice point partitions the real line up to endpoints. -/
theorem hasSum_midPoisson_angular_tiles {f : ℝ → ℂ} (hf : Integrable f) (p : ℤ) :
    HasSum (fun m : ℤ => ∫ θ in -Real.pi..Real.pi,
      f (θ + (p + 2 * m : ℤ) * Real.pi)) (∫ x : ℝ, f x) := by
  let c (m : ℤ) : ℝ := (p + 2 * m : ℤ) * Real.pi
  let s (m : ℤ) : Set ℝ := Ioc (-Real.pi + c m) (Real.pi + c m)
  have hordered (m l : ℤ) (h : m < l) : Disjoint (s m) (s l) := by
    have hn : (m : ℝ) + 1 ≤ l := by exact_mod_cast (show m + 1 ≤ l by omega)
    have hmul := mul_le_mul_of_nonneg_right hn (show 0 ≤ 2 * Real.pi by positivity)
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' := hx.2
    have hy' := hy.1
    simp only [c, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at hx' hy'
    nlinarith
  have hd : Pairwise (fun m l => Disjoint (s m) (s l)) := by
    intro m l hml
    rcases lt_or_gt_of_ne hml with h | h
    · exact hordered m l h
    · exact (hordered l m h).symm
  have hu : (⋃ m : ℤ, s m) = univ := by
    apply eq_univ_of_forall
    intro x
    let y : ℝ := (x - (p : ℝ) * Real.pi + Real.pi) / (2 * Real.pi)
    let m : ℤ := ⌈y⌉ - 1
    have hlow : (m : ℝ) < y := by
      push_cast [m]
      linarith [Int.ceil_lt_add_one y]
    have hhigh : y ≤ (m : ℝ) + 1 := by
      push_cast [m]
      linarith [Int.le_ceil y]
    have hpos : 0 < 2 * Real.pi := by positivity
    have hlo := (lt_div_iff₀ hpos).mp hlow
    have hhi := (div_le_iff₀ hpos).mp hhigh
    apply mem_iUnion_of_mem m
    change -Real.pi + c m < x ∧ x ≤ Real.pi + c m
    simp only [c, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    exact ⟨by nlinarith, by nlinarith⟩
  have h := hasSum_integral_iUnion (s := s) (fun _ => measurableSet_Ioc) hd hf.integrableOn
  rw [hu, setIntegral_univ] at h
  convert h using 1
  funext m
  rw [intervalIntegral.integral_comp_add_right, intervalIntegral.integral_of_le (by
    have := Real.pi_pos
    linarith)]

end DurfeeCCS.Step09
