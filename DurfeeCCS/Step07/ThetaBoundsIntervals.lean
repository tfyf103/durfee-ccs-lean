module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-! Certified reciprocal and division for dyadic enclosures with positive denominators. -/

@[expose] public section

namespace Inclusion.IntervalDyadicReal

/-- Reverse finite strictly positive endpoints under reciprocal, rounding outward.
For intervals outside the positive domain the enclosure is the whole real line. -/
def reciprocalPositive (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match I.lb, I.ub with
  | (l : Dyadic), (u : Dyadic) =>
    if 0 < l then Interval.Icc (rat u.toRat⁻¹ prec).lb (rat l.toRat⁻¹ prec).ub
    else ⟨⊥, ⊤⟩
  | _, _ => ⟨⊥, ⊤⟩

@[inclusion_op interval_dyadic_real]
theorem inv_mem_positive {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    x⁻¹ ∈ reciprocalPositive I prec := by
  rw [mem_iff_mem_map] at hx ⊢
  rw [Interval.mem_map_iff] at hx
  rcases I with ⟨_ | l, _ | u⟩ <;> simp only [reciprocalPositive]
  all_goals try (rw [Interval.mem_map_iff]; simp)
  split_ifs with hl
  · have hlx := hx.1 l rfl
    have hxu := hx.2 u rfl
    have hl' : 0 < Dyadic.toReal l := by
      simpa only [show Dyadic.toReal 0 = 0 from map_zero Dyadic.toRealAddMonoidHom]
        using Dyadic.toReal_lt_toReal.mpr hl
    have hx' : 0 < x := hl'.trans_le hlx
    have hlo : (↑(u.toRat⁻¹) : ℝ) ≤ x⁻¹ := by
      simpa only [Rat.cast_inv, Dyadic.toReal] using inv_anti₀ hx' hxu
    have hhi : x⁻¹ ≤ (↑(l.toRat⁻¹) : ℝ) := by
      simpa only [Rat.cast_inv, Dyadic.toReal] using inv_anti₀ hl' hlx
    exact Interval.mem_Icc_of_le (ratCast_mem _ prec) hlo hhi (ratCast_mem _ prec)
  · rw [Interval.mem_map_iff]
    simp

@[inclusion_op interval_dyadic_real]
theorem div_mem_positive {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J)
    (prec : ℕ) : x / y ∈ I.mul (reciprocalPositive J prec) := by
  rw [div_eq_mul_inv]
  exact mul_mem hx (inv_mem_positive hy prec)

end Inclusion.IntervalDyadicReal
