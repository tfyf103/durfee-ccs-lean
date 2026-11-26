module

public import DurfeeCCS.Step08.MinorArcGeometry
public import DurfeeCCS.Step08.MinorArcLogBounds

/-! Sine estimates for the paired-log sums on the short arcs in (40). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open DurfeeCCS.Step07

/-- The modulus bound outside the arcs of denominator at most seven. -/
theorem norm_pairedLog_outside_rational_arcs {r r₀ u : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀)
    (hr₁ : r₀ ≤ 1) (hu : 0 < u) (θ : ℝ) {v : ℝ}
    (hv : ∀ q : ℚ, ¬OnMinorRationalArc v q) :
    ‖pairedLog r θ (verticalPoint u v)‖ / (r / u) ≤ firstSaddleOffArcs r₀ u := by
  apply norm_pairedLog_off_arcs hr hr₀ hr₁ hu θ v
  intro k hk
  have hk' : k < 7 := Finset.mem_range.mp hk
  have hs := minorArc_sin_outside hv (by omega : 0 < k + 1) (by omega : k + 1 ≤ 7)
  convert hs using 1
  ring

/-- The modulus bound on the origin arc and beyond the interval `|v| < 16u`. -/
theorem norm_pairedLog_on_zero_arc {r u : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hu : 0 < u) (θ : ℝ) {v : ℝ} (hv : |v| ≤ 0.07) (hnot : 16 * u ≤ |v|) :
    ‖pairedLog r θ (verticalPoint u v)‖ / (r / u) ≤ 0.478 := by
  apply norm_pairedLog_zero_arc hr hr₁ hu θ v
  intro k hk
  have hk' : k < 7 := Finset.mem_range.mp hk
  have hs := minorArc_sin_zero hnot hv (by omega : k + 1 ≤ 7)
  convert hs using 1
  ring

private theorem high_denominator_resonant_sum {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1)
    {d : ℕ} (hd : 3 ≤ d) (hd₁ : d ≤ 7) :
    (∑ k ∈ Finset.range 7,
      if d ∣ k + 1 then 2 * r ^ k / ((k + 1 : ℕ) : ℝ) ^ 2 else 0) ≤
        2 * (r ^ 2 / 9 + r ^ 5 / 36) := by
  have hpow (k : ℕ) : r ^ (2 + k) ≤ r ^ 2 := by
    rw [pow_add]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hr hr₁)
  have h3 : r ^ 3 ≤ r ^ 2 := hpow 1
  have h4 : r ^ 4 ≤ r ^ 2 := hpow 2
  have h5 : r ^ 5 ≤ r ^ 2 := hpow 3
  have h6 : r ^ 6 ≤ r ^ 2 := hpow 4
  have h5pos : 0 ≤ r ^ 5 := by positivity
  have hcases : d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> norm_num [Finset.sum_range_succ] <;>
    linarith only [h3, h4, h5, h6, sq_nonneg r, h5pos]

/-- The modulus bound on a rational arc of denominator between three and seven. -/
theorem norm_pairedLog_high_arc {r r₀ u : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀)
    (hr₁ : r₀ ≤ 1) (hu : 0 < u) (θ : ℝ) {v : ℝ} {q : ℚ}
    (hv : OnMinorRationalArc v q) (hd : 3 ≤ q.den) :
    ‖pairedLog r θ (verticalPoint u v)‖ / (r / u) ≤ firstSaddleHighDenominatorArc r₀ u := by
  unfold firstSaddleHighDenominatorArc
  apply norm_pairedLog_le_seven hr hr₀ hr₁ hu θ v
  let R (k : ℕ) : ℝ :=
    if q.den ∣ k + 1 then 2 * r₀ ^ k / ((k + 1 : ℕ) : ℝ) ^ 2 else 0
  let S (k : ℕ) : ℝ := (u / 0.129) * (r₀ ^ k / ((k + 1 : ℕ) : ℝ))
  have hR : 0 ≤ r₀ := hr.le.trans hr₀
  have h (k : ℕ) (hk : k ∈ Finset.range 7) : logScaledMode r θ u v k ≤ R k + S k := by
    have hk' : k < 7 := Finset.mem_range.mp hk
    by_cases hkd : q.den ∣ k + 1
    · simp only [R, ite_eq_left hkd]
      exact (logScaledMode_le_radius hr hr₀ hu θ v k).trans
        (le_add_of_nonneg_right (show 0 ≤ S k by unfold S; positivity))
    · simp only [R, ite_eq_right hkd, zero_add, S]
      exact logScaledMode_le_sin hr hr₀ hu (by norm_num) θ v k
        (minorArc_sin_nonresonant hv (by omega : k + 1 ≤ 7) hkd).le
  calc
    _ ≤ ∑ k ∈ Finset.range 7, (R k + S k) := Finset.sum_le_sum h
    _ = (∑ k ∈ Finset.range 7, R k) + (u / 0.129) *
          ∑ k ∈ Finset.range 7, r₀ ^ k / ((k + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (high_denominator_resonant_sum hR hr₁ hd hv.1) le_rfl

end DurfeeCCS.Step08
