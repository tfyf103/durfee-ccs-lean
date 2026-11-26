module

public import DurfeeCCS.Step07.FirstSaddleRadiusBound
public import DurfeeCCS.Step07.FirstSaddleErrorTable

/-! Apply the page 20–23 numerical bounds at the manuscript's actual saddle coordinates. -/

@[expose] public section

namespace DurfeeCCS.Step07

/-- The common upper bound for the saddle line parameter at all radii up to an endpoint. -/
theorem firstSaddleRadius_leU0 {n : ℕ} (hn : 6400 ≤ n) {r r₀ : ℝ}
    (hr : 0 < r) (hrr : r ≤ r₀) (hr₀ : r₀ ≤ 1) :
    (Step06.saddleS r).re / Real.sqrt (n : ℝ) ≤ firstSaddleU0 r₀ := by
  have h := (firstSaddle_coordinates_bounds hr (hrr.trans hr₀)).2.1
  have hz : 0 ≤ r₀ := hr.le.trans hrr
  have hm : r * (1 + 0.282 * r) ≤ r₀ * (1 + 0.282 * r₀) := by gcongr
  unfold firstSaddleU0
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, Real.sq_sqrt (by exact_mod_cast Nat.zero_le n)]
  exact div_le_div₀ (by positivity) (h.trans hm) (by norm_num) (by exact_mod_cast hn)

/-- The lower bound for the saddle parameter from the lower radius and the coefficient β. -/
theorem firstSaddleOmega_lower {n : ℕ} (hn : 6400 ≤ n) {r r₀ β : ℝ}
    (hr : 0 < r) (hrr : r₀ ≤ r) (hβ : 0 ≤ β) (ha : β * r ≤ (Step06.saddleS r).re ^ 2) :
    Real.sqrt (6400 * β * r₀) ≤ (Step06.saddleS r).re * Real.sqrt (n : ℝ) := by
  obtain ⟨hb, hab⟩ := Step06.saddleS_components hr
  have hapos : 0 < (Step06.saddleS r).re := hb.trans hab
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by exact_mod_cast Nat.zero_le n)]
  have hprod : β * r₀ ≤ (Step06.saddleS r).re ^ 2 :=
    (mul_le_mul_of_nonneg_left hrr hβ).trans ha
  calc
    _ = (β * r₀) * 6400 := by ring
    _ ≤ _ := mul_le_mul hprod (by exact_mod_cast hn) (by norm_num) (sq_nonneg _)

theorem firstSaddleCaseTwoError_saddle_06 {n : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0.25 < r) (hr₀ : r ≤ 0.6) :
    firstSaddleCaseTwoError 0.6 ((Step06.saddleS r).re * Real.sqrt (n : ℝ)) 0.479 < 0.753 := by
  have hrpos : 0 < r := by linarith
  have h₀ : r ≤ (Step06.saddleS r).re ^ 2 :=
    (firstSaddle_coordinates_bounds hrpos (by linarith)).1
  apply firstSaddleCaseTwoError_06
  have h := firstSaddleOmega_lower hn hrpos hr.le (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa using h₀)
  rw [show (6400 : ℝ) * 1 * 0.25 = 40 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 40)] at h
  exact h

theorem firstSaddleCaseTwoError_saddle_09 {n : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0.6 < r) (hr₀ : r ≤ 0.9) :
    firstSaddleCaseTwoError 0.9 ((Step06.saddleS r).re * Real.sqrt (n : ℝ)) 0.692 < 0.648 := by
  have hrpos : 0 < r := by linarith
  have h₀ : r ≤ (Step06.saddleS r).re ^ 2 :=
    (firstSaddle_coordinates_bounds hrpos (by linarith)).1
  apply firstSaddleCaseTwoError_09
  have h := firstSaddleOmega_lower hn hrpos hr.le (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa using h₀)
  rw [show (6400 : ℝ) * 1 * 0.6 = 3840 by norm_num] at h
  exact h

theorem firstSaddleCaseTwoError_saddle_1 {n : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0.9 < r) (hr₀ : r ≤ 1) :
    firstSaddleCaseTwoError 1 ((Step06.saddleS r).re * Real.sqrt (n : ℝ)) 0.827 < 0.886 := by
  have hrpos : 0 < r := by linarith
  apply firstSaddleCaseTwoError_1
  have h := firstSaddleOmega_lower hn hrpos hr.le (by norm_num : (0 : ℝ) ≤ 1.12)
    (firstSaddleRadius_sharp hr.le hr₀).le
  rw [show (6400 : ℝ) * 1.12 * 0.9 = 32256 / 5 by norm_num] at h
  exact h

theorem firstSaddleTable_sum_saddle_003 {n : ℕ} {r : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ 0.03) (hnr : 4 * Real.pi ≤ Real.sqrt ((n : ℝ) * r)) :
    firstSaddleTableSum 0.03 ((Step06.saddleS r).re * Real.sqrt (n : ℝ)) 0.99 < 0.849 := by
  have h := (firstSaddle_coordinates_bounds hr (by linarith)).1
  obtain ⟨hb, hab⟩ := Step06.saddleS_components hr
  have ha : Real.sqrt r ≤ (Step06.saddleS r).re := (Real.sqrt_le_iff).2 ⟨(hb.trans hab).le, h⟩
  apply firstSaddleTable_row1_sum
  rw [mul_comm (n : ℝ) r, Real.sqrt_mul hr.le] at hnr
  exact hnr.trans (mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _))

theorem firstSaddleTable_sum_saddle_01 {n : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0.03 < r) (hr₀ : r ≤ 0.1) :
    firstSaddleTableSum 0.1 ((Step06.saddleS r).re * Real.sqrt (n : ℝ)) 0.99 < 0.765 := by
  have hrpos : 0 < r := by linarith
  have h₀ := (firstSaddle_coordinates_bounds hrpos (by linarith)).1
  apply firstSaddleTable_row2_sum
  have h := firstSaddleOmega_lower hn hrpos hr.le (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa using h₀)
  rw [show (6400 : ℝ) * 1 * 0.03 = 192 by norm_num] at h
  exact h

theorem firstSaddleTable_sum_saddle_025 {n : ℕ} (hn : 6400 ≤ n) {r : ℝ}
    (hr : 0.1 < r) (hr₀ : r ≤ 0.25) :
    firstSaddleTableSum 0.25 ((Step06.saddleS r).re * Real.sqrt (n : ℝ)) 0.55 < 0.785 := by
  have hrpos : 0 < r := by linarith
  have h₀ := (firstSaddle_coordinates_bounds hrpos (by linarith)).1
  apply firstSaddleTable_row3_sum
  have h := firstSaddleOmega_lower hn hrpos hr.le (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa using h₀)
  rw [show (6400 : ℝ) * 1 * 0.1 = 640 by norm_num] at h
  exact h

/-- The page 22 envelope for the actual saddle line, for each of the certified rows. -/
theorem FirstSaddleArcRow.saddleEnvelope {n : ℕ} (hn : 6400 ≤ n)
    {r r₀ β off high pi μ : ℝ}
    (hr : 0 < r) (hrr : r ≤ r₀) (hr₀ : r₀ ≤ 1) (hβ : 0 < β)
    (h : FirstSaddleArcRow r₀ β off high pi μ) :
    let u := (Step06.saddleS r).re / Real.sqrt (n : ℝ)
    firstSaddleOffArcs r₀ u / β < μ ∧ firstSaddleHighDenominatorArc r₀ u / β < μ ∧
      firstSaddlePiArc r₀ u / β < μ ∧ 0.478 / β < μ :=
  h.envelope (hr.le.trans hrr) hβ (firstSaddleRadius_leU0 hn hr hrr hr₀)

end DurfeeCCS.Step07
