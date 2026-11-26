module

public import DurfeeCCS.Step06.Dilog
public import DurfeeCCS.Step07.FirstSaddleErrors

/-! Exact endpoint evaluations for the arc bounds on page 22 of the manuscript. -/

@[expose] public section

open scoped BigOperators

namespace DurfeeCCS.Step07

/-- The page 21 bound for the terms with index at least eight. -/
noncomputable def firstSaddleTail (r : ℝ) : ℝ :=
  if r = 1 then 2 / 7 else min (2 / 7) (r ^ 7 / (32 * (1 - r)))

/-- The page 21 bound for the odd terms with index at least thirty-three. -/
noncomputable def firstSaddleOddTail (r : ℝ) : ℝ :=
  if r = 1 then 1 / 32 else 2 * r ^ 32 / (33 ^ 2 * (1 - r ^ 2))

noncomputable def firstSaddleOffArcs (r u : ℝ) : ℝ :=
  2 * u / (0.99 * 0.07) *
    (∑ k ∈ Finset.range 7, r ^ k / ((k + 1 : ℕ) : ℝ) ^ 2) + firstSaddleTail r

noncomputable def firstSaddleHighDenominatorArc (r u : ℝ) : ℝ :=
  2 * (r ^ 2 / 9 + r ^ 5 / 36) +
    u / 0.129 * (∑ k ∈ Finset.range 7, r ^ k / ((k + 1 : ℕ) : ℝ)) + firstSaddleTail r

noncomputable def firstSaddlePiArc (r u : ℝ) : ℝ :=
  (Step06.principalDilog ((r ^ 2 : ℝ) : ℂ)).re / (2 * r) +
    u / 0.466 * (∑ k ∈ Finset.range 16, r ^ (2 * k) / ((2 * k + 1 : ℕ) : ℝ)) +
    firstSaddleOddTail r

theorem principalDilog_upper_geometric {w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 1) :
    (Step06.principalDilog (w : ℂ)).re ≤
      (∑ k ∈ Finset.range 8, w ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2) +
        w ^ 9 / (81 * (1 - w)) := by
  let a (k : ℕ) := w ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2
  let b (k : ℕ) := (w ^ 9 / 81) * w ^ k
  have h := Step06.principalDilog_hasSum (z := (w : ℂ)) (by simpa [abs_of_nonneg hw₀] using hw.le)
  have ha : HasSum a (Step06.principalDilog (w : ℂ)).re := by
    convert Complex.reCLM.hasSum h using 1
    · funext k
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
        ← Complex.ofReal_div]
      rfl
    · rfl
  have hb := (hasSum_geometric_of_lt_one hw₀ hw).mul_left (w ^ 9 / 81)
  have hab (k : ℕ) : a (k + 8) ≤ b k := by
    dsimp only [a, b]
    have hk : (9 : ℝ) ≤ ((9 + k : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right 9 k
    rw [show k + 8 + 1 = 9 + k by omega, pow_add]
    rw [div_mul_eq_mul_div]
    gcongr
    nlinarith
  calc
    _ = ∑ k ∈ Finset.range 8, a k + ∑' k, a (k + 8) := by
      rw [ha.summable.sum_add_tsum_nat_add, ha.tsum_eq]
    _ ≤ ∑ k ∈ Finset.range 8, a k + ∑' k, b k := by
      exact add_le_add_right ((ha.summable.comp_injective (add_left_injective 8)).tsum_le_tsum
        hab hb.summable) _
    _ = _ := by
      rw [hb.tsum_eq]
      dsimp only [a]
      congr 1
      field_simp

private theorem firstSaddleU0_lt {r u : ℝ} (hu : 0 < u)
    (h : r * (1 + 0.282 * r) / 6400 < u ^ 2) : firstSaddleU0 r < u :=
  (Real.sqrt_lt' hu).2 h

private theorem firstSaddleOffArcs_mono {r u v : ℝ} (hr : 0 ≤ r) (huv : u ≤ v) :
    firstSaddleOffArcs r u ≤ firstSaddleOffArcs r v := by
  unfold firstSaddleOffArcs
  gcongr

private theorem firstSaddleHighDenominatorArc_mono {r u v : ℝ} (hr : 0 ≤ r) (huv : u ≤ v) :
    firstSaddleHighDenominatorArc r u ≤ firstSaddleHighDenominatorArc r v := by
  unfold firstSaddleHighDenominatorArc
  gcongr

private theorem firstSaddlePiArc_le {r u v d : ℝ} (hr : 0 < r) (huv : u ≤ v)
    (hd : (Step06.principalDilog ((r ^ 2 : ℝ) : ℂ)).re ≤ d) :
    firstSaddlePiArc r u ≤
      d / (2 * r) + v / 0.466 * (∑ k ∈ Finset.range 16,
        r ^ (2 * k) / ((2 * k + 1 : ℕ) : ℝ)) + firstSaddleOddTail r := by
  unfold firstSaddlePiArc
  gcongr

private theorem firstSaddlePiArc_mono {r u v : ℝ} (hr : 0 ≤ r) (huv : u ≤ v) :
    firstSaddlePiArc r u ≤ firstSaddlePiArc r v := by
  unfold firstSaddlePiArc
  gcongr

/-- The three strict bounds and the common envelope for the four arcs on page 22. -/
def FirstSaddleArcRow (r β off high pi μ : ℝ) : Prop :=
  firstSaddleOffArcs r (firstSaddleU0 r) / β < off ∧
    firstSaddleHighDenominatorArc r (firstSaddleU0 r) / β < high ∧
      firstSaddlePiArc r (firstSaddleU0 r) / β < pi ∧
        off ≤ μ ∧ high ≤ μ ∧ pi ≤ μ ∧ 0.478 / β < μ

/-- Every saddle line parameter below the endpoint inherits the common arc bound. -/
theorem FirstSaddleArcRow.envelope {r β off high pi μ u : ℝ}
    (h : FirstSaddleArcRow r β off high pi μ)
    (hr : 0 ≤ r) (hβ : 0 < β) (hu : u ≤ firstSaddleU0 r) :
    firstSaddleOffArcs r u / β < μ ∧ firstSaddleHighDenominatorArc r u / β < μ ∧
      firstSaddlePiArc r u / β < μ ∧ 0.478 / β < μ := by
  obtain ⟨hO, hH, hV, hmO, hmH, hmV, h0⟩ := h
  refine ⟨?_, ?_, ?_, h0⟩
  · exact (div_le_div_of_nonneg_right (firstSaddleOffArcs_mono hr hu) hβ.le).trans_lt
      (hO.trans_le hmO)
  · exact (div_le_div_of_nonneg_right (firstSaddleHighDenominatorArc_mono hr hu) hβ.le).trans_lt
      (hH.trans_le hmH)
  · exact (div_le_div_of_nonneg_right (firstSaddlePiArc_mono hr hu) hβ.le).trans_lt
      (hV.trans_le hmV)

theorem firstSaddleArcRow_06 : FirstSaddleArcRow 0.6 1 0.369 0.210 0.359 0.479 := by
  have hu : firstSaddleU0 0.6 ≤ 0.010470 := (firstSaddleU0_lt (by norm_num) (by norm_num)).le
  have hO := firstSaddleOffArcs_mono (by norm_num : 0 ≤ (0.6 : ℝ)) hu
  have hH := firstSaddleHighDenominatorArc_mono (by norm_num : 0 ≤ (0.6 : ℝ)) hu
  have hV := firstSaddlePiArc_le (by norm_num : 0 < (0.6 : ℝ)) hu
    (principalDilog_upper_geometric (w := (0.6 : ℝ) ^ 2) (by norm_num) (by norm_num))
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · rw [div_one]
    refine hO.trans_lt ?_
    norm_num [firstSaddleOffArcs, firstSaddleTail, min_def, Finset.sum_range_succ]
  · rw [div_one]
    refine hH.trans_lt ?_
    norm_num [firstSaddleHighDenominatorArc, firstSaddleTail, min_def, Finset.sum_range_succ]
  · rw [div_one]
    refine hV.trans_lt ?_
    norm_num [firstSaddleOddTail, Finset.sum_range_succ]

theorem firstSaddleArcRow_09 : FirstSaddleArcRow 0.9 1 0.692 0.590 0.658 0.692 := by
  have hu : firstSaddleU0 0.9 ≤ 0.013279 := (firstSaddleU0_lt (by norm_num) (by norm_num)).le
  have hO := firstSaddleOffArcs_mono (by norm_num : 0 ≤ (0.9 : ℝ)) hu
  have hH := firstSaddleHighDenominatorArc_mono (by norm_num : 0 ≤ (0.9 : ℝ)) hu
  have hV := firstSaddlePiArc_le (by norm_num : 0 < (0.9 : ℝ)) hu
    (principalDilog_upper_geometric (w := (0.9 : ℝ) ^ 2) (by norm_num) (by norm_num))
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · rw [div_one]
    refine hO.trans_lt ?_
    norm_num [firstSaddleOffArcs, firstSaddleTail, min_def, Finset.sum_range_succ]
  · rw [div_one]
    refine hH.trans_lt ?_
    norm_num [firstSaddleHighDenominatorArc, firstSaddleTail, min_def, Finset.sum_range_succ]
  · rw [div_one]
    refine hV.trans_lt ?_
    norm_num [firstSaddleOddTail, Finset.sum_range_succ]

theorem firstSaddleArcRow_1 : FirstSaddleArcRow 1 1.12 0.807 0.758 0.827 0.827 := by
  have hu : firstSaddleU0 1 ≤ 0.014154 := (firstSaddleU0_lt (by norm_num) (by norm_num)).le
  have hO := firstSaddleOffArcs_mono (by norm_num : 0 ≤ (1 : ℝ)) hu
  have hH := firstSaddleHighDenominatorArc_mono (by norm_num : 0 ≤ (1 : ℝ)) hu
  have hb : (Step06.principalDilog (((1 : ℝ) ^ 2 : ℝ) : ℂ)).re ≤ 1.644935 := by
    simp only [one_pow, Complex.ofReal_one, Step06.principalDilog_one]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re]
    nlinarith [Real.pi_lt_d6, Real.pi_pos, sq_nonneg (Real.pi - 3.141593)]
  have hV := firstSaddlePiArc_le (by norm_num : 0 < (1 : ℝ)) hu hb
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · apply (div_lt_iff₀ (by norm_num : 0 < (1.12 : ℝ))).2
    refine hO.trans_lt ?_
    norm_num [firstSaddleOffArcs, firstSaddleTail, Finset.sum_range_succ]
  · apply (div_lt_iff₀ (by norm_num : 0 < (1.12 : ℝ))).2
    refine hH.trans_lt ?_
    norm_num [firstSaddleHighDenominatorArc, firstSaddleTail, Finset.sum_range_succ]
  · apply (div_lt_iff₀ (by norm_num : 0 < (1.12 : ℝ))).2
    refine hV.trans_lt ?_
    norm_num [firstSaddleOddTail, Finset.sum_range_succ]

end DurfeeCCS.Step07
