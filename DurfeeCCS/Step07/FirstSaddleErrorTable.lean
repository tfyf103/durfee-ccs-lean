module

public import DurfeeCCS.Step07.FirstSaddleArcTable
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-! Explicit local and nonlocal error bounds from the table on page 23. -/

@[expose] public section

open scoped BigOperators

namespace DurfeeCCS.Step07

noncomputable def firstSaddleRectError (r : ℝ) : ℝ :=
  (3 * 24.54) / (4 * Real.pi) * (Real.exp (5.33 * r * firstSaddleU0 r) - 1)

noncomputable def firstSaddleRectComplement (ω : ℝ) : ℝ :=
  (3 * ω / 2) *
    (1.5 * Real.exp (-0.206 * ω) +
      Real.exp (2.76 - 0.2 * ω) / (0.1 * ω - 0.69) +
      3600 * Real.exp (-9 * ω / 17) +
      1760000 * Real.exp (-49 * ω / 65) +
      (105 / 4) * Real.exp (-0.275 * ω))

noncomputable def firstSaddleMinorArcError (ω μ : ℝ) : ℝ :=
  12 * Real.pi * ω ^ 2 * Real.exp (-(1 - μ) * ω)

/-- Monotonicity beyond the maximum of the polynomial times the exponential. -/
theorem pow_mul_exp_antitone_here {a w c : ℝ} {k : ℕ}
    (ha : 0 < a) (hw : a ≤ w) (hk : (k : ℝ) ≤ c * a) :
    w ^ k * Real.exp (-c * w) ≤ a ^ k * Real.exp (-c * a) := by
  have hEq : w / a = (w - a) / a + 1 := by field_simp; ring
  have hb : w / a ≤ Real.exp ((w - a) / a) := hEq ▸ Real.add_one_le_exp _
  have he := pow_le_pow_left₀ (div_nonneg (ha.le.trans hw) ha.le) hb k
  rw [← Real.exp_nat_mul] at he
  have hc : (k : ℝ) / a ≤ c := (div_le_iff₀ ha).2 hk
  have hh := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hw)
  have hExp : (k : ℝ) * ((w - a) / a) + -c * w ≤ -c * a := by
    linarith only [show (k : ℝ) * ((w - a) / a) ≤ c * (w - a) by
      convert hh using 1
      ring]
  calc
    _ = a ^ k * (w / a) ^ k * Real.exp (-c * w) := by
      rw [← mul_pow, show a * (w / a) = w by field_simp]
    _ ≤ a ^ k * Real.exp ((k : ℝ) * ((w - a) / a)) * Real.exp (-c * w) := by gcongr
    _ = a ^ k * Real.exp ((k : ℝ) * ((w - a) / a) + -c * w) := by
      rw [Real.exp_add, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) (pow_nonneg ha.le k)

private theorem firstSaddleRectComplement_split (ω : ℝ) :
    firstSaddleRectComplement ω = (3 / 2) *
      (1.5 * (ω * Real.exp (-0.206 * ω)) +
       ω / (0.1 * ω - 0.69) * Real.exp (2.76 - 0.2 * ω) +
       3600 * (ω * Real.exp (-(9 / 17) * ω)) +
       1760000 * (ω * Real.exp (-(49 / 65) * ω)) +
       (105 / 4) * (ω * Real.exp (-0.275 * ω))) := by
  unfold firstSaddleRectComplement
  rw [show -9 * ω / 17 = -(9 / 17) * ω by ring,
    show -49 * ω / 65 = -(49 / 65) * ω by ring]
  ring

theorem firstSaddleRectComplement_nonincreasing {a w : ℝ} (ha : 40 ≤ a) (hw : a ≤ w) :
    firstSaddleRectComplement w ≤ firstSaddleRectComplement a := by
  have hapos : 0 < a := by linarith
  have hap : 0 < 0.1 * a - 0.69 := by linarith
  have hwp : 0 < 0.1 * w - 0.69 := by linarith
  have hRatio : w / (0.1 * w - 0.69) ≤ a / (0.1 * a - 0.69) :=
    (div_le_div_iff₀ hwp hap).2 (by nlinarith only [hw])
  have h01 := pow_mul_exp_antitone_here (k := 1) (c := 0.206) hapos hw (by norm_num; linarith)
  have h09 := pow_mul_exp_antitone_here (k := 1) (c := 9 / 17) hapos hw (by norm_num; linarith)
  have h49 := pow_mul_exp_antitone_here (k := 1) (c := 49 / 65) hapos hw (by norm_num; linarith)
  have h027 := pow_mul_exp_antitone_here (k := 1) (c := 0.275) hapos hw (by norm_num; linarith)
  simp only [pow_one] at h01 h09 h49 h027
  rw [firstSaddleRectComplement_split, firstSaddleRectComplement_split]
  have hRatio_nonneg : 0 ≤ w / (0.1 * w - 0.69) := div_nonneg (hapos.le.trans hw) hwp.le
  gcongr

theorem firstSaddleMinorArcError_nonincreasing {a w μ : ℝ} (ha : 0 < a) (hw : a ≤ w)
    (hμ : 2 ≤ (1 - μ) * a) :
    firstSaddleMinorArcError w μ ≤ firstSaddleMinorArcError a μ := by
  unfold firstSaddleMinorArcError
  simp only [mul_assoc (12 * Real.pi)]
  exact mul_le_mul_of_nonneg_left
    (pow_mul_exp_antitone_here (k := 2) (c := 1 - μ) ha hw (by exact_mod_cast hμ))
    (by positivity)

private theorem firstSaddleRectError_le {r u z : ℝ} (hr : 0 ≤ r)
    (hu : firstSaddleU0 r ≤ u)
    (he : Real.exp (5.33 * r * u) ≤ z) :
    firstSaddleRectError r ≤ (3 * 24.54) / (4 * 3.141592) * (z - 1) := by
  have hExp : Real.exp (5.33 * r * firstSaddleU0 r) ≤ z :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu (by positivity))).trans he
  have h0 : 0 ≤ Real.exp (5.33 * r * firstSaddleU0 r) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by unfold firstSaddleU0; positivity)
  unfold firstSaddleRectError
  gcongr
  exact Real.pi_gt_d6.le

theorem firstSaddleRectError_06 : firstSaddleRectError 0.6 < 0.200 := by
  have hu : firstSaddleU0 0.6 ≤ 0.010470 :=
    ((Real.sqrt_lt' (by norm_num)).2 (by norm_num :
      (0.6 : ℝ) * (1 + 0.282 * 0.6) / 6400 < 0.010470 ^ 2)).le
  refine (firstSaddleRectError_le (by norm_num) hu (z := 1.03406) ?_).trans_lt
    (by norm_num)
  refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 6) (by norm_num)).trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem firstSaddleRectError_09 : firstSaddleRectError 0.9 < 0.386 := by
  have hu : firstSaddleU0 0.9 ≤ 0.013279 :=
    ((Real.sqrt_lt' (by norm_num)).2 (by norm_num :
      (0.9 : ℝ) * (1 + 0.282 * 0.9) / 6400 < 0.013279 ^ 2)).le
  refine (firstSaddleRectError_le (by norm_num) hu (z := 1.06580) ?_).trans_lt
    (by norm_num)
  refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 6) (by norm_num)).trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem firstSaddleRectError_1 : firstSaddleRectError 1 < 0.460 := by
  have hu : firstSaddleU0 1 ≤ 0.014154 :=
    ((Real.sqrt_lt' (by norm_num)).2 (by norm_num :
      (1 : ℝ) * (1 + 0.282 * 1) / 6400 < 0.014154 ^ 2)).le
  refine (firstSaddleRectError_le (by norm_num) hu (z := 1.07838) ?_).trans_lt
    (by norm_num)
  refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 6) (by norm_num)).trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- Reduce a negative exponent to a positive argument and take a reciprocal. -/
private theorem exp_le_certificate {x y z : ℝ} (hx : x ≤ 0) (hy : 0 < y)
    (h : y ≤ ∑ i ∈ Finset.range 13, (-x / 64) ^ i / i.factorial)
    (hz : (y ^ 64)⁻¹ ≤ z) :
    Real.exp x ≤ z := by
  have hsmall := h.trans (Real.sum_le_exp_of_nonneg
    (div_nonneg (neg_nonneg.mpr hx) (by norm_num : (0 : ℝ) ≤ 64)) 13)
  have hlarge := pow_le_pow_left₀ hy.le hsmall 64
  rw [← Real.exp_nat_mul, show ((64 : ℕ) : ℝ) * (-x / 64) = -x by norm_num; ring] at hlarge
  calc
    _ = (Real.exp (-x))⁻¹ := by rw [← Real.exp_neg, neg_neg]
    _ ≤ (y ^ 64)⁻¹ := inv_anti₀ (by positivity) hlarge
    _ ≤ _ := hz

local macro "certify_exp_negative" y:term : tactic =>
  `(tactic| refine exp_le_certificate (y := $y) ?_ ?_ ?_ ?_ <;>
    norm_num [Finset.sum_range_succ, Nat.factorial])

private theorem firstSaddleRectComplement_le {ω a b c d e : ℝ} (hω : 40 ≤ ω)
    (ha : Real.exp (-0.206 * ω) ≤ a)
    (hb : Real.exp (2.76 - 0.2 * ω) ≤ b)
    (hc : Real.exp (-9 * ω / 17) ≤ c)
    (hd : Real.exp (-49 * ω / 65) ≤ d)
    (he : Real.exp (-0.275 * ω) ≤ e) :
    firstSaddleRectComplement ω ≤
      3 * ω / 2 * (1.5 * a + b / (0.1 * ω - 0.69) + 3600 * c + 1760000 * d + (105 / 4) * e) := by
  have hω₀ : 0 ≤ ω := by linarith
  have hden : 0 < 0.1 * ω - 0.69 := by linarith
  unfold firstSaddleRectComplement
  gcongr

theorem firstSaddleRectComplement_40 {ω : ℝ} (hω : (40 : ℝ) ≤ ω) :
    firstSaddleRectComplement ω < 0.147 := by
  have h : (40 : ℝ) ≤ ω := hω
  have h1 : Real.exp (-0.206 * 40) ≤ 0.00026388689 := by
    certify_exp_negative 1.137405735
  have h2 : Real.exp (2.76 - 0.2 * 40) ≤ 0.0053003099 := by
    certify_exp_negative 1.085320134
  have h3 : Real.exp (-9 * 40 / 17) ≤ 0.00000000063559434 := by
    certify_exp_negative 1.392195992
  have h4 : Real.exp (-49 * 40 / 65) ≤ 0.000000000000080233429 := by
    certify_exp_negative 1.601841403
  have h5 : Real.exp (-0.275 * 40) ≤ 0.000016701868 := by
    certify_exp_negative 1.18752938
  refine (firstSaddleRectComplement_nonincreasing (by norm_num) h).trans_lt ?_
  refine (firstSaddleRectComplement_le (by norm_num) h1 h2 h3 h4 h5).trans_lt ?_
  norm_num

theorem firstSaddleRectComplement_sqrt3840 {ω : ℝ} (hω : Real.sqrt 3840 ≤ ω) :
    firstSaddleRectComplement ω < 0.00161 := by
  have h : (61.967733 : ℝ) ≤ ω := (Real.le_sqrt_of_sq_le (by norm_num)).trans hω
  have h1 : Real.exp (-0.206 * 61.967733) ≤ 0.0000028581300 := by
    certify_exp_negative 1.220741717
  have h2 : Real.exp (2.76 - 0.2 * 61.967733) ≤ 0.000065495011 := by
    certify_exp_negative 1.162443393
  have h3 : Real.exp (-9 * 61.967733 / 17) ≤ 0.0000000000000056538658 := by
    certify_exp_negative 1.669627806
  have h4 : Real.exp (-49 * 61.967733 / 65) ≤ 0.0000000000000000000051559933 := by
    certify_exp_negative 2.074890523
  have h5 : Real.exp (-0.275 * 61.967733) ≤ 0.000000039731697 := by
    certify_exp_negative 1.305084254
  refine (firstSaddleRectComplement_nonincreasing (by norm_num) h).trans_lt ?_
  refine (firstSaddleRectComplement_le (by norm_num) h1 h2 h3 h4 h5).trans_lt ?_
  norm_num

theorem firstSaddleRectComplement_sqrt32256div5 {ω : ℝ} (hω : Real.sqrt (32256 / 5) ≤ ω) :
    firstSaddleRectComplement ω < 0.000040 := by
  have h : (80.319362 : ℝ) ≤ ω := (Real.le_sqrt_of_sq_le (by norm_num)).trans hω
  have h1 : Real.exp (-0.206 * 80.319362) ≤ 0.000000065201813 := by
    certify_exp_negative 1.295022338
  have h2 : Real.exp (2.76 - 0.2 * 80.319362) ≤ 0.0000016680382 := by
    certify_exp_negative 1.231056821
  have h3 : Real.exp (-9 * 80.319362 / 17) ≤ 0.00000000000000000034113619 := by
    certify_exp_negative 1.943336781
  have h4 : Real.exp (-49 * 80.319362 / 65) ≤ 0.0000000000000000000000000050599945 := by
    certify_exp_negative 2.575566235
  have h5 : Real.exp (-0.275 * 80.319362) ≤ 0.00000000025549596 := by
    certify_exp_negative 1.412162556
  refine (firstSaddleRectComplement_nonincreasing (by norm_num) h).trans_lt ?_
  refine (firstSaddleRectComplement_le (by norm_num) h1 h2 h3 h4 h5).trans_lt ?_
  norm_num

private theorem firstSaddleMinorArcError_le (ω μ : ℝ) :
    firstSaddleMinorArcError ω μ ≤ 12 * 3.141593 * ω ^ 2 * Real.exp (-(1 - μ) * ω) := by
  unfold firstSaddleMinorArcError
  gcongr
  exact Real.pi_lt_d6.le

theorem firstSaddleMinorArcError_40 {ω : ℝ} (hω : 40 ≤ ω) :
    firstSaddleMinorArcError ω 0.479 < 0.000054 := by
  refine (firstSaddleMinorArcError_nonincreasing (by norm_num) hω (by norm_num)).trans_lt ?_
  exact (firstSaddleMinorArcError_le 40 0.479).trans_lt (by dyadic_interval +kernel [prec := 65])

theorem firstSaddleMinorArcError_sqrt3840 {ω : ℝ} (hω : Real.sqrt 3840 ≤ ω) :
    firstSaddleMinorArcError ω 0.692 < 0.00075 := by
  have h : (61.967733 : ℝ) ≤ ω := (Real.le_sqrt_of_sq_le (by norm_num)).trans hω
  refine (firstSaddleMinorArcError_nonincreasing (by norm_num) h (by norm_num)).trans_lt ?_
  exact (firstSaddleMinorArcError_le 61.967733 0.692).trans_lt (by dyadic_interval +kernel [prec := 65])

theorem firstSaddleMinorArcError_sqrt32256div5 {ω : ℝ} (hω : Real.sqrt (32256 / 5) ≤ ω) :
    firstSaddleMinorArcError ω 0.827 < 0.225 := by
  have h : (80.319362 : ℝ) ≤ ω := (Real.le_sqrt_of_sq_le (by norm_num)).trans hω
  refine (firstSaddleMinorArcError_nonincreasing (by norm_num) h (by norm_num)).trans_lt ?_
  exact (firstSaddleMinorArcError_le 80.319362 0.827).trans_lt (by dyadic_interval +kernel [prec := 65])

/-- Sum of the five explicit error bounds in the second case of Proposition 3.5. -/
noncomputable def firstSaddleCaseTwoError (r ω μ : ℝ) : ℝ :=
  firstSaddleRectError r + firstSaddleRectComplement ω + firstSaddleE ω 0.55 +
    firstSaddleMinorArcError ω μ + firstSaddleL16 ω

private theorem firstSaddleE_on_tail {a ω b : ℝ}
    (ha : 2 ≤ a) (hω : a ≤ ω) (hb : firstSaddleE a 0.55 < b) :
    firstSaddleE ω 0.55 < b := by
  have hA := antitoneOn_firstSaddleE (γ := 0.55) (m := 2) (by norm_num) le_rfl
  exact (hA ha (ha.trans hω) hω).trans_lt hb

private theorem firstSaddleL16_on_tail {ω : ℝ} (hω : 40 ≤ ω) : firstSaddleL16 ω < 0.001 := by
  have hA := antitoneOn_firstSaddleL16 (show 40 ∈ Set.Ici (12 : ℝ) by norm_num)
    (show ω ∈ Set.Ici (12 : ℝ) from (by norm_num : (12 : ℝ) ≤ 40).trans hω) hω
  exact hA.trans_lt firstSaddleL16_40

theorem firstSaddleCaseTwoError_06 {ω : ℝ} (hω : 40 ≤ ω) :
    firstSaddleCaseTwoError 0.6 ω 0.479 < 0.753 := by
  unfold firstSaddleCaseTwoError
  linarith only [firstSaddleRectError_06, firstSaddleRectComplement_40 hω,
    firstSaddleE_on_tail (by norm_num) hω firstSaddleE_40, firstSaddleMinorArcError_40 hω,
    firstSaddleL16_on_tail hω]

theorem firstSaddleCaseTwoError_09 {ω : ℝ} (hω : Real.sqrt 3840 ≤ ω) :
    firstSaddleCaseTwoError 0.9 ω 0.692 < 0.648 := by
  have h₀ : (40 : ℝ) ≤ Real.sqrt 3840 := Real.le_sqrt_of_sq_le (by norm_num)
  unfold firstSaddleCaseTwoError
  linarith only [firstSaddleRectError_09, firstSaddleRectComplement_sqrt3840 hω,
    firstSaddleE_on_tail ((by norm_num : (2 : ℝ) ≤ 40).trans h₀) hω firstSaddleE_sqrt3840,
    firstSaddleMinorArcError_sqrt3840 hω, firstSaddleL16_on_tail (h₀.trans hω)]

theorem firstSaddleCaseTwoError_1 {ω : ℝ} (hω : Real.sqrt (32256 / 5) ≤ ω) :
    firstSaddleCaseTwoError 1 ω 0.827 < 0.886 := by
  have h₀ : (40 : ℝ) ≤ Real.sqrt (32256 / 5) := Real.le_sqrt_of_sq_le (by norm_num)
  unfold firstSaddleCaseTwoError
  linarith only [firstSaddleRectError_1, firstSaddleRectComplement_sqrt32256div5 hω,
    firstSaddleE_on_tail ((by norm_num : (2 : ℝ) ≤ 40).trans h₀) hω firstSaddleE_sqrt32256div5,
    firstSaddleMinorArcError_sqrt32256div5 hω, firstSaddleL16_on_tail (h₀.trans hω)]

end DurfeeCCS.Step07
