module

public import DurfeeCCS.Step10.OuterFarData
public import Mathlib.Data.Nat.Sqrt
public import DurfeeCCS.Step07.OuterTable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The size restrictions and exact exponent gap in Lemma 4.3. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real

theorem outerY_gt80 {n : ℕ} (hn : 6401 ≤ n) : 80 < outerY n := by
  have : (6401 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.lt_sqrt_of_sq_lt (by linarith)

theorem cast_sq_lt_of_lt_sqrt {n d : ℕ} (hd : d < n.sqrt) : d ^ 2 < n :=
  (pow_lt_pow_left₀ hd (Nat.zero_le _) (by decide : 2 ≠ 0)).trans_le (Nat.sqrt_le' _)

theorem farRadius_pos {n d : ℕ} (hd : d ^ 2 < n) : 0 < farRadius n d := by
  have h : (d : ℝ) ^ 2 + 1 ≤ n := by exact_mod_cast (show d ^ 2 + 1 ≤ n by omega)
  have hn : 0 < n := by omega
  exact Real.sqrt_pos.mpr (by rw [outerY_sq hn]; linarith)

theorem farRadius_sq {n d : ℕ} (hd : d ^ 2 < n) :
    (farRadius n d) ^ 2 = (outerY n) ^ 2 - (d : ℝ) ^ 2 :=
  Real.sq_sqrt (Real.sqrt_pos.mp (farRadius_pos hd)).le

theorem farShift_eq {n d : ℕ} (hd : d ^ 2 < n) :
    sqrt (((n - d ^ 2 : ℕ) : ℝ) - 1 / 12) = farRadius n d := by
  have hn : 0 < n := by omega
  unfold farRadius
  rw [outerY_sq hn, Nat.cast_sub hd.le, Nat.cast_pow]
  congr 1
  ring

theorem farCube_eq {y : ℝ} (hy : 0 ≤ y) : (y ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = y := by
  rw [← Real.rpow_mul_natCast hy, show (1 / 3 : ℝ) * (3 : ℕ) = 1 by norm_num, rpow_one]

theorem farCube_gt {y : ℝ} (hy : 80 ≤ y) : (4.3 : ℝ) < y ^ (1 / 3 : ℝ) := by
  have hy0 : 0 ≤ y := by linarith
  by_contra! h
  have hle' := pow_le_pow_left₀ (rpow_nonneg hy0 (1 / 3 : ℝ)) h 3
  rw [farCube_eq hy0] at hle'
  norm_num at hle'
  linarith

theorem farParameters_of_size {n d : ℕ} (hn : 6401 ≤ n) (hd : d < n.sqrt) :
    (n.sqrt : ℝ) > outerY n - 1 ∧
      (n.sqrt : ℝ) < outerY n + 1 / (12 * outerY n) ∧
      (d : ℝ) < outerY n ∧
      1.96 * outerY n < (farRadius n d) ^ 2 ∧
      12.5 < farRadius n d := by
  let y := outerY n
  let m := n.sqrt
  let f := farRadius n d
  have hn0 : 0 < n := by omega
  have hy80 : 80 < y := outerY_gt80 hn
  have hy0 : 0 < y := by linarith
  have hy2 : y ^ 2 = (n : ℝ) - 1 / 12 := outerY_sq hn0
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by dsimp [m]; omega)
  have hmsq : (m : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hnmsq : (n : ℝ) < ((m : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
  have hmlo : y - 1 < m := by nlinarith
  have hmp : (m : ℝ) < y + 1 / (12 * y) := by
    have hdiff : (m : ℝ) - y < 1 / (12 * y) := by
      apply (lt_div_iff₀ (by positivity : 0 < 12 * y)).mpr
      by_cases hm : (m : ℝ) ≤ y
      · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hm) (by positivity)).trans_lt
          (by norm_num)
      · have hmy : 0 < (m : ℝ) - y := sub_pos.mpr (lt_of_not_ge hm)
        nlinarith [sq_pos_of_pos hmy]
    linarith
  have hdsq := cast_sq_lt_of_lt_sqrt hd
  have hfpos : 0 < f := farRadius_pos hdsq
  have hf2 : f ^ 2 = y ^ 2 - (d : ℝ) ^ 2 := farRadius_sq hdsq
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hdy : (d : ℝ) < y := by nlinarith
  have hdm : (d : ℝ) ≤ (m : ℝ) - 1 := by
    have h' : (d : ℝ) + 1 ≤ m := by exact_mod_cast (show d + 1 ≤ m by exact hd)
    linarith
  have hdm2 := pow_le_pow_left₀ hd0 hdm 2
  have hflo : 1.96 * y < f ^ 2 := by nlinarith
  have hfl : 12.5 < f := by nlinarith
  exact ⟨hmlo, hmp, hdy, hflo, hfl⟩

theorem farParameters_of_threshold {n d : ℕ} (hn : 6401 ≤ n) (hd : 1 ≤ d)
    (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) :
    farRadius n d < (π / (2 * sqrt 3)) * (outerY n ^ (1 / 3 : ℝ)) ^ 2 ∧
      0.978 * outerY n < (d : ℝ) ∧
      ((n.sqrt - d : ℕ) : ℝ) < 0.42 * outerY n ^ (1 / 3 : ℝ) := by
  let y := outerY n
  let w := y ^ (1 / 3 : ℝ)
  let f := farRadius n d
  have hy80 : 80 < y := outerY_gt80 hn
  have hy : 0 < y := by linarith
  have hw : 0 < w := Real.rpow_pos_of_pos hy _
  have hwlo : 4.3 < w := farCube_gt hy80.le
  have hwcub : w ^ 3 = y := farCube_eq hy.le
  have hdsq := cast_sq_lt_of_lt_sqrt hdm
  have hf : 0 < f := farRadius_pos hdsq
  have hfsq : f ^ 2 = y ^ 2 - (d : ℝ) ^ 2 := farRadius_sq hdsq
  have hs3 : 0 < sqrt 3 := by positivity
  have hs3sq : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hπlo := Real.pi_gt_three
  have hπhi := Real.pi_lt_d2
  obtain ⟨_, hmhi, hdy, _, _⟩ := farParameters_of_size hn hdm
  change ((n.sqrt : ℝ) < y + _) at hmhi
  change ((d : ℝ) < y) at hdy
  have hmul : 4 * w * (sqrt 3 * f) ≤ 2 * π * (d : ℝ) :=
    (le_div_iff₀ (mul_pos hs3 hf)).mp hfar
  have hcmp : 2 * sqrt 3 * w * f ≤ π * (d : ℝ) := by linarith
  have hcmp2 := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * sqrt 3 * w * f) hcmp 2
  simp only [mul_pow, hs3sq] at hcmp2
  norm_num at hcmp2
  have hfhi : f < (π / (2 * sqrt 3)) * w ^ 2 := by
    calc
      f ≤ π * (d : ℝ) / (2 * sqrt 3 * w) :=
        (le_div_iff₀ (by positivity)).mpr (by nlinarith)
      _ < π * y / (2 * sqrt 3 * w) :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hdy pi_pos) (by positivity)
      _ = _ := by rw [← hwcub]; field_simp
  have hf987 : f ^ 2 ≤ (0.045 : ℝ) * (d : ℝ) ^ 2 := by
    have hp : π ^ 2 ≤ (3.15 : ℝ) ^ 2 := by
      gcongr
    have hw2 : (4.3 : ℝ) ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (by norm_num) hwlo.le 2
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have h1 := mul_le_mul_of_nonneg_right hp (sq_nonneg (d : ℝ))
    have h2 := mul_le_mul_of_nonneg_right hw2 (sq_nonneg f)
    nlinarith
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hdl : 0.978 * y < (d : ℝ) := by
    by_contra! h
    have ht := pow_le_pow_left₀ hd0 h 2
    nlinarith [sq_pos_of_pos hy]
  have hfhsq := pow_lt_pow_left₀ hfhi hf.le (by decide : 2 ≠ 0)
  have hhalf : (π / (2 * sqrt 3)) ^ 2 < (0.827 : ℝ) := by
    rw [div_pow, mul_pow, hs3sq]
    apply (div_lt_iff₀ (by norm_num : 0 < (2 : ℝ) ^ 2 * 3)).mpr
    nlinarith [pow_lt_pow_left₀ hπhi pi_pos.le (by decide : 2 ≠ 0)]
  have hfhsq' : f ^ 2 < 0.827 * w ^ 4 := by
    apply hfhsq.trans
    rw [mul_pow, ← pow_mul]
    exact mul_lt_mul_of_pos_right hhalf (by positivity)
  have hdiff : y - (d : ℝ) < 0.419 * w := by
    have hlt : 1.978 * y < y + (d : ℝ) := by linarith
    have hmul' := mul_lt_mul_of_pos_left hlt (by positivity : 0 < 0.419 * w)
    have hrewrite : 0.419 * w * (1.978 * y) = 0.828782 * w ^ 4 := by
      rw [← hwcub]
      ring
    rw [hrewrite] at hmul'
    have hfhsq'' : f ^ 2 < (0.419 * w) * (y + (d : ℝ)) := by
      exact hfhsq'.trans (lt_of_le_of_lt (by gcongr; norm_num) hmul')
    have hfsub : f ^ 2 = (y - d) * (y + d) := by rw [hfsq]; ring
    rw [hfsub] at hfhsq''
    exact (mul_lt_mul_iff_left₀ (show 0 < y + (d : ℝ) by positivity)).mp hfhsq''
  have hsmall : 1 / (12 * y) < 0.001 * w := by
    apply (div_lt_iff₀ (by positivity : 0 < 12 * y)).mpr
    have h0 := mul_lt_mul hwlo hy80.le (by norm_num : (0 : ℝ) < 80) hw.le
    nlinarith
  refine ⟨hfhi, hdl, ?_⟩
  rw [Nat.cast_sub hdm.le]
  change (n.sqrt : ℝ) - (d : ℝ) < 0.42 * w
  linarith

/-- Exact exponent deficit of any other positive shifted index. -/
theorem farExponentGap {n d l : ℕ} (hd : d ^ 2 < n) (hl : l ^ 2 < n) :
    farSample n d * (d : ℝ) + 2 * π / sqrt 3 * farRadius n d -
      farSample n d * (l : ℝ) - 2 * π / sqrt 3 * farRadius n l =
    π / (sqrt 3 * farRadius n d) *
      (((d : ℝ) - l) ^ 2 + (farRadius n l - farRadius n d) ^ 2) := by
  have hf := farRadius_sq hd
  have hg := farRadius_sq hl
  have hfn := (farRadius_pos hd).ne'
  have hs : sqrt (3 : ℝ) ≠ 0 := by positivity
  unfold farSample
  field_simp
  linear_combination hf - hg

end DurfeeCCS.Step10
