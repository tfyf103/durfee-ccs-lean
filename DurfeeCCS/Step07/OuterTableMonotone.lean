module

public import DurfeeCCS.Step07.OuterTable
public import DurfeeCCS.Step07.PowerDecay
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Uniform reduction of the three parameter-dependent majorants to the endpoint on page 43. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open Real Set

theorem outerHighLowBound_le {c y₀ : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 ≤ y₀) :
    outerHighLowBound c y₀ ≤ outerHighLowBound c 80 := by
  let a := 76 * π ^ 2 * c / 4125
  have hc0 : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 9 / 10).trans hc
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hπ := Real.pi_gt_d2.le
  have h₃ : (3 : ℝ) ≤ a * (1 : ℕ) * (80 : ℝ) ^ 1 := by
    calc
      _ ≤ 76 * 3.14 ^ 2 * (9 / 10 : ℝ) / 4125 * 80 := by norm_num
      _ ≤ _ := by dsimp [a]; simp only [Nat.cast_one, mul_one, pow_one]; gcongr
  have hm := power_mul_exp_antitoneOn (b := 0) 3 1 (by decide) (by decide)
    (by norm_num : (0 : ℝ) ≤ 80) ha h₃
  have hh := hm (show (80 : ℝ) ∈ Ici 80 from le_rfl) hy₀ hy₀
  simp only [pow_one, add_zero] at hh
  unfold outerHighLowBound
  have hleft (y : ℝ) : 29 * c ^ 3 * y ^ 3 / 121 * exp (-76 * π ^ 2 * c * y / 4125) =
      (29 * c ^ 3 / 121) * (y ^ 3 * exp (-a * y)) := by
    rw [show -76 * π ^ 2 * c * y / 4125 = -a * y by dsimp [a]; ring]
    ring
  rw [hleft, hleft]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

private def outerThird (x : ℝ) : ℝ := x ^ (1 / 3 : ℝ)

private theorem outerThird_sq {x : ℝ} (hx : 0 ≤ x) :
    outerThird x ^ (2 : ℕ) = x ^ (2 / 3 : ℝ) := by
  unfold outerThird
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  norm_num

private theorem outerThird_cube {x : ℝ} (hx : 0 ≤ x) : outerThird x ^ (3 : ℕ) = x := by
  unfold outerThird
  rw [← Real.rpow_mul_natCast hx, show (1 / 3 : ℝ) * (3 : ℕ) = 1 by norm_num, Real.rpow_one]

private theorem outerThird_mono {x : ℝ} (hx : 80 ≤ x) : outerThird 80 ≤ outerThird x := by
  apply Real.rpow_le_rpow (by norm_num) hx (by norm_num)

theorem outerHighLargeBound_le {c y₀ : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 ≤ y₀) :
    outerHighLargeBound c y₀ ≤ outerHighLargeBound c 80 := by
  let a := c * π ^ 2 / 12
  let b := 7 * c * π ^ 2 / 40
  have hc0 : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 9 / 10).trans hc
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hπ := Real.pi_gt_d2.le
  have h₇ : (7 : ℝ) ≤ a * (2 : ℕ) * (outerThird 80) ^ 2 := by
    rw [outerThird_sq (by norm_num)]
    calc
      _ ≤ (9 / 10 : ℝ) * 3.14 ^ 2 / 12 * 2 * 18.5663553344511 := by norm_num
      _ ≤ _ := by dsimp [a]; gcongr; exact outerEightyPow_lo.le
  have hm := power_mul_exp_antitoneOn (b := b) 7 2 (by decide) (by decide)
    (Real.rpow_nonneg (by norm_num) _) ha h₇
  have hh := hm (show outerThird 80 ∈ Ici (outerThird 80) from le_rfl)
    (outerThird_mono hy₀) (outerThird_mono hy₀)
  have hrewrite (y : ℝ) (hy : 0 ≤ y) :
      outerHighLargeBound c y =
        (29 * c ^ 3 / 16) * (outerThird y ^ 7 * exp (-a * outerThird y ^ 2 + b)) := by
    unfold outerHighLargeBound
    dsimp only
    rw [← outerThird_sq hy]
    have hexp : -c * π ^ 2 * outerThird y ^ 2 / 12 + 7 * c * π ^ 2 / 40 =
        -a * outerThird y ^ 2 + b := by dsimp [a, b]; ring
    rw [hexp]
    have hp' : y * (outerThird y ^ 2) ^ 2 = outerThird y ^ 7 := by
      rw [show outerThird y ^ 7 = outerThird y ^ 3 * (outerThird y ^ 2) ^ 2 by ring,
        outerThird_cube hy]
    linear_combination (29 * c ^ 3 / 16) * exp (-a * outerThird y ^ 2 + b) * hp'
  rw [hrewrite _ (by linarith), hrewrite _ (by norm_num)]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

theorem outerLowerBound_le {c y₀ : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 ≤ y₀) :
    outerLowerBound c y₀ ≤ outerLowerBound c 80 := by
  let a := 17 * c * π ^ 2 / 120
  have hc0 : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 9 / 10).trans hc
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hπ := Real.pi_gt_d2.le
  have h₅ : (5 : ℝ) ≤ a * (2 : ℕ) * (outerThird 80) ^ 2 := by
    rw [outerThird_sq (by norm_num)]
    calc
      _ ≤ 17 * (9 / 10 : ℝ) * 3.14 ^ 2 / 120 * 2 * 18.5663553344511 := by norm_num
      _ ≤ _ := by dsimp [a]; gcongr; exact outerEightyPow_lo.le
  have hm := power_mul_exp_antitoneOn (b := 0) 5 2 (by decide) (by decide)
    (Real.rpow_nonneg (by norm_num) _) ha h₅
  have hh := hm (show outerThird 80 ∈ Ici (outerThird 80) from le_rfl)
    (outerThird_mono hy₀) (outerThird_mono hy₀)
  simp only [add_zero] at hh
  have hrewrite (y : ℝ) (hy : 0 ≤ y) : outerLowerBound c y =
        (7 * c ^ 2 / 2) * (outerThird y ^ 5 * exp (-a * outerThird y ^ 2)) := by
    unfold outerLowerBound
    dsimp only
    rw [← outerThird_sq hy]
    have hexp : -17 * c * π ^ 2 * outerThird y ^ 2 / 120 =
        -a * outerThird y ^ 2 := by dsimp [a]; ring
    rw [hexp]
    have hp' : y * outerThird y ^ 2 = outerThird y ^ 5 := by
      rw [show outerThird y ^ 5 = outerThird y ^ 3 * outerThird y ^ 2 by ring,
        outerThird_cube hy]
    linear_combination (7 * c ^ 2 / 2) * exp (-a * outerThird y ^ 2) * hp'
  rw [hrewrite _ (by linarith), hrewrite _ (by norm_num)]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

theorem outerHighLowBound_uniform_left {y₀ : ℝ} (hy₀ : 80 ≤ y₀) :
    outerHighLowBound (9 / 10) y₀ < 0.184340 :=
  (outerHighLowBound_le (by norm_num) hy₀).trans_lt outerHighLowBound_left

theorem outerHighLowBound_uniform_right {y₀ : ℝ} (hy₀ : 80 ≤ y₀) :
    outerHighLowBound 1 y₀ < 0.059036 :=
  (outerHighLowBound_le (by norm_num) hy₀).trans_lt outerHighLowBound_right

theorem outerHighLargeBound_uniform_left {y₀ : ℝ} (hy₀ : 80 ≤ y₀) :
    outerHighLargeBound (9 / 10) y₀ < 0.185375 :=
  (outerHighLargeBound_le (by norm_num) hy₀).trans_lt outerHighLargeBound_left

theorem outerHighLargeBound_uniform_right {y₀ : ℝ} (hy₀ : 80 ≤ y₀) :
    outerHighLargeBound 1 y₀ < 0.065639 :=
  (outerHighLargeBound_le (by norm_num) hy₀).trans_lt outerHighLargeBound_right

theorem outerLowerBound_uniform_left {y₀ : ℝ} (hy₀ : 80 ≤ y₀) :
    outerLowerBound (9 / 10) y₀ < 3.005e-7 :=
  (outerLowerBound_le (by norm_num) hy₀).trans_lt outerLowerBound_left_sharp

theorem outerLowerBound_uniform_right {y₀ : ℝ} (hy₀ : 80 ≤ y₀) :
    outerLowerBound 1 y₀ < 2.767e-8 :=
  (outerLowerBound_le (by norm_num) hy₀).trans_lt outerLowerBound_right_sharp

private theorem scaled_power_mul_exp_bound {a h H y Y : ℝ} (n : ℕ) (hn : 0 < n)
    (ha : 0 ≤ a) (hh : 0 < h) (hhH : h ≤ H) (hY : 0 ≤ Y) (hy : Y ≤ y)
    (hthreshold : (n : ℝ) ≤ a * (Y / H)) :
    h * ((y / h) ^ n * exp (-a * (y / h))) ≤
      H * ((Y / H) ^ n * exp (-a * (Y / H))) := by
  have hH := hh.trans_le hhH
  have hz₀ : 0 ≤ Y / H := div_nonneg hY hH.le
  have hz : Y / H ≤ y / h := div_le_div₀ (hY.trans hy) hy hh hhH
  have hm := power_mul_exp_antitoneOn (b := 0) n 1 hn (by decide) hz₀ ha
    (by simpa using hthreshold)
  have h₁ := hm (show Y / H ∈ Ici (Y / H) from le_rfl) hz hz
  simp only [pow_one, add_zero] at h₁
  apply mul_le_mul hhH h₁
  · exact mul_nonneg (pow_nonneg (hz₀.trans hz) _) (exp_nonneg _)
  · exact hH.le

/-- Numerical reduction of the high-frequency bound on the branch `h ≤ 11`. -/
theorem outerHighLowMajorant_le {c y₀ y h : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 ≤ y₀)
    (hy : c * y₀ ≤ y) (hh : 0 < h) (hh11 : h ≤ 11) :
    29 * y ^ 3 / h ^ 2 * exp (-0.152 * 4 * π ^ 2 * y / (3 * h)) ≤
      outerHighLowBound c y₀ := by
  let a := 76 * π ^ 2 / 375
  have hc0 : 0 ≤ c := by linarith
  have hy₀0 : 0 ≤ y₀ := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hπ := Real.pi_gt_d2.le
  have hthreshold : 3 ≤ a * (c * y₀ / 11) := by
    calc
      _ ≤ (76 * 3.14 ^ 2 / 375) * ((9 / 10 : ℝ) * 80 / 11) := by norm_num
      _ ≤ _ := by dsimp [a]; gcongr
  have hu := scaled_power_mul_exp_bound 3 (by decide) ha hh hh11
    (mul_nonneg hc0 hy₀0) hy hthreshold
  calc
    _ = 29 * (h * ((y / h) ^ 3 * exp (-a * (y / h)))) := by
      rw [show -0.152 * 4 * π ^ 2 * y / (3 * h) = -a * (y / h) by
        dsimp [a]; field_simp; ring]
      field_simp
    _ ≤ 29 * (11 * ((c * y₀ / 11) ^ 3 * exp (-a * (c * y₀ / 11)))) := by gcongr
    _ = _ := by
      unfold outerHighLowBound
      rw [show -a * (c * y₀ / 11) = -76 * π ^ 2 * c * y₀ / 4125 by
        dsimp [a]; ring]
      ring

private theorem outerQuotient_at_cap {y₀ : ℝ} (hy₀ : 0 < y₀) :
    y₀ / (4 * outerThird y₀) = y₀ ^ (2 / 3 : ℝ) / 4 := by
  have ht : 0 < outerThird y₀ := Real.rpow_pos_of_pos hy₀ _
  rw [← outerThird_sq hy₀.le]
  calc
    _ = outerThird y₀ ^ 3 / (4 * outerThird y₀) := by rw [outerThird_cube hy₀.le]
    _ = _ := by field_simp

/-- Numerical reduction of the lower-endpoint error majorant. -/
theorem outerLowerMajorant_le {c y₀ y h : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 ≤ y₀)
    (hy : c * y₀ ≤ y) (hh : 0 < h) (hhH : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    14 * y ^ 2 / h * exp (-17 * π ^ 2 * y / (30 * h)) ≤ outerLowerBound c y₀ := by
  let a := 17 * π ^ 2 / 30
  let H := 4 * outerThird y₀
  have hc0 : 0 ≤ c := by linarith
  have hy₀0 : 0 < y₀ := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hπ := Real.pi_gt_d2.le
  have hp : 18.5663553344511 ≤ y₀ ^ (2 / 3 : ℝ) :=
    outerEightyPow_lo.le.trans (Real.rpow_le_rpow (by norm_num) hy₀ (by norm_num))
  have hquot : c * y₀ / H = c * (y₀ ^ (2 / 3 : ℝ) / 4) := by
    rw [mul_div_assoc, ← outerQuotient_at_cap hy₀0]
  have hthreshold : 2 ≤ a * (c * y₀ / H) := by
    rw [hquot]
    calc
      _ ≤ (17 * 3.14 ^ 2 / 30) * ((9 / 10 : ℝ) * (18.5663553344511 / 4)) := by norm_num
      _ ≤ _ := by dsimp [a]; gcongr
  have hu := scaled_power_mul_exp_bound 2 (by decide) ha hh (show h ≤ H from hhH)
    (mul_nonneg hc0 hy₀0.le) hy hthreshold
  calc
    _ = 14 * (h * ((y / h) ^ 2 * exp (-a * (y / h)))) := by
      rw [show -17 * π ^ 2 * y / (30 * h) = -a * (y / h) by dsimp [a]; field_simp]
      field_simp
    _ ≤ 14 * (H * ((c * y₀ / H) ^ 2 * exp (-a * (c * y₀ / H)))) := by gcongr
    _ = _ := by
      unfold outerLowerBound
      dsimp only [H]
      rw [show -a * (c * y₀ / (4 * outerThird y₀)) = -17 * c * π ^ 2 * y₀ ^ (2 / 3 : ℝ) / 120 by
        change -a * (c * y₀ / H) = _
        rw [hquot]
        dsimp [a]
        ring]
      rw [← outerThird_sq hy₀0.le]
      have ht : 0 < outerThird y₀ := Real.rpow_pos_of_pos hy₀0 _
      field_simp
      rw [outerThird_cube hy₀0.le]
      ring

private theorem highFrequencyReciprocal_antitoneOn {u₀ A y : ℝ} (hu₀ : 0 ≤ u₀)
    (hAy : 0 ≤ A * y) (h54 : 54 ≤ A * y * u₀) :
    AntitoneOn
      (fun u : ℝ => u ^ 2 * exp (-(A * y) * (u / 4 - 8.4 * u ^ 3)))
      (Icc u₀ (1 / 11)) := by
  let f := fun u : ℝ => u ^ 2 * exp (-(A * y) * (u / 4 - 8.4 * u ^ 3))
  have hf (u : ℝ) : HasDerivAt f
      (u * exp (-(A * y) * (u / 4 - 8.4 * u ^ 3)) *
        (2 - A * y * u * (1 / 4 - 25.2 * u ^ 2))) u := by
    have hd : HasDerivAt (fun t : ℝ => -(A * y) * (t / 4 - 8.4 * t ^ 3))
        (-(A * y) * (1 / 4 - 8.4 * ((3 : ℝ) * u ^ 2))) u :=
      (((hasDerivAt_id u).div_const 4).sub
        ((hasDerivAt_pow 3 u).const_mul 8.4)).const_mul (-(A * y))
    have hprod := (hasDerivAt_pow 2 u).mul hd.exp
    change HasDerivAt f _ u at hprod
    convert hprod using 1
    norm_num
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Icc u₀ (1 / 11))
  · exact (fun x hx => (hf x).continuousAt.continuousWithinAt)
  · exact (fun x hx => (hf x).differentiableAt.differentiableWithinAt)
  · intro u hu
    rw [(hf u).deriv]
    have hu' : u ∈ Icc u₀ (1 / 11) := interior_subset hu
    have hu0 : 0 ≤ u := hu₀.trans hu'.1
    have hAu : 54 ≤ A * y * u := h54.trans (mul_le_mul_of_nonneg_left hu'.1 hAy)
    have husq : u ^ 2 ≤ (1 / 11 : ℝ) ^ 2 := pow_le_pow_left₀ hu0 hu'.2 2
    have hg : 0.0417 ≤ (1 / 4 - 25.2 * u ^ 2 : ℝ) := by linarith
    have hb : (2 : ℝ) ≤ A * y * u * (1 / 4 - 25.2 * u ^ 2) := by
      calc
        _ ≤ 54 * 0.0417 := by norm_num
        _ ≤ _ := mul_le_mul hAu hg (by norm_num) (by linarith)
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hb)

/-- Numerical reduction of the high-frequency bound on the branch `11 ≤ h`. -/
theorem outerHighLargeMajorant_le {c y₀ y h : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 ≤ y₀)
    (hy : c * y₀ ≤ y) (hh11 : 11 ≤ h) (hhH : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    29 * y ^ 3 / h ^ 2 * exp (-(4 * π ^ 2 * y / (3 * h)) * (1 / 4 - 8.4 / h ^ 2)) ≤
      outerHighLargeBound c y₀ := by
  let A := 4 * π ^ 2 / 3
  let H := 4 * outerThird y₀
  let Y := c * y₀
  have hH11 : 11 ≤ H := hh11.trans hhH
  have hH : 0 < H := by linarith
  have hh : 0 < h := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hy₀0 : 0 < y₀ := by linarith
  have hY : 0 ≤ Y := mul_nonneg hc0 hy₀0.le
  have hypos := hY.trans hy
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hπ := Real.pi_gt_d2.le
  have hp : 18.5663553344511 ≤ y₀ ^ (2 / 3 : ℝ) :=
    outerEightyPow_lo.le.trans (Real.rpow_le_rpow (by norm_num) hy₀ (by norm_num))
  have hquot : Y / H = c * (y₀ ^ (2 / 3 : ℝ) / 4) := by
    dsimp only [Y]
    rw [mul_div_assoc, ← outerQuotient_at_cap hy₀0]
  have h54 : 54 ≤ A * Y / H := by
    rw [mul_div_assoc, hquot]
    calc
      _ ≤ (4 * 3.14 ^ 2 / 3) * ((9 / 10 : ℝ) * (18.5663553344511 / 4)) := by norm_num
      _ ≤ _ := by dsimp [A]; gcongr
  have h54y : 54 ≤ A * y * H⁻¹ := by
    rw [← div_eq_mul_inv]
    exact h54.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy hA) hH.le)
  have hu0 : 0 ≤ H⁻¹ := inv_nonneg.mpr hH.le
  have hule : H⁻¹ ≤ h⁻¹ := inv_le_inv₀ hH hh |>.mpr hhH
  have hu11 : h⁻¹ ≤ 1 / 11 := by rw [one_div]; exact inv_le_inv₀ hh (by norm_num) |>.mpr hh11
  have hu := highFrequencyReciprocal_antitoneOn hu0 (mul_nonneg hA hypos) h54y
    (show H⁻¹ ∈ Icc H⁻¹ (1 / 11) from ⟨le_rfl, hule.trans hu11⟩)
    (show h⁻¹ ∈ Icc H⁻¹ (1 / 11) from ⟨hule, hu11⟩) hule
  have hgap : (0.180 : ℝ) ≤ 1 / 4 - 8.4 / H ^ 2 := by
    have HH := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11) hH11 2
    have Hsq : 8.4 / H ^ 2 ≤ 8.4 / (11 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) HH
    linarith
  let a := A / H * (1 / 4 - 8.4 / H ^ 2)
  have ha : 0 ≤ a := mul_nonneg (div_nonneg hA hH.le) (by linarith)
  have hthreshold : (3 : ℝ) ≤ a * Y := by
    have he : a * Y = (A * Y / H) * (1 / 4 - 8.4 / H ^ 2) := by dsimp [a]; ring
    rw [he]
    calc
      _ ≤ 54 * 0.180 := by norm_num
      _ ≤ _ := mul_le_mul h54 hgap (by norm_num) (by linarith)
  have hm := power_mul_exp_antitoneOn (b := 0) 3 1 (by decide) (by decide) hY ha
    (by simpa using hthreshold)
  have hYdec := hm (show Y ∈ Ici Y from le_rfl) hy hy
  simp only [pow_one, add_zero] at hYdec
  have hnormalize (x w : ℝ) (hw : 0 < w) :
      29 * x ^ 3 / w ^ 2 * exp (-(4 * π ^ 2 * x / (3 * w)) * (1 / 4 - 8.4 / w ^ 2)) =
      29 * x ^ 3 * (w⁻¹ ^ 2 * exp (-(A * x) * (w⁻¹ / 4 - 8.4 * w⁻¹ ^ 3))) := by
    rw [show -(4 * π ^ 2 * x / (3 * w)) * (1 / 4 - 8.4 / w ^ 2) =
        -(A * x) * (w⁻¹ / 4 - 8.4 * w⁻¹ ^ 3) by dsimp [A]; field_simp,
      inv_pow, div_eq_mul_inv]
    ring
  have hexpEq (x : ℝ) :
      -(A * x) * (H⁻¹ / 4 - 8.4 * H⁻¹ ^ 3) = -a * x := by dsimp [a]; field_simp
  calc
    _ = 29 * y ^ 3 * (h⁻¹ ^ 2 * exp (-(A * y) * (h⁻¹ / 4 - 8.4 * h⁻¹ ^ 3))) :=
      hnormalize y h hh
    _ ≤ 29 * y ^ 3 * (H⁻¹ ^ 2 * exp (-(A * y) * (H⁻¹ / 4 - 8.4 * H⁻¹ ^ 3))) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (29 * H⁻¹ ^ 2) * (y ^ 3 * exp (-a * y)) := by rw [hexpEq]; ring
    _ ≤ (29 * H⁻¹ ^ 2) * (Y ^ 3 * exp (-a * Y)) :=
      mul_le_mul_of_nonneg_left hYdec (by positivity)
    _ = _ := by
      unfold outerHighLargeBound
      dsimp only
      have ht : 0 < outerThird y₀ := Real.rpow_pos_of_pos hy₀0 _
      have he : -a * Y = -c * π ^ 2 * y₀ ^ (2 / 3 : ℝ) / 12 + 7 * c * π ^ 2 / 40 := by
        dsimp only [a]
        rw [show -(A / H * (1 / 4 - 8.4 / H ^ 2)) * Y =
          -(A * (Y / H)) * (1 / 4 - 8.4 / H ^ 2) by ring]
        rw [hquot, ← outerThird_sq hy₀0.le]
        dsimp only [A, H]
        field_simp
        ring
      rw [he, ← outerThird_sq hy₀0.le]
      dsimp only [H, Y]
      field_simp
      rw [show outerThird y₀ ^ 6 = (outerThird y₀ ^ 3) ^ 2 by ring,
        outerThird_cube hy₀0.le]
      ring

/-- Passing from a pointwise two-mode inequality to the first row's geometric majorant.
The index starts at zero for the paired frequencies with magnitude `3π`. -/
theorem outerSmallModeSeries_le {c δ : ℝ} (hc : 0 < c) (hδ : 13 * c * π ^ 4 / 800 ≤ δ)
    {f : ℕ → ℝ} (hf0 : ∀ m, 0 ≤ f m)
    (hf : ∀ m : ℕ, f m ≤ 1.47 * exp (-δ * ((m : ℝ) + 1) * ((m : ℝ) + 2))) :
    Summable f ∧ (∑' m, f m) ≤ outerSmallModeBound c := by
  let d := 13 * c * π ^ 4 / 800
  let q := exp (-4 * d)
  let A := 1.47 * exp (-2 * d)
  have hd : 0 < d := by dsimp [d]; positivity
  have hq0 : 0 ≤ q := exp_nonneg _
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom (m : ℕ) : f m ≤ A * q ^ m := by
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hquad : (2 : ℝ) + 4 * m ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
      cases m with
      | zero => norm_num
      | succ m =>
        have hm1 : 1 ≤ (m.succ : ℝ) := by exact_mod_cast Nat.succ_pos _
        nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm1)]
    have hδ0 : 0 ≤ δ := hd.le.trans hδ
    have hc' : d * (2 + 4 * (m : ℝ)) ≤ δ * (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
      gcongr
    apply (hf m).trans
    dsimp only [A, q]
    rw [mul_assoc (1.47 : ℝ), ← Real.exp_nat_mul, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
    nlinarith [hc']
  have hsum := (summable_geometric_of_lt_one hq0 hq).mul_left A
  have hSummable := hsum.of_nonneg_of_le hf0 hgeom
  refine ⟨hSummable, (hSummable.tsum_le_tsum hgeom hsum).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]
  unfold outerSmallModeBound
  dsimp only [A, q, d]
  rw [show -2 * (13 * c * π ^ 4 / 800) = -13 * c * π ^ 4 / 400 by ring,
    show -4 * (13 * c * π ^ 4 / 800) = -13 * c * π ^ 4 / 200 by ring]
  simp only [div_eq_mul_inv]

theorem outerSmallModeExponent_le {c y₀ y h : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 ≤ y₀)
    (hy : c * y₀ ≤ y) (hh : 0 < h) (hhH : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    13 * c * π ^ 4 / 800 ≤ 26 * π ^ 4 * y / (25 * h ^ 3) := by
  let H := 4 * outerThird y₀
  have hH : 0 < H := hh.trans_le hhH
  have hc0 : 0 ≤ c := by linarith
  have hy₀0 : 0 < y₀ := by linarith
  have hy0 : 0 ≤ y := (mul_nonneg hc0 hy₀0.le).trans hy
  have hhH3 := pow_le_pow_left₀ hh.le (show h ≤ H from hhH) 3
  have hcap : H ^ 3 = 64 * y₀ := by dsimp only [H]; rw [mul_pow, outerThird_cube hy₀0.le]; norm_num
  calc
    _ = 26 * π ^ 4 * (c * y₀) / (25 * H ^ 3) := by rw [hcap]; field_simp; ring
    _ ≤ _ := by
      exact div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hy (by positivity)) (by positivity)
        (mul_le_mul_of_nonneg_left hhH3 (by norm_num))

/-- Numerically bound the upper-endpoint factor multiplied by the normalized small-mode sum. -/
theorem outerUpperMajorant_le {c y₀ y h s : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 ≤ y₀)
    (hy : c * y₀ ≤ y) (hh : 8.76 ≤ h) (hs0 : 0 ≤ s) (hs : s ≤ 1.142 + outerSmallModeBound c) :
    s * (1 / (y * h) + 2 * exp (-2 * (y * h))) ≤ outerUpperBound c := by
  have hc0 : 0 < c := by linarith
  have hprod : (80 : ℝ) * c * 8.76 ≤ y * h := by
    have hy' : 80 * c ≤ y :=
      (mul_le_mul_of_nonneg_right hy₀ hc0.le).trans (by simpa only [mul_comm] using hy)
    exact mul_le_mul hy' hh (by norm_num) ((show 0 ≤ 80 * c by positivity).trans hy')
  have hinv : (1 : ℝ) / (y * h) ≤ 1 / (80 * c * 8.76) :=
    div_le_div_of_nonneg_left zero_le_one (by positivity) hprod
  have hexp : exp (-2 * (y * h)) ≤ exp (-160 * c * 8.76) :=
    exp_le_exp.mpr (by linarith)
  unfold outerUpperBound
  apply mul_le_mul hs (add_le_add hinv (mul_le_mul_of_nonneg_left hexp (by norm_num)))
  · exact add_nonneg (div_nonneg zero_le_one ((show 0 ≤ 80 * c * 8.76 by positivity).trans hprod))
      (by positivity)
  · exact hs0.trans hs

/-- The positive lower bounds on the outer parameters obtained from the manuscript's `n` range. -/
theorem outerParameterLower {n : ℕ} (hn : 6401 ≤ n)
    {h : ℝ} (hh : 2 * log (sqrt ((n : ℝ) - 1 / 12)) ≤ h) :
    80 ≤ sqrt ((n : ℝ) - 1 / 12) ∧ 8.76 < h := by
  have hn' : (6401 : ℝ) ≤ n := by exact_mod_cast hn
  have hy₀ : 80 ≤ sqrt ((n : ℝ) - 1 / 12) := Real.le_sqrt_of_sq_le (by linarith)
  have hl := outerEightyLog_gt.trans_le (Real.log_le_log (by norm_num) hy₀)
  exact ⟨hy₀, (show 8.76 < 2 * log (sqrt ((n : ℝ) - 1 / 12)) by linarith).trans_le hh⟩

end DurfeeCCS.Step07
