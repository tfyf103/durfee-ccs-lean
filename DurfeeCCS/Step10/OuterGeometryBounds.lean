module

public import DurfeeCCS.Step10.OuterDelta
public import DurfeeCCS.Step07.OuterTable
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Set intervalIntegral

private def base (h : ℝ) : ℝ := h ^ 2 + outerA

theorem outerA_bounds : (13.15945 : ℝ) < outerA ∧ outerA < 13.16 := by
  have h₁ := pow_lt_pow_left₀ pi_gt_d6 (by norm_num) (n := 2) (by decide)
  have h₂ := pow_lt_pow_left₀ pi_lt_d6 pi_pos.le (n := 2) (by decide)
  unfold outerA
  constructor <;> linarith

private theorem base_pos (h : ℝ) : 0 < base h := outerBase_pos h

private theorem base_deriv (h : ℝ) : HasDerivAt base (2 * h) h := by
  change HasDerivAt (fun x : ℝ => x ^ 2 + outerA) _ h
  simpa [id, mul_comm] using ((hasDerivAt_id h).pow 2).add_const outerA

private def slope (y h : ℝ) := y * outerA / (base h * sqrt (base h))

private def slopePower (y h : ℝ) := y * outerA * base h ^ (-(3 / 2) : ℝ)

private theorem slope_eq_power (y h : ℝ) : slope y h = slopePower y h := by
  have hp := base_pos h
  have hpow : base h ^ (3 / 2 : ℝ) = base h * sqrt (base h) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [slope, slopePower, Real.rpow_neg hp.le, hpow, div_eq_mul_inv]

private theorem slope_deriv (y h : ℝ) : HasDerivAt (slopePower y)
    (-(3 * y * outerA) * h * base h ^ (-(5 / 2) : ℝ)) h := by
  convert ((base_deriv h).rpow_const (p := -(3 / 2 : ℝ))
    (Or.inl (base_pos h).ne')).const_mul (y * outerA) using 1
  · rfl
  · rw [show (-(3 / 2 : ℝ) - 1) = -(5 / 2 : ℝ) by norm_num]
    ring

private theorem slope_deriv₂ (y h : ℝ) :
    HasDerivAt (fun w => -(3 * y * outerA) * w * base w ^ (-(5 / 2) : ℝ))
      (3 * y * outerA * (4 * h ^ 2 - outerA) * base h ^ (-(7 / 2) : ℝ)) h := by
  convert (((hasDerivAt_id h).const_mul (-(3 * y * outerA))).mul
    ((base_deriv h).rpow_const (p := -(5 / 2 : ℝ)) (Or.inl (base_pos h).ne'))) using 1
  · rfl
  · rw [show (-(5 / 2 : ℝ) - 1) = -(7 / 2 : ℝ) by norm_num]
    have hp : base h ^ (-(5 / 2) : ℝ) = base h ^ (-(7 / 2) : ℝ) * base h := by
      conv_rhs => arg 2; rw [← Real.rpow_one (base h)]
      rw [← Real.rpow_add (base_pos h)]
      norm_num
    rw [hp]
    simp only [id_eq]
    unfold base
    ring

private theorem convex_slope {y : ℝ} (hy : 0 ≤ y) :
    ConvexOn ℝ (Ici (8 : ℝ)) (slopePower y) := by
  apply convexOn_of_deriv2_nonneg' (convex_Ici 8)
  · exact fun h _ => (slope_deriv y h).differentiableAt.differentiableWithinAt
  · have he : deriv (slopePower y) = fun h => -(3 * y * outerA) * h * base h ^ (-(5 / 2) : ℝ) :=
      funext fun h => (slope_deriv y h).deriv
    rw [he]
    exact fun h _ => (slope_deriv₂ y h).differentiableAt.differentiableWithinAt
  · intro h hh
    change 0 ≤ deriv (deriv (slopePower y)) h
    have h8 : 8 ≤ h := hh
    have he : deriv (slopePower y) = fun h => -(3 * y * outerA) * h * base h ^ (-(5 / 2) : ℝ) :=
      funext fun h => (slope_deriv y h).deriv
    rw [he, (slope_deriv₂ y h).deriv]
    have hh' : 0 ≤ 4 * h ^ 2 - outerA := by nlinarith [outerA_bounds.2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy) outerA_pos.le) hh') (Real.rpow_nonneg (base_pos h).le _)

private theorem midpoint_slope {y t : ℝ} (hy : 0 ≤ y) (ht : 8 ≤ t) :
    2 * slope y (t + 1) ≤ outerDelta y (t + 2) - outerDelta y t := by
  let g := slopePower y
  have hD : ∀ x, HasDerivAt (outerDelta y) (g x) x := by
    intro x
    change HasDerivAt (outerDelta y) (slopePower y x) x
    rw [← slope_eq_power]
    exact hasDerivAt_outerDelta y x
  let b := deriv g (t + 1)
  let L : ℝ → ℝ := fun x => g (t + 1) + b * (x - (t + 1))
  have hL (x : ℝ) (hx : x ∈ Icc t (t + 2)) : L x ≤ g x := by
    have hmid : t + 1 ∈ Ici (8 : ℝ) := by exact le_trans ht (by linarith)
    have hx₈ : x ∈ Ici (8 : ℝ) := le_trans ht hx.1
    rcases lt_trichotomy x (t + 1) with hlt | heq | hgt
    · have h := (convex_slope hy).slope_le_deriv hx₈ hmid hlt
        ((slope_deriv y (t + 1)).differentiableAt)
      rw [slope_def_field] at h
      have h' := (div_le_iff₀ (sub_pos.mpr hlt)).mp h
      dsimp [L, b]
      linarith
    · subst x
      simp [L]
    · have h := (convex_slope hy).deriv_le_slope hmid hx₈ hgt
        ((slope_deriv y (t + 1)).differentiableAt)
      rw [slope_def_field] at h
      have h' := (le_div_iff₀ (sub_pos.mpr hgt)).mp h
      dsimp [L, b]
      linarith
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun x => (slope_deriv y x).continuousAt
  let F : ℝ → ℝ := fun x => g (t + 1) * x + b / 2 * (x - (t + 1)) ^ 2
  have hF (x : ℝ) : HasDerivAt F (L x) x := by
    convert (((hasDerivAt_id x).const_mul (g (t + 1))).add
      ((((hasDerivAt_id x).sub_const (t + 1)).pow 2).const_mul (b / 2))) using 1
    · rfl
    · dsimp [L, id]
      norm_num
      ring
  have hf : Continuous L := by dsimp [L]; fun_prop
  have hi₁ := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
    (hf.intervalIntegrable t (t + 2))
  have hi₂ := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x)
    (hg.intervalIntegrable t (t + 2))
  have hm := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (a := t) (b := t + 2) (by linarith)
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) hL
  rw [hi₁, hi₂] at hm
  rw [slope_eq_power]
  dsimp [F] at hm
  linarith only [hm, show g (t + 1) * (t + 2) + b / 2 * (t + 2 - (t + 1)) ^ 2 -
    (g (t + 1) * t + b / 2 * (t - (t + 1)) ^ 2) = 2 * g (t + 1) by ring]

private theorem log6400_bounds : (8.76 : ℝ) < log 6400 ∧ log 6400 < 8.765 := by
  constructor
  · have h := DurfeeCCS.Step07.outerEightyLog_gt
    rw [show (6400 : ℝ) = 80 * 80 by norm_num, log_mul (by norm_num) (by norm_num)]
    linarith
  · rw [log_lt_iff_lt_exp (by norm_num)]
    dyadic_interval +kernel [prec := 28]

theorem outerStart_gt {n : ℕ} (hn : 6401 ≤ n) : (8.76 : ℝ) < outerStart n := by
  have hn' : (6401 : ℝ) ≤ n := by exact_mod_cast hn
  exact log6400_bounds.1.trans (Real.log_lt_log (by norm_num) (by linarith))

theorem outerDelta_start_lower {n : ℕ} (hn : 6401 ≤ n) :
    0.92 * outerY n < outerDelta (outerY n) (outerStart n) := by
  let t := outerStart n
  have ht : 8.76 < t := outerStart_gt hn
  have ht₀ : 0 < t := by linarith
  have hp : 0 < sqrt (t ^ 2 + outerA) := sqrt_pos.2 (outerBase_pos t)
  have hratio : 0.92 < t / sqrt (t ^ 2 + outerA) := by
    apply (lt_div_iff₀ hp).2
    have hs := sq_sqrt (outerBase_pos t).le
    have ht₂ := pow_lt_pow_left₀ ht (by norm_num) (n := 2) (by decide)
    by_contra! h
    have hh := pow_le_pow_left₀ ht₀.le h 2
    nlinarith only [hh, hs, ht₂, outerA_bounds.2]
  unfold outerDelta
  rw [mul_div_assoc]
  simpa only [mul_comm (outerY n) 0.92] using mul_lt_mul_of_pos_left hratio (lt_trans (by norm_num) (eighty_lt_outerY hn))


private theorem expHalf_deriv (t : ℝ) : HasDerivAt (fun s : ℝ => exp (s / 2))
    (exp (t / 2) / 2) t := by
  simpa [id, div_eq_mul_inv] using ((hasDerivAt_id t).div_const 2).exp

private theorem midSlope_at_start (t : ℝ) (ht : log 6400 ≤ t) :
    (0.931 : ℝ) < slope (exp (t / 2)) (t + 1) := by
  let t₀ := log (6400 : ℝ)
  have hbaseUpper : base (t₀ + 1) < 108.52 := by
    have ht₀ : 8.76 < t₀ := log6400_bounds.1
    have hs := pow_lt_pow_left₀ (show t₀ + 1 < 9.765 by linarith [log6400_bounds.2])
      (show 0 ≤ t₀ + 1 by linarith) (n := 2) (by decide)
    unfold base
    linarith [outerA_bounds.2]
  have hsqrt : sqrt (base (t₀ + 1)) < 10.42 :=
    (sqrt_lt' (by norm_num)).2 (by linarith)
  have ht₀exp : exp (t₀ / 2) = 80 := by
    rw [show t₀ = log (80 * 80) by dsimp [t₀]; norm_num,
      log_mul (by norm_num) (by norm_num), show (log 80 + log 80) / 2 = log 80 by ring,
      exp_log (by norm_num)]
  have hnum : 0.931 < slope (exp (t₀ / 2)) (t₀ + 1) := by
    rw [ht₀exp, slope, lt_div_iff₀ (mul_pos (base_pos _) (sqrt_pos.2 (base_pos _)))]
    have hp := mul_lt_mul_of_pos_right hbaseUpper (sqrt_pos.2 (base_pos (t₀ + 1)))
    have hq := mul_lt_mul_of_pos_left hsqrt (show 0 < (108.52 : ℝ) by norm_num)
    linarith only [hp, hq, outerA_bounds.1]
  let f (s : ℝ) := slopePower (exp (s / 2)) (s + 1)
  have hf (s : ℝ) : HasDerivAt f
      (exp (s / 2) * outerA * base (s + 1) ^ (-(3 / 2) : ℝ) *
        (1 / 2 - 3 * (s + 1) / base (s + 1))) s := by
    have hi : HasDerivAt (fun z : ℝ => base (z + 1)) (2 * (s + 1)) s := by
      simpa [id, Function.comp_def] using (base_deriv (s + 1)).comp s ((hasDerivAt_id s).add_const 1)
    convert ((expHalf_deriv s).mul_const outerA).mul
      (hi.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl (base_pos (s + 1)).ne')) using 1
    · rfl
    · rw [Real.rpow_sub_one (base_pos (s + 1)).ne']
      field_simp
      ring
  have hm : StrictMonoOn f (Ici t₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
      (fun s _ => (hf s).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ici] at hs
    have hs₀ : 9 < s + 1 := by linarith [show t₀ < s from hs, log6400_bounds.1]
    have hh : 0 < 1 / 2 - 3 * (s + 1) / base (s + 1) := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ (base_pos (s + 1))).2
      unfold base
      nlinarith only [hs₀, sq_nonneg (s + 1 - 9), outerA_pos]
    rw [(hf s).deriv]
    exact mul_pos (mul_pos (mul_pos (exp_pos _) outerA_pos) (rpow_pos_of_pos (base_pos _) _)) hh
  simp_rw [slope_eq_power] at hnum ⊢
  exact hnum.trans_le (hm.monotoneOn (show t₀ ∈ Ici t₀ from le_rfl) ht ht)

private theorem phaseBound_le_midSlope {y t : ℝ} (hy : 0 ≤ y) (ht : 8.76 ≤ t) :
    2 * π ^ 4 * y / (3 * t * sqrt (t ^ 2 + outerA) ^ 3) ≤ 0.748 * slope y (t + 1) := by
  have ht₀ : 0 < t := by linarith
  let B := base t
  let C := base (t + 1)
  have hB := base_pos t
  have hC := base_pos (t + 1)
  have hB₀ := sqrt_pos.2 hB
  have hC₀ := sqrt_pos.2 hC
  have h2 : C ≤ 1.207 * B := by
    dsimp [B, C, base]
    nlinarith only [ht, sq_nonneg (t - 8.76), outerA_bounds.1]
  have h3 : sqrt C ≤ 1.099 * sqrt B := by
    apply (sqrt_le_left (by positivity : 0 ≤ 1.099 * sqrt B)).2
    nlinarith only [h2, sq_sqrt hB.le, hB.le]
  have h4 : C * sqrt C ≤ (1.207 * 1.099) * (B * sqrt B) := by
    calc
      _ ≤ (1.207 * B) * (1.099 * sqrt B) :=
        mul_le_mul h2 h3 (sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hp : π ^ 2 * (1.207 * 1.099) ≤ 0.748 * (2 * t) := by
    have hπ := pow_le_pow_left₀ pi_pos.le pi_lt_d6.le 2
    linarith only [ht, hπ]
  have hBS : B * sqrt B = sqrt B ^ 3 := by
    linear_combination -(sqrt B) * sq_sqrt hB.le
  have hden : 0 < B * sqrt B := mul_pos hB hB₀
  have hdenC : 0 < C * sqrt C := mul_pos hC hC₀
  change 2 * π ^ 4 * y / (3 * t * sqrt B ^ 3) ≤ 0.748 * (y * outerA / (C * sqrt C))
  rw [← hBS]
  have he : 2 * π ^ 4 * y / (3 * t * (B * sqrt B)) =
      (y * outerA / (C * sqrt C)) * (π ^ 2 * (C * sqrt C) / (2 * t * (B * sqrt B))) := by
    generalize hD : B * sqrt B = D at hden ⊢
    generalize hE : C * sqrt C = E at hdenC ⊢
    unfold outerA
    field_simp [hden.ne', hdenC.ne', ht₀.ne']
    ring
  rw [he, mul_comm (0.748 : ℝ)]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (mul_nonneg hy outerA_pos.le) hdenC.le)
  apply (div_le_iff₀ (by positivity)).2
  calc
    π ^ 2 * (C * sqrt C) ≤ π ^ 2 * ((1.207 * 1.099) * (B * sqrt B)) :=
      mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
    _ = (π ^ 2 * (1.207 * 1.099)) * (B * sqrt B) := by ring
    _ ≤ (0.748 * (2 * t)) * (B * sqrt B) := mul_le_mul_of_nonneg_right hp hden.le
    _ = _ := by ring

private theorem outerY_eq_exp {n : ℕ} (hn : 6401 ≤ n) :
    outerY n = exp (outerStart n / 2) := by
  rw [outerStart_eq (by omega : 1 ≤ n), show 2 * log (outerY n) / 2 = log (outerY n) by ring,
    exp_log (lt_trans (by norm_num) (eighty_lt_outerY hn))]

private theorem log6400_le_start {n : ℕ} (hn : 6401 ≤ n) : log 6400 ≤ outerStart n := by
  have hn' : (6401 : ℝ) ≤ n := by exact_mod_cast hn
  exact (Real.log_lt_log (by norm_num) (by linarith)).le

theorem outerDelta_increment {n : ℕ} (hn : 6401 ≤ n) :
    1.05 + (2 * π ^ 4 * outerY n /
        (3 * outerStart n * sqrt (outerStart n ^ 2 + outerA) ^ 3) + 1 / outerStart n) <
      outerDelta (outerY n) (outerStart n + 2) - outerDelta (outerY n) (outerStart n) := by
  let t := outerStart n
  let y := outerY n
  have ht : 8.76 < t := outerStart_gt hn
  have hy : 0 < y := lt_trans (by norm_num) (eighty_lt_outerY hn)
  have hmid := midpoint_slope hy.le (show 8 ≤ t by linarith)
  have hsmall := phaseBound_le_midSlope hy.le ht.le
  have hmidnum : 0.931 < slope y (t + 1) := by
    rw [show y = exp (t / 2) from outerY_eq_exp hn]
    exact midSlope_at_start t (log6400_le_start hn)
  have hinv : 1 / t < 0.1142 := by
    apply (div_lt_iff₀ (show 0 < t by linarith)).2
    linarith
  linarith only [hmid, hsmall, hmidnum, hinv]


private theorem outerLoss_lower {n : ℕ} (hn : 6401 ≤ n) :
    (4.07 : ℝ) < outerY n * outerA / (2 * base (outerStart n + 2)) := by
  let t₀ := log (6400 : ℝ)
  let f (t : ℝ) := exp (t / 2) * outerA / (2 * base (t + 2))
  have hf (t : ℝ) : HasDerivAt f
      (exp (t / 2) * outerA * (base (t + 2) - 4 * (t + 2)) /
        (4 * base (t + 2) ^ 2)) t := by
    have hq : HasDerivAt (fun u : ℝ => base (u + 2)) (2 * (t + 2)) t := by
      simpa [id, Function.comp_def] using (base_deriv (t + 2)).comp t ((hasDerivAt_id t).add_const 2)
    convert ((expHalf_deriv t).mul_const outerA).div
      (hq.const_mul 2) (mul_ne_zero (by norm_num) (base_pos (t + 2)).ne') using 1
    field_simp
    ring
  have hm : StrictMonoOn f (Ici t₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Ici] at ht
    have ht' : 8 < t := by linarith [show t₀ < t from ht, log6400_bounds.1]
    have hp : 0 < base (t + 2) - 4 * (t + 2) := by
      unfold base
      nlinarith only [ht', outerA_pos, sq_nonneg (t - 8)]
    rw [(hf t).deriv]
    exact div_pos (mul_pos (mul_pos (exp_pos _) outerA_pos) hp) (mul_pos (by norm_num) (pow_pos (base_pos _) 2))
  have ht₀exp : exp (t₀ / 2) = 80 := by
    rw [show t₀ = log (80 * 80) by dsimp [t₀]; norm_num,
      log_mul (by norm_num) (by norm_num), show (log 80 + log 80) / 2 = log 80 by ring,
      exp_log (by norm_num)]
  have hf₀ : 4.07 < f t₀ := by
    have ht₀ := log6400_bounds
    have hs := pow_lt_pow_left₀ (show t₀ + 2 < 10.765 by linarith [ht₀.2])
      (show 0 ≤ t₀ + 2 by linarith [ht₀.1]) (n := 2) (by decide)
    dsimp [f]
    rw [ht₀exp, lt_div_iff₀ (mul_pos (by norm_num) (base_pos _))]
    unfold base
    linarith only [hs, outerA_bounds.1, outerA_bounds.2]
  rw [outerY_eq_exp hn]
  exact hf₀.trans_le (hm.monotoneOn (show t₀ ∈ Ici t₀ from le_rfl)
    (log6400_le_start hn) (log6400_le_start hn))

theorem outerDelta_end_loss {n : ℕ} (hn : 6401 ≤ n) :
    4.07 < outerY n - outerDelta (outerY n) (outerStart n + 2) := by
  let h := outerStart n + 2
  let R := sqrt (base h)
  let y := outerY n
  have hh : 0 < h := by dsimp [h]; linarith [outerStart_gt hn]
  have hR : 0 < R := sqrt_pos.2 (base_pos h)
  have hR₂ : R ^ 2 = base h := sq_sqrt (base_pos h).le
  have hy : 0 < y := lt_trans (by norm_num) (eighty_lt_outerY hn)
  have hhR : h < R := (lt_sqrt hh.le).2 (by unfold base; linarith [outerA_pos])
  have hgap : R - h = outerA / (R + h) := by
    apply (eq_div_iff (by positivity)).2
    unfold base at hR₂
    nlinarith only [hR₂]
  have hloss : y * outerA / (2 * base h) < y - outerDelta y h := by
    change _ < y - y * h / R
    rw [show y - y * h / R = y * (R - h) / R by field_simp, hgap, ← mul_div_assoc, div_div]
    apply div_lt_div_of_pos_left (mul_pos hy outerA_pos) (by positivity)
    have hp := mul_lt_mul_of_pos_right hhR hR
    nlinarith only [hp, hR₂]
  exact (outerLoss_lower hn).trans hloss

theorem outerDelta_end_lt_degree {n : ℕ} (hn : 6401 ≤ n) :
    outerDelta (outerY n) (outerStart n + 2) < (n.sqrt : ℝ) - 1 := by
  have h := outerY_lt_sqrtNat_succ (by omega : 1 ≤ n)
  linarith only [outerDelta_end_loss hn, h]

theorem outerStart_add_two_lt_farThreshold {n : ℕ} (hn : 6401 ≤ n) :
    outerStart n + 2 < farThreshold n := by
  let f (t : ℝ) := 4 * exp (t / 6) - (t + 2)
  have hf (t : ℝ) : HasDerivAt f (4 * (exp (t / 6) / 6) - 1) t := by
    convert ((((hasDerivAt_id t).div_const 6).exp).const_mul 4).sub
      ((hasDerivAt_id t).add_const 2) using 1
    · rfl
    · simp [id, div_eq_mul_inv]
  have he₀ : (4 : ℝ) < exp 1.4 := by dyadic_interval +kernel [prec := 28]
  have he : 4 < exp ((8.76 : ℝ) / 6) :=
    he₀.trans (exp_lt_exp.mpr (by norm_num))
  have hm : StrictMonoOn f (Ici (8.76 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
    intro t ht
    rw [interior_Ici] at ht
    have ht' : 8.76 < t := ht
    have hex := exp_le_exp.mpr (show (8.76 : ℝ) / 6 ≤ t / 6 by linarith)
    rw [(hf t).deriv]
    linarith only [he, hex]
  have hp : 0 < f 8.76 := by dsimp [f]; linarith only [he]
  have hpt := hp.trans (hm (show (8.76 : ℝ) ∈ Ici 8.76 from le_rfl)
    (outerStart_gt hn).le (outerStart_gt hn))
  have hy : 0 < outerY n := lt_trans (by norm_num) (eighty_lt_outerY hn)
  have hE : (outerY n) ^ (1 / 3 : ℝ) = exp (outerStart n / 6) := by
    rw [rpow_def_of_pos hy, outerStart_eq (by omega : 1 ≤ n)]
    congr 1
    ring
  unfold farThreshold
  rw [hE]
  exact sub_pos.mp hpt

end DurfeeCCS.Step10
