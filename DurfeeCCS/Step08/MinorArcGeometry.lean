module

public import DurfeeCCS.Step07.TrigonometricBounds
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Geometry of the short arcs around rational multiples of `2π`, pp. 21–22. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Set DurfeeCCS.Step07
open scoped Real

/-- A lift of an arc of radius 0.07 about a reduced rational multiple of `2π`.
Integer translates of the rational center represent the same arc modulo `2π`. -/
def OnMinorRationalArc (v : ℝ) (q : ℚ) : Prop :=
  q.den ≤ 7 ∧ |v-2*Real.pi*(q : ℝ)| ≤ 0.07

private theorem rat_cast_num_div_den (q : ℚ) : (q : ℝ) = (q.num : ℝ)/q.den := by
  exact_mod_cast q.num_div_den.symm

private theorem one_le_abs_intCast {z : ℤ} (hz : z ≠ 0) : 1 ≤ |(z : ℝ)| := by
  have h : (1 : ℤ) ≤ |z| := by
    rcases lt_or_gt_of_ne hz with h | h
    · rw [abs_of_neg h]
      omega
    · rw [abs_of_pos h]
      omega
  exact_mod_cast h

private theorem rat_abs_ge_inv_den {q : ℚ} (hq : q ≠ 0) :
    1/(q.den : ℝ) ≤ |(q : ℝ)| := by
  have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hden : 0 ≤ (q.den : ℝ) := by positivity
  have hn' := one_le_abs_intCast hn
  rw [rat_cast_num_div_den, abs_div, abs_of_nonneg hden]
  exact div_le_div_of_nonneg_right hn' hden

/-- Distinct reduced centers of denominator at most seven are separated by `2π/42`. -/
theorem minorArc_centers_separated {p q : ℚ} (hp : p.den ≤ 7) (hq : q.den ≤ 7) (hne : p ≠ q) :
    2*Real.pi/42 ≤ |2*Real.pi*(p : ℝ)-2*Real.pi*(q : ℝ)| := by
  have hLC : p.den.lcm q.den ≤ 42 := by
    by_cases he : p.den = q.den
    · rw [he, Nat.lcm_self]
      omega
    · apply (Nat.le_of_dvd (Nat.mul_pos p.den_pos q.den_pos) (Nat.lcm_dvd_mul _ _)).trans
      rcases lt_or_gt_of_ne he with hl | hl
      · exact Nat.mul_le_mul (by omega : p.den ≤ 6) hq |>.trans (by decide)
      · exact Nat.mul_le_mul hp (by omega : q.den ≤ 6) |>.trans (by decide)
  have hden := (Nat.le_of_dvd (Nat.lcm_pos p.den_pos q.den_pos) (Rat.sub_den_dvd_lcm p q)).trans hLC
  have hdenR : ((p-q).den : ℝ) ≤ 42 := by exact_mod_cast hden
  have h0 : 0 < ((p-q).den : ℝ) := by exact_mod_cast (p-q).den_pos
  have hsep := (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) h0 hdenR).trans
    (rat_abs_ge_inv_den (sub_ne_zero.mpr hne))
  rw [show 2*Real.pi*(p : ℝ)-2*Real.pi*(q : ℝ) = 2*Real.pi*((p-q : ℚ) : ℝ) by push_cast; ring,
    abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hsep (by positivity : 0 ≤ 2*Real.pi)

theorem minorArc_unique_center {v : ℝ} {p q : ℚ} (hp : OnMinorRationalArc v p)
    (hq : OnMinorRationalArc v q) : p = q := by
  by_contra hne
  have hsep := minorArc_centers_separated hp.1 hq.1 hne
  have htri := abs_sub_le (2*Real.pi*(p : ℝ)) v (2*Real.pi*(q : ℝ))
  rw [abs_sub_comm (2*Real.pi*(p : ℝ)) v] at htri
  linarith only [hsep, htri, hp.2, hq.2, Real.pi_gt_d2]

/-- In the fundamental interval, the denominator-one arc is the arc about zero. -/
theorem minorArc_den_one_eq_zero {v : ℝ} {q : ℚ} (hv : OnMinorRationalArc v q)
    (hvπ : |v| ≤ Real.pi) (hq : q.den = 1) : q = 0 ∧ |v| ≤ 0.07 := by
  have hq0 : q = 0 := by
    by_contra hn
    have habs := rat_abs_ge_inv_den hn
    rw [hq] at habs
    have hlarge : 2*Real.pi ≤ |2*Real.pi*(q : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]
      norm_num at habs
      exact (le_mul_of_one_le_right (by positivity) habs)
    have hnear := hv.2
    have htri := abs_sub_le (2*Real.pi*(q : ℝ)) v 0
    rw [sub_zero, sub_zero, abs_sub_comm (2*Real.pi*(q : ℝ)) v] at htri
    linarith only [hlarge, htri, hnear, hvπ, Real.pi_gt_d2]
  exact ⟨hq0, by simpa [hq0] using hv.2⟩

private theorem abs_sin_int_translate (x : ℝ) (m : ℤ) :
    |Real.sin x| = |Real.sin (x-(m : ℝ)*Real.pi)| := by
  nth_rw 1 [show x = (x-(m : ℝ)*Real.pi)+(m : ℝ)*Real.pi by ring]
  rw [Real.sin_add_int_mul_pi, abs_mul, abs_zpow]
  simp

private theorem abs_angle_sub_round_pi_le (x : ℝ) :
    |x-(round (x/Real.pi) : ℝ)*Real.pi| ≤ Real.pi/2 := by
  rw [show x-(round (x/Real.pi) : ℝ)*Real.pi = Real.pi*(x/Real.pi-(round (x/Real.pi) : ℝ)) by
    field_simp [Real.pi_ne_zero], abs_mul, abs_of_pos Real.pi_pos]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (abs_sub_round (x/Real.pi)) Real.pi_pos.le

/-- Outside the rational arcs every sine denominator up to order seven is bounded below. -/
theorem minorArc_sin_outside {v : ℝ} (hv : ∀ q : ℚ, ¬OnMinorRationalArc v q)
    {j : ℕ} (hj : 0 < j) (hj₇ : j ≤ 7) :
    0.99*(0.035*j) ≤ |Real.sin (j*v/2)| := by
  let x : ℝ := j*v/2
  let m : ℤ := round (x/Real.pi)
  let q : ℚ := (m : ℚ)/j
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hj₇R : (j : ℝ) ≤ 7 := by exact_mod_cast hj₇
  have hden : q.den ≤ 7 := by
    have hd : q.den ∣ j := by
      apply Int.natCast_dvd_natCast.mp
      rw [show q = Rat.divInt m (j : ℤ) by simp only [q, Rat.divInt_eq_div, Int.cast_natCast]]
      exact Rat.den_dvd m (j : ℤ)
    exact (Nat.le_of_dvd hj hd).trans hj₇
  have hfar : 0.07 < |v-2*Real.pi*(q : ℝ)| :=
    lt_of_not_ge (fun ha => hv q ⟨hden, ha⟩)
  have hdiff : x-(m : ℝ)*Real.pi = (j : ℝ)/2*(v-2*Real.pi*(q : ℝ)) := by
    simp only [x,q,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
    field_simp
  have hmin : 0.035*j ≤ |x-(m : ℝ)*Real.pi| := by
    rw [hdiff, abs_mul, abs_of_pos (by positivity : 0 < (j : ℝ)/2)]
    nlinarith only [mul_le_mul_of_nonneg_left hfar.le (show 0 ≤ (j : ℝ)/2 by positivity)]
  have hmax : |x-(m : ℝ)*Real.pi| ≤ Real.pi/2 := abs_angle_sub_round_pi_le x
  have hlo : 0 ≤ (0.035 : ℝ)*j := by positivity
  have hhi : (0.035 : ℝ)*j ≤ 0.245 := by linarith only [hj₇R]
  change _ ≤ |Real.sin x|
  rw [abs_sin_int_translate x m, Real.abs_sin_eq_sin_abs_of_abs_le_pi
    (hmax.trans (by linarith [Real.pi_pos]))]
  exact (ninetyNine_mul_le_sin hlo hhi).trans
    (Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], hmin.trans hmax⟩
      ⟨by linarith [abs_nonneg (x-(m : ℝ)*Real.pi), Real.pi_pos], hmax⟩ hmin)

/-- On the arc centered at zero the small-angle sine bound gains a factor of eight. -/
theorem minorArc_sin_zero {u v : ℝ} (hu : 16*u ≤ |v|) (hv : |v| ≤ 0.07)
    {j : ℕ} (hj : j ≤ 7) :
    0.99*8*j*u ≤ |Real.sin (j*v/2)| := by
  have hjR : (j : ℝ) ≤ 7 := by exact_mod_cast hj
  have hAbs : |(j : ℝ)*v/2| = (j : ℝ)*|v|/2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg j), abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hcut : |(j : ℝ)*v/2| ≤ 0.245 := by
    rw [hAbs]
    nlinarith only [mul_le_mul hjR hv (abs_nonneg v) (by norm_num : (0 : ℝ) ≤ 7)]
  have h := ninetyNine_mul_le_sin (abs_nonneg ((j : ℝ)*v/2)) hcut
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (hcut.trans (by linarith [Real.pi_gt_d2])), hAbs]
  rw [hAbs] at h
  nlinarith only [h, mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) j)]

private theorem rat_den_dvd_mul_of_eq {q : ℚ} {j : ℕ} {m : ℤ}
    (h : (j : ℤ)*q.num = m*(q.den : ℤ)) : q.den ∣ j := by
  apply q.reduced.symm.dvd_of_dvd_mul_right
  have hd : (q.den : ℤ) ∣ (j : ℤ)*q.num := ⟨m, by rw [h, mul_comm]⟩
  have hp := Int.natAbs_dvd_natAbs.mpr hd
  simpa [Int.natAbs_mul] using hp

private theorem abs_rat_mul_sub_int_ge {q : ℚ} {j : ℕ} (hnd : ¬q.den ∣ j) (m : ℤ) :
    1/(q.den : ℝ) ≤ |(j : ℝ)*(q : ℝ)-(m : ℝ)| := by
  have hden : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have he : (j : ℝ)*(q : ℝ)-(m : ℝ) = (((j : ℤ)*q.num-m*(q.den : ℤ) : ℤ) : ℝ)/q.den := by
    rw [rat_cast_num_div_den]
    push_cast
    field_simp
  have hn : (j : ℤ)*q.num-m*(q.den : ℤ) ≠ 0 := by
    intro he
    exact hnd (rat_den_dvd_mul_of_eq (sub_eq_zero.mp he))
  have hn' := one_le_abs_intCast hn
  rw [he, abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_right hn' hden.le

/-- The nonresonant sine bound on a rational arc of denominator between three and seven. -/
theorem minorArc_sin_nonresonant {v : ℝ} {q : ℚ} (hv : OnMinorRationalArc v q)
    {j : ℕ} (hj : j ≤ 7) (hnd : ¬q.den ∣ j) :
    0.129 < |Real.sin (j*v/2)| := by
  let x : ℝ := j*v/2
  let m : ℤ := round (x/Real.pi)
  have hjR : (j : ℝ) ≤ 7 := by exact_mod_cast hj
  have hden : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hden₇ : (q.den : ℝ) ≤ 7 := by exact_mod_cast hv.1
  have hsep := (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hden hden₇).trans
    (abs_rat_mul_sub_int_ge hnd m)
  have hsep' : Real.pi/7 ≤ |Real.pi*((j : ℝ)*(q : ℝ))-(m : ℝ)*Real.pi| := by
    rw [show Real.pi*((j : ℝ)*(q : ℝ))-(m : ℝ)*Real.pi =
      Real.pi*((j : ℝ)*(q : ℝ)-(m : ℝ)) by ring, abs_mul, abs_of_pos Real.pi_pos]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hsep Real.pi_pos.le
  have hnear : |Real.pi*((j : ℝ)*(q : ℝ))-x| ≤ 0.245 := by
    rw [show Real.pi*((j : ℝ)*(q : ℝ))-x = (j : ℝ)/2*(-(v-2*Real.pi*(q : ℝ))) by unfold x; ring,
      abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ)/2)]
    nlinarith only [mul_le_mul hjR hv.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)]
  have hlow : Real.pi/7-0.245 ≤ |x-(m : ℝ)*Real.pi| := by
    linarith only [hsep', hnear, abs_sub_le (Real.pi*((j : ℝ)*(q : ℝ))) x ((m : ℝ)*Real.pi)]
  have hmax : |x-(m : ℝ)*Real.pi| ≤ Real.pi/2 := abs_angle_sub_round_pi_le x
  have hnum : 0.129 < 2/Real.pi*(Real.pi/7-0.245) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ Real.pi_pos]
    linarith only [Real.pi_gt_d2]
  change 0.129 < |Real.sin x|
  rw [abs_sin_int_translate x m]
  exact (hnum.trans_le (mul_le_mul_of_nonneg_left hlow (by positivity))).trans_le
    (Real.mul_abs_le_abs_sin hmax)

/-- Odd terms up to 31 on the arc centered at `π` modulo `2π`. -/
theorem minorArc_sin_pi_odd {v : ℝ} {q : ℚ} (hv : OnMinorRationalArc v q) (hq : q.den = 2)
    {j : ℕ} (hj : Odd j) (hj₃₁ : j ≤ 31) :
    0.466 < |Real.sin (j*v/2)| := by
  have hjR : (j : ℝ) ≤ 31 := by exact_mod_cast hj₃₁
  have hOdd : Odd q.num := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro h
    obtain ⟨m, hm⟩ := h
    have he : (1 : ℤ)*q.num = m*(q.den : ℤ) := by rw [one_mul, hm, hq]; ring
    have hc := rat_den_dvd_mul_of_eq (j := 1) he
    norm_num [hq] at hc
  have hjZ : Odd (j : ℤ) := by exact_mod_cast hj
  obtain ⟨m, hm⟩ := hjZ.mul hOdd
  have hm' : (j : ℤ)*q.num = 2*m+1 := by omega
  have hmR : (j : ℝ)*(q.num : ℝ) = 2*(m : ℝ)+1 := by exact_mod_cast hm'
  let t : ℝ := j*(v-2*Real.pi*(q : ℝ))/2
  have hcut : |t| ≤ 1.085 := by
    rw [show t = (j : ℝ)/2*(v-2*Real.pi*(q : ℝ)) by unfold t; ring,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ)/2)]
    nlinarith only [mul_le_mul hjR hv.2 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 31)]
  have he : (j : ℝ)*v/2-(m : ℝ)*Real.pi = t+Real.pi/2 := by
    unfold t
    rw [rat_cast_num_div_den, hq]
    norm_num
    nlinarith only [congrArg (fun z : ℝ => Real.pi*z) hmR]
  rw [abs_sin_int_translate ((j : ℝ)*v/2) m, he, Real.sin_add_pi_div_two, ← Real.cos_abs t]
  have hpos : 0 ≤ Real.cos |t| := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith only [abs_nonneg t, Real.pi_pos], hcut.trans (by linarith [Real.pi_gt_d2])⟩
  rw [abs_of_nonneg hpos]
  exact cos_1085_lower.trans_le (Real.antitoneOn_cos ⟨abs_nonneg _, hcut.trans (by linarith [Real.pi_gt_d2])⟩
    ⟨by norm_num, by linarith [Real.pi_gt_d2]⟩ hcut)

end DurfeeCCS.Step08
