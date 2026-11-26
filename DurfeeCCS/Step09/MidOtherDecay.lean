module

public import DurfeeCCS.Step07.ThetaBoundsTail
public import DurfeeCCS.Step07.ThetaFiniteGaussian
public import DurfeeCCS.Step07.MidSaddleTableConnections

meta import DurfeeCCS.Step07.ThetaBoundsIntervals
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The uniform scalar exponential estimates of Lemma 3.10. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Real Set DurfeeCCS.Step06 DurfeeCCS.Step07

theorem midOther_sqrt_decay_le {x a A c : ℝ} (hx : 80 ≤ x) (ha : 0 ≤ a) (hA : a ≤ A)
    (hc : 0 ≤ c) (hturn : (1 / 2 : ℝ) ≤ c * 80) :
    √(a*x) * exp (-c*x) ≤ √(80*A) * exp (-80*c) := by
  have hA' := ha.trans hA
  calc
    _ = √a * (√x * exp (-c*x)) := by rw [sqrt_mul ha, mul_assoc]
    _ ≤ √A * (√80 * exp (-c*80)) := by
      refine mul_le_mul (sqrt_le_sqrt hA) ?_ (by positivity) (by positivity)
      exact sqrt_mul_exp_antitoneOn (by norm_num) hc hturn le_rfl hx hx
    _ = _ := by rw [← mul_assoc, ← sqrt_mul hA']; congr 2 <;> ring

theorem midOther_far_budget_lt {y : ℝ} (hy : 80 ≤ y) :
    6 * 109000 * √y * exp (-4*y) < 0.000001 := by
  have h := sqrt_mul_exp_antitoneOn (by norm_num : (0 : ℝ) ≤ 80)
    (by norm_num : (0 : ℝ) ≤ 4) (by norm_num) le_rfl hy hy
  have hb : (6 * 109000 : ℝ) * √80 * exp (-4*80) < 0.000001 := by
    dyadic_interval +kernel [prec := 60]
  calc
    _ = (6 * 109000) * (√y * exp (-4*y)) := by ring
    _ ≤ (6 * 109000) * (√80 * exp (-4*80)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ < _ := by convert hb using 1 <;> ring

theorem midOther_small_near_budget_lt {x a : ℝ} (hx : 80 ≤ x) (ha : 0 ≤ a) (ha' : a ≤ 1.733) :
    109000 * √(a*x) * (26*a + 2) * exp (-0.44*x) < 0.000001 := by
  have h := midOther_sqrt_decay_le hx ha ha' (c := 0.44) (by norm_num) (by norm_num)
  have hb : (109000 : ℝ) * (26*1.733+2) * (√(80*1.733) * exp (-80*0.44)) < 0.000001 := by
    dyadic_interval +kernel [prec := 55]
  calc
    _ = 109000 * (26*a+2) * (√(a*x) * exp (-0.44*x)) := by ring
    _ ≤ 109000 * (26*1.733+2) * (√(80*1.733) * exp (-80*0.44)) := by
      refine mul_le_mul (by linarith only [ha']) h (by positivity) (by positivity)
    _ < _ := hb

theorem midOther_intermediate_near_budget_lt {x a : ℝ} (hx : 80 ≤ x)
    (ha : 0 ≤ a) (ha' : a ≤ 5.295) :
    110 * √(a*x) * (2 * exp (-0.21*x) + (26*a+2) * exp (-0.36*x)) < 0.00023 := by
  have h₁ := midOther_sqrt_decay_le hx ha ha' (c := 0.21) (by norm_num) (by norm_num)
  have h₂ := midOther_sqrt_decay_le hx ha ha' (c := 0.36) (by norm_num) (by norm_num)
  have h₂' := mul_le_mul (show 26*a+2 ≤ (140 : ℝ) by linarith only [ha']) h₂
    (by positivity) (by norm_num)
  have hg := add_le_add (mul_le_mul_of_nonneg_left h₁ (show (0 : ℝ) ≤ 2 by norm_num)) h₂'
  have h := mul_le_mul_of_nonneg_left hg (show (0 : ℝ) ≤ 110 by norm_num)
  have hb : (110 : ℝ) * (2 * (√(80*5.295) * exp (-80*0.21)) +
      140 * (√(80*5.295) * exp (-80*0.36))) < 0.00023 := by
    dyadic_interval +kernel [prec := 50]
  exact (by convert h using 1 <;> ring : _ ≤ _).trans_lt hb

theorem midOther_small_opposite_core_budget_lt {x a : ℝ} (hx : 80 ≤ x)
    (ha : 0 ≤ a) (ha' : a ≤ 1.733) :
    109000 * (√(a*x) * exp (-(0.733 / 1.733)*x)) < 0.000001 := by
  have h := midOther_sqrt_decay_le hx ha ha' (c := 0.733 / 1.733) (by norm_num) (by norm_num)
  have hb : (109000 : ℝ) * (√(80*1.733) * exp (-80*(0.733/1.733))) < 0.000001 := by
    dyadic_interval +kernel [prec := 55]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_lt hb

theorem midOther_small_opposite_first_budget_lt {x a : ℝ} (hx : 80 ≤ x)
    (ha : 0 ≤ a) (ha' : a ≤ 1.377) :
    109000 * (√(a*x) * exp (-0.32*x)) < 0.00001 := by
  have h := midOther_sqrt_decay_le hx ha ha' (c := 0.32) (by norm_num) (by norm_num)
  have hb : (109000 : ℝ) * (√(80*1.377) * exp (-80*0.32)) < 0.00001 := by
    dyadic_interval +kernel [prec := 55]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_lt hb

theorem midOther_small_opposite_second_budget_lt {x a : ℝ} (hx : 80 ≤ x)
    (ha : 0 ≤ a) (ha' : a ≤ 1.733) :
    109000 * (√(a*x) * exp (-0.44*x)) < 0.000001 := by
  have h := midOther_sqrt_decay_le hx ha ha' (c := 0.44) (by norm_num) (by norm_num)
  have hb : (109000 : ℝ) * (√(80*1.733) * exp (-80*0.44)) < 0.000001 := by
    dyadic_interval +kernel [prec := 55]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_lt hb

private theorem midOther_log_eighty_lower : 3 < log (80 : ℝ) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  dyadic_interval +kernel [prec := 35]

private theorem midOther_log_eighty_upper : log (80 : ℝ) < 4.3821 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  dyadic_interval +kernel [prec := 40]

def midOtherScale (x : ℝ) : ℝ := √(√(x / 80))

theorem midOtherScale_growth {x : ℝ} (hx : 80 ≤ x) :
    let z := midOtherScale x
    1 ≤ z ∧ x = 80*z^4 ∧ log x+1 ≤ 5.3821*z ∧ theta38Growth x ≤ 5.681*z := by
  let z := midOtherScale x
  have hX : 1 ≤ x / 80 := by linarith
  have hZ : 1 ≤ z := by
    unfold z midOtherScale
    have hY : 1 ≤ √(x/80) := le_sqrt_of_sq_le (by simpa using hX)
    exact le_sqrt_of_sq_le (by simpa using hY)
  have hZ0 : 0 < z := by linarith
  have hXz : x = 80*z^4 := by
    have hh : z ^ 2 = √(x/80) := sq_sqrt (sqrt_nonneg _)
    rw [show z ^ 4 = (z^2)^2 by ring, hh, sq_sqrt (by positivity)]
    ring
  have hlog : log x + 1 = log 80 + 1 + 4 * log z := by
    rw [hXz, Real.log_mul (by norm_num) (pow_ne_zero _ hZ0.ne'), Real.log_pow]
    norm_num
    ring
  have ht : log x + 1 ≤ 5.3821*z := by
    rw [hlog]
    have h₁ := log_le_sub_one_of_pos hZ0
    linarith only [h₁, midOther_log_eighty_upper, hZ]
  have ht0 : 0 ≤ log x + 1 := by linarith [Real.log_nonneg (show 1 ≤ x by linarith)]
  have hZ2 : 1 ≤ z^2 := by nlinarith only [hZ, sq_nonneg (z-1)]
  refine ⟨hZ,hXz,ht,?_⟩
  unfold theta38Growth
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hSq := pow_le_pow_left₀ ht0 ht 2
  nlinarith only [hSq,hZ2,
    mul_nonneg (show 0 ≤ (5.681 : ℝ)^2 - 5.3821^2 - 3.3 by norm_num) (sq_nonneg z)]

private theorem midOtherScale_exp_decay {c z : ℝ} (hc : 4 ≤ c) (hz : 1 ≤ z) :
    z ^ 4 * exp (-c*z) ≤ exp (-c) := by
  have h := power_mul_exp_antitoneOn (x₀ := 1) (a := c) (b := 0) 4 1
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by simpa using hc)
  simpa using h (show (1 : ℝ) ∈ Ici 1 from le_rfl) hz hz

private theorem midOtherScale_prefactor {x a : ℝ} (hx : 80 ≤ x) (ha : 0 ≤ a)
    (hau : a ≤ theta38Growth x) :
    √(a*x) ≤ √(80*5.681) * midOtherScale x ^ 3 := by
  let z := midOtherScale x
  obtain ⟨hz,hX,_,hA⟩ := midOtherScale_growth hx
  have hZ : 0 ≤ z := by linarith
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, sq_sqrt (by norm_num : 0 ≤ (80*5.681 : ℝ))]
  calc
    _ ≤ (5.681*z)*x := mul_le_mul_of_nonneg_right (hau.trans hA) (by positivity)
    _ = (80*5.681)*z^5 := by rw [hX]; ring
    _ ≤ (80*5.681)*((z^3)^2) := by
      rw [← pow_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact pow_le_pow_right₀ hz (by decide : 5 ≤ 3*2)

theorem midOther_large_opposite_budget_lt {x a : ℝ} (hx : 80 ≤ x) (ha : 0 < a)
    (hA : a ≤ theta38Growth x) :
    110 * (√(a*x) * exp (-(1.245*x/a))) < 0.00006 := by
  let z := midOtherScale x
  let C : ℝ := 1.245 * 80 / 5.681
  obtain ⟨hz,hX,_,hA'⟩ := midOtherScale_growth hx
  change 1 ≤ z at hz
  change x = 80 * z^4 at hX
  have hZ : 0 ≤ z := by linarith
  have hC : 4 ≤ C := by norm_num [C]
  have ho : C*z ≤ 1.245*x/a := by
    apply (le_div_iff₀ ha).mpr
    calc
      _ ≤ C*z*(5.681*z) := mul_le_mul_of_nonneg_left (hA.trans hA') (by positivity)
      _ = 1.245*80*z^2 := by unfold C; ring
      _ ≤ 1.245*80*z^4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by decide : 2 ≤ 4)) (by norm_num)
      _ = _ := by rw [hX]; ring
  have hE : exp (-(1.245*x/a)) ≤ exp (-C*z) := Real.exp_le_exp.mpr (by linarith only [ho])
  have hP := midOtherScale_prefactor hx ha.le hA
  have hpow : z^3 ≤ z^4 := pow_le_pow_right₀ hz (by decide)
  have hk := midOtherScale_exp_decay hC hz
  have hbase : (110 : ℝ) * (√(80*5.681) * exp (-C)) < 0.00006 := by
    unfold C
    dyadic_interval +kernel [prec := 55]
  apply lt_of_le_of_lt _ hbase
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ (√(80*5.681)*z^4)*exp (-C*z) :=
      mul_le_mul (hP.trans (mul_le_mul_of_nonneg_left hpow (by positivity))) hE
        (by positivity) (by positivity)
    _ = √(80*5.681)*(z^4*exp (-C*z)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (by positivity)

theorem midOther_large_near_budget_lt {x a t : ℝ} (hx : 80 ≤ x) (ha : 0 < a)
    (hA : a ≤ theta38Growth x) (ht : 0 ≤ t) (htx : t ≤ log x + 1) :
    let δ₁ := 59.5 * x / (a * (t^2 + 25.5))
    let δ₂ := 178 * x / (a * (t^2 + 65))
    110 * √(a*x) * (2 * exp (-δ₁) + (26*a+2) * exp (-δ₂)) < 0.00098 := by
  let z := midOtherScale x
  let δ₁ := 59.5 * x / (a * (t^2 + 25.5))
  let δ₂ := 178 * x / (a * (t^2 + 65))
  let C₁ : ℝ := 59.5*80/(5.681*(5.3821^2+25.5))
  let C₂ : ℝ := 178*80/(5.681*(5.3821^2+65))
  obtain ⟨hz,hX,ht',hA'⟩ := midOtherScale_growth hx
  change 1 ≤ z at hz
  change x = 80*z^4 at hX
  change log x + 1 ≤ 5.3821*z at ht'
  have hAZ : a ≤ 5.681*z := hA.trans hA'
  have hZ : 0 ≤ z := by linarith
  have hc' (b d : ℝ) (hb : 0 ≤ b) (hd : 0 < d) :
      (b*80/(5.681*(5.3821^2+d)))*z ≤ b*x/(a*(t^2+d)) := by
    have ht2 := pow_le_pow_left₀ ht (htx.trans ht') 2
    have hz2 := pow_le_pow_right₀ hz (show (0 : ℕ) ≤ 2 by decide)
    have htd : t^2+d ≤ (5.3821^2+d)*z^2 := by
      simp only [pow_zero] at hz2
      nlinarith only [ht2, mul_le_mul_of_nonneg_left hz2 hd.le]
    have hD := mul_le_mul hAZ htd (show 0 ≤ t^2+d by positivity) (by positivity : 0 ≤ 5.681*z)
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (b*80/(5.681*(5.3821^2+d)))*z*((5.681*z)*((5.3821^2+d)*z^2)) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := by rw [hX]; field_simp
  have hδ₁ : C₁*z ≤ δ₁ := hc' 59.5 25.5 (by norm_num) (by norm_num)
  have hδ₂ : C₂*z ≤ δ₂ := hc' 178 65 (by norm_num) (by norm_num)
  have hE₁ : exp (-δ₁) ≤ exp (-C₁*z) := exp_le_exp.mpr (by linarith)
  have hE₂ : exp (-δ₂) ≤ exp (-C₂*z) := exp_le_exp.mpr (by linarith)
  have hP := midOtherScale_prefactor hx ha.le hA
  change √(a*x) ≤ √(80*5.681)*z^3 at hP
  have hP' : √(a*x) ≤ √(80*5.681)*z^4 :=
    hP.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by decide)) (by positivity))
  have hCo : 26*a+2 ≤ (26*5.681+2)*z := by linarith only [hAZ,hz]
  have hD₁ : 4 ≤ C₁ := by norm_num [C₁]
  have hD₂ : 4 ≤ C₂ := by norm_num [C₂]
  have h₁ : √(a*x)*exp (-δ₁) ≤ √(80*5.681)*exp (-C₁) := by
    calc
      _ ≤ (√(80*5.681)*z^4)*exp (-C₁*z) :=
        mul_le_mul hP' hE₁ (by positivity) (by positivity)
      _ = √(80*5.681)*(z^4*exp (-C₁*z)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (midOtherScale_exp_decay hD₁ hz) (by positivity)
  have h₂ : √(a*x)*(26*a+2)*exp (-δ₂) ≤
      √(80*5.681)*(26*5.681+2)*exp (-C₂) := by
    calc
      _ ≤ ((√(80*5.681)*z^3)*((26*5.681+2)*z))*exp (-C₂*z) := by
        exact mul_le_mul (mul_le_mul hP hCo (by positivity) (by positivity)) hE₂ (by positivity) (by positivity)
      _ = (√(80*5.681)*(26*5.681+2))*(z^4*exp (-C₂*z)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (midOtherScale_exp_decay hD₂ hz) (by positivity)
  have H : 110*(2*(√(a*x)*exp (-δ₁)) + √(a*x)*(26*a+2)*exp (-δ₂)) ≤
      110*(2*(√(80*5.681)*exp (-C₁)) + √(80*5.681)*(26*5.681+2)*exp (-C₂)) :=
    mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num)) h₂) (by norm_num)
  have hb : 110*(2*(√(80*5.681)*exp (-C₁)) + √(80*5.681)*(26*5.681+2)*exp (-C₂)) < 0.00098 := by
    unfold C₁ C₂
    dyadic_interval +kernel [prec := 55]
  exact (by convert H using 1 <;> ring : _ ≤ _).trans_lt hb

end DurfeeCCS.Step09
