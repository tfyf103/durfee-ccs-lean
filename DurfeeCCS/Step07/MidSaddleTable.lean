module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import DurfeeCCS.Step06.SaddleComponents
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Endpoint arithmetic for the auxiliary-mode estimates on pages 36 and 38. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open Set

/-- The product whose maximum on each page 36 interval controls the imaginary correction. -/
def modeImagCorrection (t : ℝ) : ℝ := 2 * t * Real.exp (-t)

theorem hasDerivAt_modeImagCorrection (t : ℝ) :
    HasDerivAt modeImagCorrection (2 * Real.exp (-t) * (1 - t)) t := by
  have hd := ((hasDerivAt_id t).const_mul (2 : ℝ)).mul
    ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg)
  convert hd using 1
  · funext y
    rfl
  · simp only [Function.comp_apply, id_eq]
    ring

theorem modeImagCorrection_mono : MonotoneOn modeImagCorrection (Iic 1) := by
  let hd := hasDerivAt_modeImagCorrection
  apply monotoneOn_of_deriv_nonneg (convex_Iic 1)
  · exact fun t _ => (hd t).continuousAt.continuousWithinAt
  · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t).deriv]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (mem_Iic.mp (interior_subset ht)))

theorem modeImagCorrection_anti : AntitoneOn modeImagCorrection (Ici 1) := by
  let hd := hasDerivAt_modeImagCorrection
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · exact fun t _ => (hd t).continuousAt.continuousWithinAt
  · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (mem_Ici.mp (interior_subset ht)))

theorem modeImagCorrection_le_at_one (t : ℝ) :
    modeImagCorrection t ≤ modeImagCorrection 1 := by
  by_cases ht : t ≤ 1
  · exact modeImagCorrection_mono ht le_rfl ht
  · exact modeImagCorrection_anti le_rfl (le_of_not_ge ht) (le_of_not_ge ht)

/-- The five left endpoint lower bounds for a(exp t)² − t² in the page 36 calculation. -/
def modeLowerGap : Fin 5 → ℝ
  | 0 => 1.14437
  | 1 => 2.00209
  | 2 => 2.54405 ^ 2 - 4
  | 3 => 3.42798 ^ 2 - 9
  | 4 => 2.92097

/-- Right endpoint upper bounds for a(exp t) from the pages 30 and 34 tables. -/
def modeUpperAmplitude : Fin 5 → ℝ
  | 0 => 1.73266
  | 1 => 2.54406
  | 2 => 3.42799
  | 3 => 4.34983
  | 4 => 5.29407

/-- Rational upper bounds for the maxima of 2te⁻ᵗ on the five log intervals. -/
def modeUpperImag : Fin 5 → ℝ
  | 0 => 0.736
  | 1 => 0.736
  | 2 => 0.542
  | 3 => 0.299
  | 4 => 0.147

/-- Frequencies 3π/2 and 5π/2 bound the two classes of modes in the table. -/
def modeMultiplier (wide : Bool) : ℝ := if wide then 5 else 3

/-- The printed page 36 constants, indexed by the log interval and the frequency class. -/
def modeGapTarget (wide : Bool) (i : Fin 5) : ℝ :=
  if wide then
    match i with
    | 0 => 0.55
    | 1 => 0.64
    | 2 => 0.56
    | 3 => 0.45
    | 4 => 0.36
  else
    match i with
    | 0 => 0.44
    | 1 => 0.49
    | 2 => 0.39
    | 3 => 0.29
    | 4 => 0.21

theorem modeImagCorrection_bound (i : Fin 5) {t : ℝ}
    (ht : (i.val : ℝ) ≤ t) : modeImagCorrection t < modeUpperImag i := by
  fin_cases i
  · refine (modeImagCorrection_le_at_one t).trans_lt ?_
    change 2 * 1 * Real.exp (-1) < (0.736 : ℝ)
    dyadic_interval +kernel [prec := 40]
  · refine (modeImagCorrection_le_at_one t).trans_lt ?_
    change 2 * 1 * Real.exp (-1) < (0.736 : ℝ)
    dyadic_interval +kernel [prec := 40]
  · have hp : (2 : ℝ) ≤ t := ht
    refine (modeImagCorrection_anti (show (2 : ℝ) ∈ Ici 1 by norm_num) (by exact le_trans (by norm_num) hp) hp).trans_lt ?_
    change 2 * 2 * Real.exp (-2) < (0.542 : ℝ)
    dyadic_interval +kernel [prec := 40]
  · have hp : (3 : ℝ) ≤ t := ht
    refine (modeImagCorrection_anti (show (3 : ℝ) ∈ Ici 1 by norm_num) (by exact le_trans (by norm_num) hp) hp).trans_lt ?_
    change 2 * 3 * Real.exp (-3) < (0.299 : ℝ)
    dyadic_interval +kernel [prec := 40]
  · have hp : (4 : ℝ) ≤ t := ht
    refine (modeImagCorrection_anti (show (4 : ℝ) ∈ Ici 1 by norm_num) (by exact le_trans (by norm_num) hp) hp).trans_lt ?_
    change 2 * 4 * Real.exp (-4) < (0.147 : ℝ)
    dyadic_interval +kernel [prec := 40]

/-- A rational lower enclosure of the exact page 36 comparison at β*. -/
def modeRationalLower (wide : Bool) (i : Fin 5) : ℝ :=
  let m := modeMultiplier wide
  let pₗ : ℝ := 3.141592
  let pᵤ : ℝ := 3.141593
  (m ^ 2 - 1) * pₗ ^ 2 / 4 *
    (modeLowerGap i - modeUpperImag i / ((m + 1) * pₗ / 2)) /
    (modeUpperAmplitude i * (((i.val : ℝ) + 1) ^ 2 + (m ^ 2 / 4 + 1 / 3) * pᵤ ^ 2))

theorem mode_gap_rational_check (wide : Bool) (i : Fin 5) :
    modeGapTarget wide i < modeRationalLower wide i := by
  cases wide <;> fin_cases i <;> norm_num [modeGapTarget, modeRationalLower, modeMultiplier,
    modeLowerGap, modeUpperAmplitude, modeUpperImag]

/-- The rational check bounds the expression used in the page 36 table. -/
theorem mode_gap_endpoint_expression (wide : Bool) (i : Fin 5) :
    modeGapTarget wide i <
      let β := modeMultiplier wide * Real.pi / 2
      (β ^ 2 - Real.pi ^ 2 / 4) * (modeLowerGap i - modeUpperImag i / (β + Real.pi / 2)) /
        (modeUpperAmplitude i * (((i.val : ℝ) + 1) ^ 2 + β ^ 2 + Real.pi ^ 2 / 3)) := by
  have hpiₗ : (3.141592 : ℝ) ≤ Real.pi := Real.pi_gt_d6.le
  have hpiᵤ : Real.pi ≤ (3.141593 : ℝ) := Real.pi_lt_d6.le
  let m := modeMultiplier wide
  have hm : 3 ≤ m := by cases wide <;> norm_num [m, modeMultiplier]
  have hA : 0 < modeUpperAmplitude i := by fin_cases i <;> norm_num [modeUpperAmplitude]
  have hV : 0 ≤ modeUpperImag i := by fin_cases i <;> norm_num [modeUpperImag]
  have hfactor₁ : 0 ≤ m ^ 2 - 1 := by nlinarith
  have hfactor₂ : 0 ≤ modeLowerGap i - modeUpperImag i / ((m + 1) * (3.141592 : ℝ) / 2) := by
    cases wide <;> fin_cases i <;> norm_num [m, modeMultiplier, modeLowerGap, modeUpperImag]
  refine (mode_gap_rational_check wide i).trans_le ?_
  dsimp only [modeRationalLower]
  rw [show m * Real.pi / 2 + Real.pi / 2 = (m + 1) * Real.pi / 2 by ring,
    show (m * Real.pi / 2) ^ 2 - Real.pi ^ 2 / 4 = (m ^ 2 - 1) * Real.pi ^ 2 / 4 by ring,
    show ((i.val : ℝ) + 1) ^ 2 + (m * Real.pi / 2) ^ 2 + Real.pi ^ 2 / 3 =
      ((i.val : ℝ) + 1) ^ 2 + (m ^ 2 / 4 + 1 / 3) * Real.pi ^ 2 by ring]
  have hn :
      (m ^ 2 - 1) * (3.141592 : ℝ) ^ 2 / 4 *
        (modeLowerGap i - modeUpperImag i / ((m + 1) * (3.141592 : ℝ) / 2)) ≤
      (m ^ 2 - 1) * Real.pi ^ 2 / 4 *
        (modeLowerGap i - modeUpperImag i / ((m + 1) * Real.pi / 2)) := by gcongr
  apply div_le_div₀ (le_trans (by positivity) hn) hn (by positivity)
  · gcongr

/-- The two rational constants used for the opposite half of the main modes, page 38. -/
theorem oppositeHalf_first_endpoint_check :
    (0.32 : ℝ) < min (1.06975 ^ 2 / 2)
      (0.5 * Real.pi ^ 2 / (4 * (1 + 2 * 0.931 ^ 2))) / 1.377 := by
  have hp : (3.141592 : ℝ) ≤ Real.pi := Real.pi_gt_d6.le
  rw [lt_div_iff₀ (by norm_num), lt_min_iff]
  constructor
  · norm_num
  · apply lt_of_lt_of_le (show (0.32 : ℝ) * 1.377 <
        0.5 * (3.141592 : ℝ) ^ 2 / (4 * (1 + 2 * 0.931 ^ 2)) by norm_num)
    gcongr

theorem oppositeHalf_second_endpoint_check :
    (0.44 : ℝ) < min (1.37622 ^ 2 / 2)
      (0.731 * Real.pi ^ 2 / (4 * (1 + 2 * 0.812 ^ 2))) / 1.733 := by
  have hp : (3.141592 : ℝ) ≤ Real.pi := Real.pi_gt_d6.le
  rw [lt_div_iff₀ (by norm_num), lt_min_iff]
  constructor
  · norm_num
  · apply lt_of_lt_of_le (show (0.44 : ℝ) * 1.733 <
        0.731 * (3.141592 : ℝ) ^ 2 / (4 * (1 + 2 * 0.812 ^ 2)) by norm_num)
    gcongr

/-- For the second interval, the displayed value 0.731 is a lower bound
for r²/(1+r²) whenever 1/2 ≤ log r. -/
theorem oppositeHalf_second_ratios {r : ℝ} (hr : 0 < r) (ht : (1 / 2 : ℝ) ≤ Real.log r) :
    (0.731 : ℝ) ≤ r ^ 2 / (1 + r ^ 2) := by
  have hexp : Real.exp 1 = Real.exp (1 / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hr' : Real.exp (1 / 2) ≤ r := by
    simpa only [Real.exp_log hr] using Real.exp_le_exp.mpr ht
  have hsq : Real.exp 1 ≤ r ^ 2 := by
    rw [hexp]
    gcongr
  have hconst : (731 / 269 : ℝ) < Real.exp 1 := by
    have hlo : (2.718 : ℝ) < Real.exp 1 := by dyadic_interval +kernel [prec := 40]
    exact lt_trans (by norm_num) hlo
  rw [le_div_iff₀ (by positivity)]
  linarith [hconst.trans_le hsq]


/-- The page 38 estimate of the phase loss, using any endpoint enclosures
    valid throughout the chosen logarithm interval. -/
theorem oppositeHalf_phase_loss {a alo ahi ρ ρhi c clo z : ℝ}
    (halo : 0 < alo) (hal : alo ≤ a) (hah : a ≤ ahi)
    (hρ : 0 ≤ ρ) (hρh : ρ ≤ ρhi) (hc : 0 ≤ clo) (hcl : clo ≤ c) :
    min (alo ^ 2 / 2) (clo * Real.pi ^ 2 / (4 * (1 + 2 * ρhi ^ 2))) / ahi ≤
      (a ^ 2 * z ^ 2 + c * Real.pi ^ 2 / 4) / (a * (1 + 2 * ρ ^ 2 + 2 * z ^ 2)) := by
  let μ := min (alo ^ 2 / 2) (clo * Real.pi ^ 2 / (4 * (1 + 2 * ρhi ^ 2)))
  have hm : 0 ≤ μ := le_min (by positivity) (by positivity)
  have ha : 0 < a := halo.trans_le hal
  have hah' : 0 < ahi := ha.trans_le hah
  have hρsq : ρ ^ 2 ≤ ρhi ^ 2 := pow_le_pow_left₀ hρ hρh 2
  have hquad : μ * (2 * z ^ 2) ≤ a ^ 2 * z ^ 2 := by
    have hh : μ * 2 ≤ a ^ 2 := by
      have hm' : μ ≤ alo ^ 2 / 2 := min_le_left _ _
      linarith [pow_le_pow_left₀ halo.le hal 2]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (sq_nonneg z)
  have hc' : μ * (1 + 2 * ρ ^ 2) ≤ c * Real.pi ^ 2 / 4 := calc
    _ ≤ μ * (1 + 2 * ρhi ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hm
    _ ≤ clo * Real.pi ^ 2 / 4 := by
      have hμ : μ ≤ clo * Real.pi ^ 2 / (4 * (1 + 2 * ρhi ^ 2)) := min_le_right _ _
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
      nlinarith only [(le_div_iff₀ (by positivity : 0 < 4 * (1 + 2 * ρhi ^ 2))).1 hμ]
    _ ≤ _ := by gcongr
  change μ / ahi ≤ _
  rw [mul_comm a, ← div_div]
  calc
    _ ≤ μ / a := div_le_div_of_nonneg_left hm ha hah
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ ha.le
      exact (le_div_iff₀ (by positivity)).2 (by nlinarith only [hquad, hc'])

theorem oppositeHalf_first_phase_loss {a ρ c z : ℝ}
    (hal : 1.06975 ≤ a) (hah : a ≤ 1.377) (hρ : 0 ≤ ρ) (hρh : ρ ≤ 0.931) (hc : 0.5 ≤ c) :
    (0.32 : ℝ) <
      (a ^ 2 * z ^ 2 + c * Real.pi ^ 2 / 4) / (a * (1 + 2 * ρ ^ 2 + 2 * z ^ 2)) :=
  oppositeHalf_first_endpoint_check.trans_le
    (oppositeHalf_phase_loss (by norm_num) hal hah hρ hρh (by norm_num) hc)

theorem oppositeHalf_second_phase_loss {a ρ c z : ℝ}
    (hal : 1.37622 ≤ a) (hah : a ≤ 1.733) (hρ : 0 ≤ ρ) (hρh : ρ ≤ 0.812) (hc : 0.731 ≤ c) :
    (0.44 : ℝ) <
      (a ^ 2 * z ^ 2 + c * Real.pi ^ 2 / 4) / (a * (1 + 2 * ρ ^ 2 + 2 * z ^ 2)) :=
  oppositeHalf_second_endpoint_check.trans_le
    (oppositeHalf_phase_loss (by norm_num) hal hah hρ hρh (by norm_num) hc)

-- The monic quadratic introduced on page 35 from the real part of the principal square root.
def modePolynomial (t c v β x : ℝ) : ℝ :=
  x ^ 2 + (t ^ 2 + β ^ 2 - c) * x - t ^ 2 * c - β * t * v - v ^ 2 / 4

theorem modePolynomial_gap {t c v β x D : ℝ}
    (hx : modePolynomial t c v β x = 0)
    (hD : modePolynomial t c v (Real.pi / 2) D = 0)
    (hβ : Real.pi / 2 ≤ β) :
    (D - x) * (D + x + t ^ 2 + β ^ 2 - c) =
      (β ^ 2 - Real.pi ^ 2 / 4) * (D - t * v / (β + Real.pi / 2)) := by
  have hden : β + Real.pi / 2 ≠ 0 := by linarith [Real.pi_pos]
  have hprod : (β ^ 2 - Real.pi ^ 2 / 4) * (t * v / (β + Real.pi / 2)) =
      (β - Real.pi / 2) * t * v := by
    rw [show β ^ 2 - Real.pi ^ 2 / 4 =
      (β - Real.pi / 2) * (β + Real.pi / 2) by ring]
    calc
      _ = (β - Real.pi / 2) * ((t * v / (β + Real.pi / 2)) * (β + Real.pi / 2)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hden, mul_assoc]
  conv_rhs => rw [mul_sub, hprod]
  unfold modePolynomial at hx hD
  linear_combination hD - hx

theorem modePrefactor_mono_beta {t β β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hβ : β₀ ≤ β) :
    (β₀ ^ 2 - Real.pi ^ 2 / 4) / (t ^ 2 + β₀ ^ 2 + Real.pi ^ 2 / 3) ≤
      (β ^ 2 - Real.pi ^ 2 / 4) / (t ^ 2 + β ^ 2 + Real.pi ^ 2 / 3) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hh := mul_nonneg
    (sub_nonneg.mpr (pow_le_pow_left₀ hβ₀ hβ 2))
    (show 0 ≤ t ^ 2 + Real.pi ^ 2 / 3 + Real.pi ^ 2 / 4 by positivity)
  nlinarith only [hh]

/-- The certified page 36 lower bounds apply throughout the interval once the
    endpoint bounds and the two quadratic-root identities have been supplied. -/
theorem modeGap_at_parameters (wide : Bool) (i : Fin 5) {t a c v β x D : ℝ}
    (htₗ : (i.val : ℝ) ≤ t) (htᵤ : t ≤ (i.val : ℝ) + 1)
    (ha : 0 < a) (haᵤ : a ≤ modeUpperAmplitude i)
    (hc : c ≤ Real.pi ^ 2 / 3) (hv : 0 ≤ v) (hvᵤ : v ≤ 2 * Real.exp (-t))
    (hDₗ : modeLowerGap i ≤ D) (hDᵤ : D ≤ c) (hxₗ : 0 ≤ x) (hxᵤ : x ≤ c)
    (hβ : modeMultiplier wide * Real.pi / 2 ≤ β)
    (hx : modePolynomial t c v β x = 0)
    (hD : modePolynomial t c v (Real.pi / 2) D = 0) :
    modeGapTarget wide i < (D - x) / a := by
  let β₀ := modeMultiplier wide * Real.pi / 2
  let h : ℝ := (i.val : ℝ) + 1
  let p := Real.pi
  let b := t * v
  let W := modeLowerGap i - modeUpperImag i / (β₀ + p / 2)
  have ht : 0 ≤ t := (Nat.cast_nonneg _).trans htₗ
  have hm : 3 ≤ modeMultiplier wide := by cases wide <;> norm_num [modeMultiplier]
  have hβ₀ : 3 * p / 2 ≤ β₀ := by
    dsimp only [β₀, p]
    gcongr
  have hp : 0 < p := Real.pi_pos
  have hβ' : β₀ ≤ β := hβ
  have hβ₀pos : 0 < β₀ := by linarith
  have hβsq : (3 * p / 2) ^ 2 ≤ β ^ 2 :=
    pow_le_pow_left₀ (by dsimp [p]; positivity) (hβ₀.trans hβ) 2
  have htv : b ≤ modeUpperImag i := by
    have hh := mul_le_mul_of_nonneg_left hvᵤ ht
    have hh' : b ≤ modeImagCorrection t := by dsimp [b, modeImagCorrection]; linarith
    exact hh'.trans (modeImagCorrection_bound i htₗ).le
  have hW : 0 ≤ W := by
    let pₗ : ℝ := 3.141592
    have hWₗ : 0 ≤ modeLowerGap i -
        modeUpperImag i / (modeMultiplier wide * pₗ / 2 + pₗ / 2) := by
      cases wide <;> fin_cases i <;> norm_num [pₗ, modeMultiplier, modeLowerGap, modeUpperImag]
    refine hWₗ.trans ?_
    dsimp only [W, β₀, p]
    have hπ : pₗ ≤ Real.pi := Real.pi_gt_d6.le
    have hV : 0 ≤ modeUpperImag i := by fin_cases i <;> norm_num [modeUpperImag]
    gcongr
  have hWb : W ≤ D - b / (β + p / 2) := by
    dsimp only [W]
    have hb : 0 ≤ b := mul_nonneg ht hv
    apply sub_le_sub hDₗ
    apply div_le_div₀ (hb.trans htv) htv
    · dsimp [p]; positivity
    · linarith
  have hD₀ : 0 ≤ D := by
    have hoo : 0 ≤ modeLowerGap i := by fin_cases i <;> norm_num [modeLowerGap]
    exact hoo.trans hDₗ
  let d := D + x + t ^ 2 + β ^ 2 - c
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [sq_nonneg t, sq_pos_of_pos Real.pi_pos]
  have hd' : d ≤ t ^ 2 + β ^ 2 + p ^ 2 / 3 := by dsimp [d, p]; linarith
  have hF : (β₀ ^ 2 - p ^ 2 / 4) / (h ^ 2 + β₀ ^ 2 + p ^ 2 / 3) ≤
      (β ^ 2 - p ^ 2 / 4) / d := calc
    _ ≤ (β ^ 2 - p ^ 2 / 4) / (h ^ 2 + β ^ 2 + p ^ 2 / 3) :=
      modePrefactor_mono_beta hβ₀pos.le hβ
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by nlinarith [sq_nonneg p]) hd
      exact hd'.trans (by gcongr)
  have hF₀ : 0 ≤ (β₀ ^ 2 - p ^ 2 / 4) / (h ^ 2 + β₀ ^ 2 + p ^ 2 / 3) := by
    have hsq : (3 * p / 2) ^ 2 ≤ β₀ ^ 2 :=
      pow_le_pow_left₀ (by dsimp [p]; positivity) hβ₀ 2
    exact div_nonneg (by nlinarith [sq_nonneg p]) (by dsimp [p]; positivity)
  have hprod := mul_le_mul hF hWb hW (hF₀.trans hF)
  have hgap := modePolynomial_gap hx hD (by linarith)
  have hgap' : (β ^ 2 - p ^ 2 / 4) / d * (D - b / (β + p / 2)) = D - x := by
    have hgap'' : (D - x) * d = (β ^ 2 - p ^ 2 / 4) * (D - b / (β + p / 2)) := hgap
    rw [div_mul_eq_mul_div, ← hgap'', mul_div_cancel_right₀ _ hd.ne']
  have hupper : 0 < modeUpperAmplitude i := ha.trans_le haᵤ
  calc
    _ < (β₀ ^ 2 - p ^ 2 / 4) * W /
      (modeUpperAmplitude i * (h ^ 2 + β₀ ^ 2 + p ^ 2 / 3)) :=
      mode_gap_endpoint_expression wide i
    _ = ((β₀ ^ 2 - p ^ 2 / 4) / (h ^ 2 + β₀ ^ 2 + p ^ 2 / 3) * W) /
        modeUpperAmplitude i := by
      rw [mul_comm (modeUpperAmplitude i), ← div_div, div_mul_eq_mul_div]
    _ ≤ ((β₀ ^ 2 - p ^ 2 / 4) / (h ^ 2 + β₀ ^ 2 + p ^ 2 / 3) * W) / a :=
      div_le_div_of_nonneg_left (mul_nonneg hF₀ hW) ha haᵤ
    _ ≤ _ := div_le_div_of_nonneg_right (hgap' ▸ hprod) ha.le

end DurfeeCCS.Step07
