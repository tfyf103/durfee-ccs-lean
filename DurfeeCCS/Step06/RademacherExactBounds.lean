module

public import DurfeeCCS.Step06.RademacherExactModular
public import DurfeeCCS.Step06.RademacherExactPolar
import DurfeeCCS.Step09.MidPoissonEuler
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-! A horizontal coefficient contour and its effective estimates for the first Bessel term. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step06

open Complex Set MeasureTheory
open DurfeeCCS.Step08 DurfeeCCS.Step09

/-- A Fourier coefficient integrand for the inverse eta-square product on a horizontal line. -/
def twoColourCoefficientIntegrand (n : ℕ) (ρ x : ℝ) : ℂ :=
  let ζ := (2 * (Real.pi : ℂ)) * ((ρ : ℂ) - (x : ℂ) * I)
  exp ((n : ℂ) * ζ) * twoColourGenerating (exp (-ζ))

private theorem exp_neg_pi_lt_eighth : Real.exp (-Real.pi) < 1 / 8 := by
  rw [Real.exp_neg, ← one_div]
  apply one_div_lt_one_div_of_lt (by norm_num)
  have h := Real.exp_lt_exp.mpr Real.pi_gt_three
  rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul] at h
  have hx := pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (3 : ℕ) ≠ 0)
  rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num]
  exact hx.trans h

private theorem norm_twoColourGenerating_exp_le {ζ : ℂ} (hζ : Real.pi ≤ ζ.re) :
    ‖twoColourGenerating (exp (-ζ))‖ ≤ 3 / 2 := by
  have hz : 0 < ζ.re := Real.pi_pos.trans_le hζ
  have hq : Real.exp (-ζ.re) ≤ 1 / 8 :=
    (Real.exp_le_exp.mpr (neg_le_neg hζ)).trans exp_neg_pi_lt_eighth.le
  have hd : (7 : ℝ) / 8 ≤ 1 - Real.exp (-ζ.re) := by linarith
  have ha : ‖eulerProductLog ζ‖ ≤ 8 / 49 := calc
    _ ≤ Real.exp (-ζ.re) / (1 - Real.exp (-ζ.re)) ^ 2 := norm_eulerProductLog_le hz
    _ ≤ (1 / 8) / (7 / 8)^2 := by
      apply div_le_div₀ (by positivity) hq (by norm_num)
      exact pow_le_pow_left₀ (by norm_num) hd 2
    _ = _ := by norm_num
  rw [twoColourGenerating_exp_neg, ← exp_eulerProductLog_eq hz, ← Complex.exp_neg,
    ← Complex.exp_nat_mul, Complex.norm_exp]
  have he : ((2 : ℕ) * -eulerProductLog ζ).re ≤ 16 / 49 := by
    have h := Complex.re_le_norm (-eulerProductLog ζ)
    simp only [Complex.neg_re, norm_neg] at h
    rw [show ((2 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, zero_mul, sub_zero]
    linarith
  calc
    _ ≤ Real.exp (16 / 49) := Real.exp_le_exp.mpr he
    _ ≤ 1 / (1 - (16 / 49 : ℝ)) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    _ ≤ _ := by norm_num

/-- All transformed cusp parameters with modulus at most `exp (-π)` have uniformly small
two-colour Euler products and nonconstant parts. -/
theorem norm_twoColourGenerating_small_disc {q : ℂ} (hq : ‖q‖ ≤ Real.exp (-Real.pi)) :
    ‖twoColourGenerating q‖ ≤ 3 / 2 ∧ ‖twoColourGenerating q - 1‖ ≤ 1 / 2 := by
  let r := Real.exp (-Real.pi)
  have hr : 0 < r := Real.exp_pos _
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos)
  have hC : ‖twoColourGenerating (r : ℂ)‖ ≤ 3 / 2 := by
    have hz := norm_twoColourGenerating_exp_le
      (ζ := (Real.pi : ℂ)) (by simp)
    simpa only [r, Complex.ofReal_exp, Complex.ofReal_neg] using hz
  have hS : ‖twoColourGenerating q - 1‖ ≤ 1 / 2 := by
    refine (norm_twoColourGenerating_sub_one_le hr hr' hq).trans ?_
    calc
      _ ≤ (‖q‖ / r) * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [Complex.re_le_norm (twoColourGenerating (r : ℂ))]
      _ ≤ _ := by nlinarith [(div_le_one hr).mpr hq]
  have ht := norm_add_le (twoColourGenerating q - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at ht
  exact ⟨by linarith, hS⟩

/-- Every point outside the principal arc in a unit interval centered at zero admits a
reduced approximation of denominator at least two within the needed Dirichlet width. -/
theorem exists_rademacher_minor_approximation {δ x : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 5) (hx : δ ≤ |x|) (hx' : |x| ≤ 1 / 2) :
    ∃ (h : ℤ) (k : ℕ), 2 ≤ k ∧ Int.gcd h k = 1 ∧ (k : ℝ) ≤ 1 / δ ∧
      |x - (h : ℝ) / k| ≤ δ / k := by
  let N := ⌊1 / δ⌋₊
  have hNd : (N : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
  have hN' : 1 / δ < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hN : 0 < N := by
    by_contra! he
    have hh : (N : ℝ) = 0 := by exact_mod_cast Nat.eq_zero_of_le_zero he
    rw [hh, zero_add, div_lt_one hδ] at hN'
    linarith
  obtain ⟨q, hq, hqN⟩ := Real.exists_rat_abs_sub_le_and_den_le x hN
  have hd : (0 : ℝ) < q.den := by exact_mod_cast Rat.pos q
  have hbound : |x - (q : ℝ)| < δ / q.den := by
    refine hq.trans_lt ?_
    rw [← div_div]
    apply div_lt_div_of_pos_right _ hd
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have hh := (div_lt_iff₀ hδ).mp hN'
    linarith
  have hk : 2 ≤ q.den := by
    by_contra! hk
    have hd₁ : q.den = 1 := by have := Rat.pos q; omega
    rw [hd₁, Nat.cast_one, div_one] at hbound
    have hr : (q : ℝ) = (q.num : ℝ) := by rw [Rat.cast_def, hd₁, Nat.cast_one, div_one]
    have hnum : |(q.num : ℝ)| < 1 := calc
      _ = |(q : ℝ)| := by rw [hr]
      _ = |(x - (q : ℝ)) + (-x)| := by rw [show x - (q : ℝ) + (-x) = -(q : ℝ) by ring, abs_neg]
      _ ≤ |x - (q : ℝ)| + |-x| := abs_add_le _ _
      _ < _ := by rw [abs_neg]; linarith
    have hnum₀ : q.num = 0 := by
      rw [abs_lt] at hnum
      obtain ⟨hl, hh⟩ := hnum
      have hl' : (-1 : ℤ) < q.num := by exact_mod_cast hl
      have hh' : q.num < (1 : ℤ) := by exact_mod_cast hh
      omega
    have hr' : (q : ℝ) = 0 := by rw [hr, hnum₀, Int.cast_zero]
    rw [hr', sub_zero] at hbound
    exact not_lt_of_ge hx hbound
  refine ⟨q.num, q.den, hk, ?_, ?_, ?_⟩
  · simpa only [Int.gcd_eq_natAbs, Int.natAbs_natCast] using q.reduced.gcd_eq_one
  · exact (by exact_mod_cast hqN : (q.den : ℝ) ≤ N).trans hNd
  · exact (by rw [← Rat.cast_def]; exact hbound.le)

private theorem real_part_circle_point (ρ x : ℝ) :
    ((ρ : ℂ) - (x : ℂ) * I).re = ρ := by simp [mul_re]

private theorem circle_point_eq_vertical (ρ x : ℝ) :
    (ρ : ℂ) - (x : ℂ) * I = verticalPoint ρ (-x) := by simp [verticalPoint, sub_eq_add_neg]

private theorem real_part_angular_exp (t : ℝ) (w : ℂ) :
    ((t : ℂ) * w).re = t * w.re := by simp [mul_re]

/-- The coefficient extraction on the unit-width version of the angular contour. -/
theorem twoColourPartitionCount_eq_horizontal_integral (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (twoColourPartitionCount n : ℂ) =
      ∫ x : ℝ in -(1 / 2)..(1 / 2), twoColourCoefficientIntegrand n ρ x := by
  let u := 2 * Real.pi * ρ
  let f := fun v : ℝ => exp ((n : ℂ) * ((u : ℂ) + v * I)) *
    (eulerProduct ((u : ℂ) + v * I))⁻¹ ^ 2
  have h₀ : 0 < 2 * Real.pi := by positivity
  have hu : 0 < u := mul_pos h₀ hρ
  have hpos : -(2 * Real.pi) ≠ 0 := neg_ne_zero.mpr h₀.ne'
  have hfun (x : ℝ) : twoColourCoefficientIntegrand n ρ x = f (-(2 * Real.pi) * x) := by
    unfold twoColourCoefficientIntegrand f
    dsimp only
    rw [twoColourGenerating_exp_neg]
    have he : (2 * (Real.pi : ℂ)) * ((ρ : ℂ) - (x : ℂ) * I) =
        (u : ℂ) + (↑(-(2 * Real.pi) * x : ℝ) : ℂ) * I := by dsimp [u]; push_cast; ring
    rw [he]
  change _ = (∫ x : ℝ in -(1 / 2)..(1 / 2), twoColourCoefficientIntegrand n ρ x)
  rw [twoColourPartitionCount_eq_angular_integral n hu]
  simp_rw [hfun]
  rw [intervalIntegral.integral_comp_mul_left f hpos]
  norm_num only [show -(2 * Real.pi) * -(1 / 2) = Real.pi by ring,
    show -(2 * Real.pi) * (1 / 2) = -Real.pi by ring, Complex.real_smul, inv_neg, Complex.ofReal_neg,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [show (∫ v in Real.pi..-Real.pi, f v) = -(∫ v in -Real.pi..Real.pi, f v) from
    intervalIntegral.integral_symm (f := f) (-Real.pi) Real.pi]
  change (2 * (Real.pi : ℂ))⁻¹ * (∫ v in -Real.pi..Real.pi, f v) =
    -((2 * (Real.pi : ℂ))⁻¹) * (-(∫ v in -Real.pi..Real.pi, f v))
  ring

/-- Continuity of the horizontal coefficient integrand. -/
theorem continuous_twoColourCoefficientIntegrand (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (twoColourCoefficientIntegrand n ρ) := by
  let ζ := fun x : ℝ => (2 * (Real.pi : ℂ)) * ((ρ : ℂ) - (x : ℂ) * I)
  have hζ : Continuous ζ := by dsimp [ζ]; fun_prop
  have hpos (x : ℝ) : 0 < (ζ x).re := by
    have he : ζ x = (((2 * Real.pi : ℝ) : ℂ) * ((ρ : ℂ) - (x : ℂ) * I)) := by simp [ζ]
    rw [he, real_part_angular_exp, real_part_circle_point]
    positivity
  have hE : Continuous (fun x : ℝ => eulerProduct (ζ x)) :=
    continuousOn_univ.mp (continuousOn_eulerProduct_right.comp hζ.continuousOn
      (fun x _ => hpos x))
  have hG : Continuous (fun x : ℝ => (eulerProduct (ζ x))⁻¹ ^ 2) := by
    refine (hE.inv₀ (fun x => ?_)).pow 2
    rw [← exp_eulerProductLog_eq (hpos x)]
    exact Complex.exp_ne_zero _
  have hFun : twoColourCoefficientIntegrand n ρ =
      fun x : ℝ => exp ((n : ℂ) * ζ x) * (eulerProduct (ζ x))⁻¹ ^ 2 := by
    funext x
    simp only [twoColourCoefficientIntegrand, ζ, twoColourGenerating_exp_neg]
  rw [hFun]
  exact (Complex.continuous_exp.comp (continuous_const.mul hζ)).mul hG

/-- A pointwise bound outside the zero cusp. The approximation is needed only to bound
the absolute value of the transformed product. -/
theorem norm_twoColourCoefficientIntegrand_minor_le (n : ℕ) {ρ x : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 25)
    (hx : Real.sqrt ρ ≤ |x|) (hx' : |x| ≤ 1 / 2) :
    ‖twoColourCoefficientIntegrand n ρ x‖ ≤
      (9 / 4) * Real.sqrt ρ * Real.exp (2 * Real.pi * n * ρ + Real.pi / (24 * ρ)) := by
  let δ := Real.sqrt ρ
  have hδ : 0 < δ := Real.sqrt_pos.mpr hρ
  have hδsq : δ ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hδ' : δ ≤ 1 / 5 := by nlinarith [sq_nonneg (δ - 1 / 5)]
  obtain ⟨h,k,hk,hg,hkδ,hxδ⟩ := exists_rademacher_minor_approximation hδ hδ' hx hx'
  have hk₁ : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk₁
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk₁.ne'
  have hk₂ : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hreal : (k : ℝ) ^ 2 * ρ ≤ (k : ℝ) * δ := by
    have hK : (k : ℝ) * δ ≤ 1 := (le_div_iff₀ hδ).mp hkδ
    rw [← hδsq, show (k : ℝ)^2 * δ^2 = ((k : ℝ) * δ) * ((k : ℝ) * δ) by ring]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ (k : ℝ) * δ)
  let a := (k : ℝ)^2 * ρ
  let b := -(k : ℝ)^2 * (x - (h : ℝ) / k)
  let z := verticalPoint a b
  have ha : 0 < a := by positivity
  have hb : |b| ≤ (k : ℝ) * δ := by
    dsimp [b]
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (k : ℝ))]
    calc
      _ ≤ (k : ℝ)^2 * (δ / k) := mul_le_mul_of_nonneg_left hxδ (sq_nonneg _)
      _ = _ := by field_simp
  have hzb : ‖z‖ ^ 2 ≤ 2 * a := by
    dsimp only [z]
    rw [norm_verticalPoint_sq]
    have hsa := pow_le_pow_left₀ ha.le hreal 2
    have hsb := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hsb
    have hrhs : ((k : ℝ) * δ)^2 = a := by rw [mul_pow, hδsq]
    rw [hrhs] at hsa hsb
    linarith
  have hza : a^2 ≤ ‖z‖ ^ 2 := by dsimp only [z]; rw [norm_verticalPoint_sq]; exact le_add_of_nonneg_right (sq_nonneg _)
  have hz₀ : z ≠ 0 := verticalPoint_ne_zero ha _
  have hzq : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz₀
  have hc : (z⁻¹).re = a / ‖z‖ ^ 2 := by
    rw [Complex.inv_re, ← Complex.sq_norm, show z.re = a from verticalPoint_re _ _]
  have hcl : 1 / 2 ≤ (z⁻¹).re := by
    rw [hc, le_div_iff₀ (by positivity)]
    linarith
  have hch : (z⁻¹).re ≤ 1 / (4 * ρ) := by
    have hka : 4 * ρ ≤ a := by
      dsimp [a]
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ((k : ℝ)-2)]) hρ.le
    calc
      _ = a / ‖z‖ ^ 2 := hc
      _ ≤ a / a^2 := div_le_div_of_nonneg_left ha.le (by positivity) hza
      _ = 1 / a := by field_simp
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) hka
  have hnz : ‖z‖ / (k : ℝ) ≤ (3 / 2) * δ := by
    rw [div_le_iff₀ hkR]
    have haux : 2 * a ≤ ((3 / 2) * δ * (k : ℝ))^2 := by
      dsimp [a]
      rw [show ((3 / 2) * δ * (k : ℝ))^2 = (9 / 4) * (k : ℝ)^2 * δ^2 by ring, hδsq]
      nlinarith [show 0 ≤ (k : ℝ)^2 * ρ by positivity]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hzb.trans haux)
  obtain ⟨h',e,he,heq⟩ := twoColourGenerating_cusp_exists_unit hk₁ hg
  have hzre : 0 < z.re := by simpa only [z, verticalPoint_re] using ha
  have hτ : (h : ℂ) / k + I * z / (k : ℂ)^2 = (x : ℂ) + I * (ρ : ℂ) := by
    dsimp [z, a, b, verticalPoint]
    push_cast
    field_simp [hkC]
    ring_nf
    rw [I_sq]
    ring
  let ζ := 2 * (Real.pi : ℂ) * ((ρ : ℂ) - (x : ℂ) * I)
  have hζ : -ζ = 2 * (Real.pi : ℂ) * I * ((x : ℂ) + I * (ρ : ℂ)) := by
    dsimp [ζ]
    ring_nf
    simp only [I_sq]
    ring
  let w := -(2 * (Real.pi : ℂ) * I * ((h' : ℂ) / k + I / z))
  have hw : Real.pi ≤ w.re := by
    have hw' : w = ((2 * Real.pi : ℝ) : ℂ) * z⁻¹ -
        ((2 * Real.pi * (h' : ℝ) / (k : ℝ) : ℝ) : ℂ) * I := by
      dsimp [w]
      push_cast
      rw [div_eq_mul_inv I]
      ring_nf
      simp only [I_sq]
      ring
    rw [hw', sub_re, real_part_angular_exp, mul_re]
    simp only [ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left hcl Real.pi_pos.le]
  have hq : ‖exp (-w)‖ ≤ Real.exp (-Real.pi) := by
    rw [norm_exp, neg_re]
    exact Real.exp_le_exp.mpr (neg_le_neg hw)
  let V := (Real.pi : ℂ) / (6 * z) - (Real.pi : ℂ) * z / (6 * (k : ℂ)^2)
  have hV : V.re ≤ Real.pi / (24 * ρ) := by
    have hF : V = ((Real.pi / 6 : ℝ) : ℂ) * z⁻¹ -
        ((Real.pi / (6 * (k : ℝ)^2) : ℝ) : ℂ) * z := by
      dsimp [V]
      push_cast
      ring
    rw [hF, sub_re, real_part_angular_exp, real_part_angular_exp]
    calc
      _ ≤ (Real.pi / 6) * (z⁻¹).re := sub_le_self _ (by positivity)
      _ ≤ (Real.pi / 6) * (1 / (4 * ρ)) := mul_le_mul_of_nonneg_left hch (by positivity)
      _ = _ := by ring
  have hExp : ((n : ℂ) * ζ).re = 2 * Real.pi * n * ρ := by
    have hζ' : ζ = ((2 * Real.pi : ℝ) : ℂ) * ((ρ : ℂ) - (x : ℂ) * I) := by push_cast; rfl
    rw [hζ', ← Complex.ofReal_natCast n, real_part_angular_exp, real_part_angular_exp,
      real_part_circle_point]
    ring
  have hEval := heq hzre
  rw [hτ, ← hζ, show 2 * (Real.pi : ℂ) * I * ((h' : ℂ) / k + I / z) = -w by simp [w]] at hEval
  change twoColourGenerating (exp (-ζ)) =
    e * (z / (k : ℂ)) * exp V * twoColourGenerating (exp (-w)) at hEval
  change ‖exp ((n : ℂ) * ζ) * twoColourGenerating (exp (-ζ))‖ ≤ _
  rw [hEval, norm_mul, norm_mul, norm_mul, norm_mul, he, one_mul, norm_div,
    Complex.norm_natCast, norm_exp, norm_exp, hExp]
  calc
    _ ≤ Real.exp (2 * Real.pi * n * ρ) *
        (((3 / 2) * δ) * Real.exp (Real.pi / (24 * ρ)) * (3 / 2)) := by
      gcongr
      exact (norm_twoColourGenerating_small_disc hq).1
    _ = _ := by rw [Real.exp_add]; ring

/-- The polar contribution to the central arc, with the coefficient shift already taken. -/
def twoColourCentralModel (n : ℕ) (ρ x : ℝ) : ℂ :=
  let z := (ρ : ℂ) - (x : ℂ) * I
  z * exp ((((Real.pi / 6 : ℝ) : ℂ) / z) +
    ((2 * Real.pi * ((n : ℝ) - 1 / 12) : ℝ) : ℂ) * z)

/-- The central integrand differs from its polar part by the decaying nonconstant
part of the transformed Euler product. -/
theorem norm_twoColourCoefficientIntegrand_sub_centralModel_le (n : ℕ) {ρ x : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 25) (hx : |x| ≤ Real.sqrt ρ) :
    ‖twoColourCoefficientIntegrand n ρ x - twoColourCentralModel n ρ x‖ ≤
      (3 / 5) * Real.sqrt ρ * Real.exp (2 * Real.pi * (n : ℝ) * ρ) := by
  let z : ℂ := (ρ : ℂ) - (x : ℂ) * I
  let ζ := (2 * (Real.pi : ℂ)) * z
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hzR : z.re = ρ := real_part_circle_point ρ x
  have hz₀ : z ≠ 0 := by intro he; rw [he, zero_re] at hzR; linarith
  have hζR : 0 < ζ.re := by
    have he : ζ = ((2 * Real.pi : ℝ) : ℂ) * z := by dsimp [ζ]; push_cast; rfl
    rw [he, real_part_angular_exp, hzR]
    positivity
  have hzn : ‖z‖ ^ 2 = ρ^2 + x^2 := by
    rw [show z = verticalPoint ρ (-x) from circle_point_eq_vertical ρ x,
      norm_verticalPoint_sq, neg_sq]
  have hxSq : x^2 ≤ ρ := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hx 2
    rwa [sq_abs, Real.sq_sqrt hρ.le] at hh
  have hBounds : ‖z‖ ≤ (6 / 5) * Real.sqrt ρ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [hzn, mul_pow, Real.sq_sqrt hρ.le]
    nlinarith [mul_le_mul_of_nonneg_left hρ' hρ.le]
  have hzInv : 3 / 4 ≤ (z⁻¹).re := by
    rw [Complex.inv_re, ← Complex.sq_norm, hzR, hzn, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hρ' hρ.le]
  let ω := ((2 * Real.pi : ℝ) : ℂ) * z⁻¹
  let q := exp (-ω)
  have hωR : ω.re = (2 * Real.pi) * (z⁻¹).re := real_part_angular_exp (2 * Real.pi) _
  have hq : ‖q‖ ≤ Real.exp (-Real.pi) := by
    change ‖exp (-ω)‖ ≤ _
    rw [norm_exp, neg_re, hωR, Real.exp_le_exp]
    have h := mul_le_mul_of_nonneg_left hzInv (show 0 ≤ 2 * Real.pi by positivity)
    linarith [Real.pi_pos]
  have hqNorm : ‖q‖ = Real.exp (-(2 * Real.pi) * (z⁻¹).re) := by
    change ‖exp (-ω)‖ = _
    rw [norm_exp, neg_re, hωR, neg_mul]
  let r := Real.exp (-Real.pi)
  have hr : 0 < r := Real.exp_pos _
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos)
  have hR : (twoColourGenerating (r : ℂ)).re - 1 ≤ 1 / 2 := by
    have h := (norm_twoColourGenerating_small_disc
      (q := (r : ℂ)) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr])).2
    have h₁ := Complex.re_le_norm (twoColourGenerating (r : ℂ) - 1)
    rw [sub_re, one_re] at h₁
    exact h₁.trans h
  have hrem : ‖twoColourGenerating q - 1‖ ≤
      Real.exp (Real.pi - (2 * Real.pi) * (z⁻¹).re) * (1 / 2) := by
    have h := (norm_twoColourGenerating_sub_one_le hr hr' hq).trans
      (mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ ‖q‖ / r))
    have hE : ‖q‖ / r = Real.exp (Real.pi - (2 * Real.pi) * (z⁻¹).re) := by
      dsimp only [r]
      rw [hqNorm, ← Real.exp_sub]
      congr 1
      ring
    rwa [hE] at h
  let a := Real.pi / 6
  let b := 2 * Real.pi * ((n : ℝ) - 1 / 12)
  let W := ((a : ℂ) / z + (b : ℂ) * z)
  have hModel : twoColourCentralModel n ρ x = z * exp W := rfl
  have hMod := twoColourGenerating_modular_cusp_zero hζR
  have h1 : ζ / (2 * (Real.pi : ℂ)) = z := by dsimp [ζ]; field_simp
  have h2 : 4 * (Real.pi : ℂ) ^ 2 / ζ = ω := by dsimp [ζ, ω]; push_cast; field_simp; ring
  have h3 : (n : ℂ) * ζ + (-ζ / 12 + (Real.pi : ℂ)^2 / (3 * ζ)) = W := by
    dsimp [ζ, W, a, b]
    push_cast
    field_simp
    ring
  rw [h1, h2] at hMod
  have hF : twoColourCoefficientIntegrand n ρ x = z * exp W * twoColourGenerating q := by
    change exp ((n : ℂ) * ζ) * twoColourGenerating (exp (-ζ)) =
      z * exp W * twoColourGenerating (exp (-ω))
    rw [hMod, ← h3, exp_add ((n : ℂ) * ζ)]
    ring
  rw [hF, hModel, ← mul_sub_one, norm_mul, norm_mul, norm_exp]
  have hW : W.re = a * (z⁻¹).re + b * ρ := by
    dsimp [W]
    rw [div_eq_mul_inv, real_part_angular_exp, real_part_angular_exp, hzR]
  rw [hW]
  have hExpo : ((a - 2 * Real.pi) * (z⁻¹).re + Real.pi) + b * ρ ≤
      2 * Real.pi * (n : ℝ) * ρ := by
    have ha' : a - 2 * Real.pi < 0 := by dsimp [a]; linarith [Real.pi_pos]
    have hA := mul_le_mul_of_nonpos_left hzInv ha'.le
    have hB : b * ρ ≤ 2 * Real.pi * (n : ℝ) * ρ := by
      dsimp only [b]
      nlinarith [mul_nonneg Real.pi_pos.le hρ.le]
    dsimp only [a] at hA ⊢
    linarith [Real.pi_pos]
  calc
    _ ≤ ((6 / 5) * Real.sqrt ρ * Real.exp (a * (z⁻¹).re + b * ρ)) *
           (Real.exp (Real.pi - (2 * Real.pi) * (z⁻¹).re) * (1 / 2)) := by gcongr
    _ = (3 / 5) * Real.sqrt ρ * Real.exp (((a - 2 * Real.pi) * (z⁻¹).re + Real.pi) + b * ρ) := by
      have hExp : ((a - 2 * Real.pi) * (z⁻¹).re + Real.pi) + b * ρ =
        (a * (z⁻¹).re + b * ρ) + (Real.pi - (2 * Real.pi) * (z⁻¹).re) := by ring
      rw [hExp, Real.exp_add (a * (z⁻¹).re + b * ρ)]
      ring
    _ ≤ _ := by gcongr

/-- The central model on the open radial half plane is a continuous function of the angle. -/
theorem continuous_twoColourCentralModel (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (twoColourCentralModel n ρ) := by
  unfold twoColourCentralModel
  let z := fun x : ℝ => (ρ : ℂ) - (x : ℂ) * I
  have hZ : Continuous z := by dsimp [z]; fun_prop
  have hZ₀ (x : ℝ) : z x ≠ 0 := by
    intro he
    have hx := real_part_circle_point ρ x
    change (z x).re = ρ at hx
    rw [he, zero_re] at hx
    linarith
  exact hZ.mul (Complex.continuous_exp.comp
    ((continuous_const.div hZ hZ₀).add (continuous_const.mul hZ)))

end DurfeeCCS.Step06
