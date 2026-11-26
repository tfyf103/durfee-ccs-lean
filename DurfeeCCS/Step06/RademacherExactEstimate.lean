module

public import DurfeeCCS.Step06.RademacherExactBounds
public import DurfeeCCS.Step06.RademacherExactArc
import Mathlib.Analysis.Real.Pi.Bounds

/-! The effective first-Bessel-term estimate needed in (68), proved on a single circle. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step06

open Complex Set MeasureTheory

/-- The first Bessel contribution with the normalization used in (14). -/
def twoColourRademacherMain (n : ℕ) : ℂ :=
  ((2 * Real.pi / (12 * (n : ℝ) - 1) : ℝ) : ℂ) *
    besselI 2 (twoColourBesselScale n)

private theorem twoColourRademacherMain_eq_polar {n : ℕ} (hn : 0 < n) :
    twoColourRademacherMain n =
      (2 * Real.pi : ℂ) * ((Real.pi / 6 / (2 * Real.pi * ((n : ℝ) - 1 / 12)) : ℝ) : ℂ) *
        besselI 2 ((2 * Real.sqrt (Real.pi / 6 * (2 * Real.pi * ((n : ℝ) - 1 / 12))) : ℝ) : ℂ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hS : 0 < (n : ℝ) - 1 / 12 := by linarith
  have hS' : 0 < 12 * (n : ℝ) - 1 := by linarith
  have hArg : twoColourBesselScale n = 2 * Real.sqrt
      (Real.pi / 6 * (2 * Real.pi * ((n : ℝ) - 1 / 12))) := by
    unfold twoColourBesselScale
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [div_pow, mul_pow, Real.sq_sqrt hS'.le, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hPref : (2 * Real.pi / (12 * (n : ℝ) - 1)) =
      (2 * Real.pi) * (Real.pi / 6 / (2 * Real.pi * ((n : ℝ) - 1 / 12))) := by
    field_simp [Real.pi_ne_zero, hS.ne', hS'.ne']
    ring
  rw [twoColourRademacherMain, hArg, hPref]
  push_cast
  rfl

/-- The normalized effect of the two minor arcs is bounded using total arc length at most one. -/
private theorem norm_twoColourMinorArcs_le (n : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 25) :
    ‖(∫ x : ℝ in -(1 / 2)..-Real.sqrt ρ, twoColourCoefficientIntegrand n ρ x) +
      (∫ x : ℝ in Real.sqrt ρ..(1 / 2), twoColourCoefficientIntegrand n ρ x)‖ ≤
      (9 / 20) * Real.exp (2 * Real.pi * (n : ℝ) * ρ + Real.pi / (24 * ρ)) := by
  let δ := Real.sqrt ρ
  let F := twoColourCoefficientIntegrand n ρ
  let E := Real.exp (2 * Real.pi * (n : ℝ) * ρ + Real.pi / (24 * ρ))
  have hδ : 0 < δ := Real.sqrt_pos.mpr hρ
  have hδsq : δ^2 = ρ := Real.sq_sqrt hρ.le
  have hδ' : δ ≤ 1 / 5 := by nlinarith only [hδsq, hρ', sq_nonneg (δ - 1 / 5)]
  have hL : -(1 / 2 : ℝ) ≤ -δ := by linarith
  have hR : δ ≤ (1 / 2 : ℝ) := by linarith
  have hl := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(1 / 2)) (b := -δ) (f := F) (C := (9 / 4) * δ * E) (by
      rw [Set.uIoc_of_le hL]
      intro x hx
      have hx' : x ≤ 0 := hx.2.trans (neg_nonpos.mpr hδ.le)
      exact norm_twoColourCoefficientIntegrand_minor_le n hρ hρ'
        (by rw [abs_of_nonpos hx']; linarith [hx.2])
        (by rw [abs_of_nonpos hx']; linarith [hx.1]))
  have hr := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := δ) (b := 1 / 2) (f := F) (C := (9 / 4) * δ * E) (by
      rw [Set.uIoc_of_le hR]
      intro x hx
      have hx' : 0 ≤ x := (hδ.trans hx.1).le
      exact norm_twoColourCoefficientIntegrand_minor_le n hρ hρ'
        (by rw [abs_of_nonneg hx']; exact hx.1.le)
        (by rw [abs_of_nonneg hx']; exact hx.2))
  rw [abs_of_nonneg (sub_nonneg.mpr hL)] at hl
  rw [abs_of_nonneg (sub_nonneg.mpr hR)] at hr
  change ‖(∫ x in -(1 / 2)..-δ, F x) + (∫ x in δ..(1 / 2), F x)‖ ≤ (9 / 20) * E
  calc
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hl hr)
    _ = ((9 / 4) * δ * (1 - 2 * δ)) * E := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      nlinarith [sq_nonneg δ]

private theorem norm_twoColourCentralRemainder_le (n : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 25) :
    ‖(∫ x : ℝ in -Real.sqrt ρ..Real.sqrt ρ, twoColourCoefficientIntegrand n ρ x) -
      (∫ x : ℝ in -Real.sqrt ρ..Real.sqrt ρ, twoColourCentralModel n ρ x)‖ ≤
      (1 / 20) * Real.exp (2 * Real.pi * (n : ℝ) * ρ) := by
  let δ := Real.sqrt ρ
  let C := (3 / 5) * δ * Real.exp (2 * Real.pi * (n : ℝ) * ρ)
  have hδ : 0 < δ := Real.sqrt_pos.mpr hρ
  have hδsq : δ^2 = ρ := Real.sq_sqrt hρ.le
  have hI : -δ ≤ δ := by linarith
  rw [← intervalIntegral.integral_sub
    ((continuous_twoColourCoefficientIntegrand n hρ).intervalIntegrable _ _)
    ((continuous_twoColourCentralModel n hρ).intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -δ) (b := δ) (f := fun x => twoColourCoefficientIntegrand n ρ x -
      twoColourCentralModel n ρ x) (C := C) (by
      rw [Set.uIoc_of_le hI]
      intro x hx
      exact norm_twoColourCoefficientIntegrand_sub_centralModel_le n hρ hρ'
        (abs_le.mpr ⟨hx.1.le,hx.2⟩))
  rw [abs_of_nonneg (sub_nonneg.mpr hI)] at h
  refine h.trans ?_
  dsimp only [C]
  calc
    _ = (6 / 5) * δ^2 * Real.exp (2 * Real.pi * ↑n * ρ) := by ring
    _ ≤ _ := by rw [hδsq]; gcongr; linarith

private theorem norm_twoColourModel_sub_RademacherMain_le {n : ℕ} (hn : 0 < n)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 25) :
    ‖(∫ x : ℝ in -Real.sqrt ρ..Real.sqrt ρ, twoColourCentralModel n ρ x) -
      twoColourRademacherMain n‖ ≤ (3 / 20) * Real.exp (2 * Real.pi * (n : ℝ) * ρ) := by
  let a := Real.pi / 6
  let b := 2 * Real.pi * ((n : ℝ) - 1 / 12)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; exact mul_pos (by positivity) (by linarith)
  have h := norm_integral_polar_arc_sub_bessel_le hρ ha hb
  rw [twoColourRademacherMain_eq_polar hn]
  change ‖(∫ x : ℝ in -Real.sqrt ρ..Real.sqrt ρ, rademacherCentralKernel ρ a b x) -
    (2 * Real.pi : ℂ) * ((a / b : ℝ) : ℂ) * besselI 2 ((2 * Real.sqrt (a*b) : ℝ) : ℂ)‖ ≤ _
  rw [mul_assoc (2 * (Real.pi : ℂ))]
  refine h.trans ?_
  have hC' : rademacherPolarLine ρ ≤ 1 := by
    unfold rademacherPolarLine
    rw [div_le_one (by linarith)]
    linarith
  have ha' : a * rademacherPolarLine ρ ≤ 2 / 3 := by
    calc
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left hC' ha.le
      _ ≤ _ := by dsimp [a]; linarith [Real.pi_lt_four]
  have hb' : b * ρ ≤ 2 * Real.pi * (n : ℝ) * ρ := by
    dsimp [b]
    nlinarith [mul_nonneg Real.pi_pos.le hρ.le]
  rw [Real.exp_add, div_eq_mul_inv, inv_rademacherPolarHeight_sq hρ]
  have hE : Real.exp (a * rademacherPolarLine ρ) ≤ 3 := calc
    _ ≤ Real.exp (2 / 3) := Real.exp_le_exp.mpr ha'
    _ ≤ 1 / (1 - (2 / 3 : ℝ)) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    _ = 3 := by norm_num
  have hSmall : ρ * (1 + ρ)^2 ≤ (1 / 25 : ℝ) * (1 + 1 / 25)^2 := by gcongr
  calc
    _ ≤ 3 * Real.exp (2 * Real.pi * (n : ℝ) * ρ) * ((1 / 25 : ℝ) * (1 + 1 / 25)^2) := by gcongr
    _ ≤ _ := by nlinarith [Real.exp_nonneg (2 * Real.pi * (n : ℝ) * ρ)]

/-- Formula (68) for all inputs at least sixteen, from the central cusp and a
pointwise bound on the two minor arcs of a single horizontal coefficient contour. -/
theorem norm_twoColourPartitionCount_sub_RademacherMain_large {n : ℕ} (hn : 16 ≤ n) :
    ‖(twoColourPartitionCount n : ℂ) - twoColourRademacherMain n‖ ≤
      (Real.pi ^ 3 / 36) * Real.exp (Real.pi * Real.sqrt ((n : ℝ) / 3)) := by
  let s := Real.sqrt (3 * (n : ℝ))
  let ρ : ℝ := 1 / (4 * s)
  let δ := Real.sqrt ρ
  let F := twoColourCoefficientIntegrand n ρ
  let G := twoColourCentralModel n ρ
  let E := Real.exp (2 * Real.pi * (n : ℝ) * ρ + Real.pi / (24 * ρ))
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsSq : s^2 = 3 * (n : ℝ) := Real.sq_sqrt (by positivity)
  have hρ : 0 < ρ := by positivity
  have hρ' : ρ ≤ 1 / 25 := by
    suffices h : (25 / 4 : ℝ) ≤ s from one_div_le_one_div_of_le (by norm_num) (by linarith)
    nlinarith [sq_nonneg (s - 25 / 4)]
  have hδ : 0 < δ := Real.sqrt_pos.mpr hρ
  have hδsq : δ^2 = ρ := Real.sq_sqrt hρ.le
  have hδ' : δ ≤ 1 / 5 := by nlinarith [sq_nonneg (δ - 1 / 5)]
  have hE : Real.exp (2 * Real.pi * (n : ℝ) * ρ) ≤ E :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity))
  have hU : E = Real.exp (Real.pi * Real.sqrt ((n : ℝ) / 3)) := by
    have hS : s / 3 = Real.sqrt ((n : ℝ) / 3) := by
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      rw [div_pow, hsSq, Real.sq_sqrt (by positivity)]
      ring
    have hEq : 2 * Real.pi * (n : ℝ) * ρ + Real.pi / (24 * ρ) = Real.pi * (s / 3) := by
      dsimp only [ρ]
      field_simp [hs.ne']
      linear_combination -48 * hsSq
    dsimp only [E]
    rw [hEq, hS]
  have hf := continuous_twoColourCoefficientIntegrand n hρ
  have hsplit : (twoColourPartitionCount n : ℂ) =
      ((∫ x in -(1 / 2)..-δ, F x) + (∫ x in δ..(1 / 2), F x)) + (∫ x in -δ..δ, F x) := by
    rw [twoColourPartitionCount_eq_horizontal_integral n hρ]
    change (∫ x in -(1 / 2)..(1 / 2), F x) = _
    rw [add_right_comm, intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-(1 / 2)) (-δ)) (hf.intervalIntegrable (-δ) δ),
      intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable (-(1 / 2)) δ) (hf.intervalIntegrable δ (1 / 2))]
  have hm := norm_twoColourMinorArcs_le n hρ hρ'
  have hc := (norm_twoColourCentralRemainder_le n hρ hρ').trans
    (mul_le_mul_of_nonneg_left hE (by norm_num))
  have hb := (norm_twoColourModel_sub_RademacherMain_le (by omega : 0 < n) hρ hρ').trans
    (mul_le_mul_of_nonneg_left hE (by norm_num))
  let L := ∫ x in -(1 / 2)..-δ, F x
  let R := ∫ x in δ..(1 / 2), F x
  let A := ∫ x in -δ..δ, F x
  let B := ∫ x in -δ..δ, G x
  let M := twoColourRademacherMain n
  rw [← hU, hsplit]
  change ‖(L + R) + A - M‖ ≤ _
  have hSum : (L + R) + A - M = (L + R) + (A - B) + (B - M) := by ring
  rw [hSum]
  calc
    _ ≤ (‖L + R‖ + ‖A - B‖) + ‖B - M‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((9 / 20) * E + (1 / 20) * E) + (3 / 20) * E := add_le_add (add_le_add hm hc) hb
    _ ≤ _ := by
      have hπ : (13 / 20 : ℝ) ≤ Real.pi^3/36 := by
        have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 3
        norm_num at hc
        linarith
      simpa only [← add_mul, show (9 / 20 + 1 / 20 + 3 / 20 : ℝ) = 13 / 20 by norm_num]
        using mul_le_mul_of_nonneg_right hπ (Real.exp_nonneg _)

end DurfeeCCS.Step06
