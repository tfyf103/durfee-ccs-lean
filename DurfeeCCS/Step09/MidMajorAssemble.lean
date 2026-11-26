module

public import DurfeeCCS.Step09.MidMajorCentral
public import DurfeeCCS.Step09.MidMajorTail
public import DurfeeCCS.Step09.MidMultiplierLocal
public import DurfeeCCS.Step09.MidPhaseQuartic
public import DurfeeCCS.Step09.MidModelJ
public import DurfeeCCS.Step09.MidGaussianModel
public import DurfeeCCS.Step07.ThetaAllRadiusRows
public import DurfeeCCS.Step07.ThetaTailRadius

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The analytic bounds of Lemma 3.8 realized at the verified radius rows. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

def midMajorMainTerm (n : ℕ) (r : ℝ) : ℂ :=
  (saddleAmplitude n r / 2 : ℝ) * exp ((saddlePhase n r : ℂ) * I)

/-- Equation (60) with the verified upper bound on the slope. -/
theorem norm_midGaussianModel_sub_main_le {n : ℕ} {r ρhi : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hρ : midSlope r ≤ ρhi) (hρhi : ρhi ≤ 3 / 2) :
    ‖midGaussianModel n r - midMajorMainTerm n r‖ ≤
      saddleAmplitude n r / 2 * midMajorJError (saddleS r).re (saddleS r).im
        (Real.sqrt (n : ℝ)) (midMajorGap ρhi (3 / 2)) := by
  let a := (saddleS r).re
  let b := (saddleS r).im
  let x := Real.sqrt (n : ℝ)
  let t := midOmega n r
  let ρ := midSlope r
  let δ := midMajorGap ρhi (3 / 2)
  have hn' : 0 < n := by omega
  have hr' : 0 < r := by linarith
  have hM := saddleAmplitude_pos hn' hr'
  have ⟨hρp,hρ1⟩ := midSlope_bounds hr'
  have ht1 := midOmega_ge_one hn hr
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have ha := (saddleS_components hr').1.trans (saddleS_components hr').2
  have hδ : δ ≤ (3 - 2 * ρ) ^ 2 / 13 := by
    have h := midMajorGap_anti_slope hρ hρhi
    unfold midMajorGap at h
    change _ ≤ _
    exact h.trans_eq (by ring)
  have hj := lemma37 ht1 hρp hρ1
  dsimp only at hj
  let B := 1 / (2 * t * Real.sqrt (1 + ρ ^ 2))
  have hB : B ≤ (2 * t)⁻¹ := by
    have hs : 1 ≤ Real.sqrt (1 + ρ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ρ])
    dsimp only [B]
    rw [← one_div (2 * t)]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (le_mul_of_one_le_right (by positivity) hs)
  have he : t * ρ ^ 2 = b ^ 2 * x / a := by
    change a * x * (b / a) ^ 2 = _
    field_simp [ha.ne']
  have hγ : Real.exp (-(t * (3 - 2 * ρ) ^ 2 / 13)) ≤ Real.exp (-δ * t) := by
    apply Real.exp_le_exp.mpr
    have h := neg_le_neg (mul_le_mul_of_nonneg_left hδ ht.le)
    convert h using 1 <;> ring
  have ht_eq : a * x = t := rfl
  have hnorm :
      ‖(Real.sqrt (t / Real.pi) : ℂ) * midModelJ t ρ / midModelZ ρ - 1‖ ≤
        midMajorJError a b x δ := by
    refine hj.trans ?_
    unfold midMajorJError midMajorJBase
    rw [ht_eq, ← he]
    exact add_le_add
      (add_le_add hB (mul_le_mul_of_nonneg_right (add_le_add_right hB _) (Real.exp_pos _).le))
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hγ) (by positivity))
  have hfact : midGaussianModel n r - midMajorMainTerm n r = midMajorMainTerm n r *
      ((Real.sqrt (t / Real.pi) : ℂ) * midModelJ t ρ / midModelZ ρ - 1) := by
    rw [midGaussianModel_eq_prediction hn' hr', midMajorMainTerm]
    dsimp only [t, ρ]
    ring
  rw [hfact, norm_mul, midMajorMainTerm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_of_nonneg (by positivity : 0 ≤ saddleAmplitude n r / 2)]
  exact mul_le_mul_of_nonneg_left hnorm (by positivity)

private theorem midMajorLocalLog_nonneg {eps q h : ℝ} (he : 0 ≤ eps) (hq : 0 ≤ q)
    (hh : h ≤ Real.pi / 2) : 0 ≤ midMajorLocalLog eps q h := by
  have hK : 0 ≤ theta38K h := by
    unfold theta38K
    dsimp only
    exact add_nonneg (inv_nonneg.mpr (sq_nonneg _)) (inv_nonneg.mpr
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by linarith only [hh]))))
  unfold midMajorLocalLog
  positivity

private theorem midMajorLocalLog_dominates {n : ℕ} (hn : 0 < n) {r eps q h : ℝ}
    (hr : 0 < r) (he : r⁻¹ ≤ eps) (hq : midU n r ≤ q)
    (hh : h ≤ Real.pi / 2) :
    midLocalLogBound (midU n r) r⁻¹ h ≤ midMajorLocalLog eps q h := by
  have hK : 0 ≤ theta38K h := by
    unfold theta38K
    dsimp only
    exact add_nonneg (inv_nonneg.mpr (sq_nonneg _)) (inv_nonneg.mpr
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by linarith only [hh]))))
  have hu := saddleU_pos hn hr
  have he₀ := inv_nonneg.mpr hr.le
  have he' := he₀.trans he
  unfold midLocalLogBound midMajorLocalLog
  gcongr

private theorem midMajor_half_arc_bound {n : ℕ} {r eps q h ρhi : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (heps : r⁻¹ ≤ eps) (hq : midU n r ≤ q) (hh : h = 3 / 4 ∨ h = 1)
    (hρ : midSlope r ≤ ρhi) (hρhi : ρhi ≤ 3 / 2) :
    ‖midContribution n r 0 0 8 - midMajorMainTerm n r‖ ≤
      saddleAmplitude n r / 2 * ((243 / 100) * midMajorLocalError eps q h (midQuarticConstant h) +
        midMajorJError (saddleS r).re (saddleS r).im (Real.sqrt (n : ℝ)) (midMajorGap ρhi (3 / 2)) +
        midMajorEtaError (midOmega n r) (midMajorGap ρhi (3 / 2)) (midMajorGap ρhi 3)) := by
  have hhn : 0 < n := by omega
  have hrp : 0 < r := by linarith
  have hu := saddleU_pos hhn hrp
  have hp : 0 < h := by rcases hh with hh | hh <;> rw [hh] <;> norm_num
  have hhi : h < Real.pi / 2 := by
    rcases hh with hh | hh <;> rw [hh] <;> linarith [Real.pi_gt_d2]
  have hκ : 0 ≤ midQuarticConstant h := by unfold midQuarticConstant; split <;> norm_num
  have hlocal := midMajor_central_error_le hn hr hmax heps hq hp hκ
    (midMajorLocalLog_nonneg ((inv_nonneg.mpr hrp.le).trans heps) (hu.le.trans hq) hhi.le)
    (fun η hη χ hχ => (norm_midMultiplier_sub_one_le_inner hn hr hmax hη.1 hη.2
      hp.le hhi (abs_le.mpr hχ)).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr (midMajorLocalLog_dominates hhn hrp heps hq hhi.le)) _))
    (fun χ hχ => by
      rw [show midPhase r 0 χ - (saddleS r ^ 2 - midCurvature r * (χ : ℂ) ^ 2) =
        midPhase r 0 χ - saddleS r ^ 2 + midCurvature r * (χ : ℂ) ^ 2 by ring]
      exact (norm_midPhase_quartic_le hr (abs_le.mpr hχ) hh).trans_eq (by ring))
  have hmodel := norm_midGaussianModel_sub_main_le hn hr hρ hρhi
  have htail := midMajor_eta_tail_le hn hr hmax hρ hρhi
  have hc : IntervalIntegrable (midMajorChiIntegral n r) volume (0 : ℝ) (3 / 2) :=
    intervalIntegrable_midMajorChiIntegral hhn hr le_rfl (by norm_num) (by norm_num)
      (fun η hη χ => (norm_midMultiplier_lt_10_9 hn hr hmax
        (by simpa only [abs_of_nonneg hη.1] using hη.2) 0 χ).le)
  have hd : IntervalIntegrable (midMajorChiIntegral n r) volume (3 / 2) 8 :=
    intervalIntegrable_midMajorChiIntegral hhn hr (by norm_num) (by norm_num) (by norm_num)
      (fun η hη χ => (norm_midMultiplier_lt_2100 hn hr hmax (by
        rw [abs_of_nonneg (by linarith only [hη.1])]
        exact hη.2) 0 χ).le)
  have he : midContribution n r 0 0 8 =
      midContribution n r 0 0 (3 / 2) + midContribution n r 0 (3 / 2) 8 := by
    change (midMajorPrefactor n r : ℂ) * (∫ η in (0 : ℝ)..8, midMajorChiIntegral n r η) =
      (midMajorPrefactor n r : ℂ) * (∫ η in (0 : ℝ)..(3 / 2), midMajorChiIntegral n r η) +
      (midMajorPrefactor n r : ℂ) * (∫ η in (3 / 2 : ℝ)..8, midMajorChiIntegral n r η)
    rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals hc hd]
  have hf : midContribution n r 0 0 8 - midMajorMainTerm n r =
      (midContribution n r 0 0 (3 / 2) - midGaussianModel n r) +
      (midGaussianModel n r - midMajorMainTerm n r) + midContribution n r 0 (3 / 2) 8 := by
    rw [he]
    ring
  rw [hf]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hlocal hmodel) htail).trans_eq (by ring))



private theorem midMajor_finite_formula (ell aMin aMax bMin bMax h κ : ℝ) :
    (243 / 100) * midMajorLocalError (Real.exp (-ell)) (aMax / 80) h κ +
      (midMajorJBase (80 * aMin) + 8 * Real.sqrt (80 * aMax) *
        (Real.exp (-(80 * bMin ^ 2 / aMax)) +
          Real.exp (-(80 * aMin * theta38Delta aMin bMax)))) +
      midMajorEtaError (80 * aMin) (theta38Delta aMin bMax) (theta38DeltaThree aMin bMax) =
      theta38Error ell aMin aMax bMin bMax h κ := by
  unfold theta38Error midMajorLocalError midMajorQuarticError midMajorMultiplierError midMajorChiError
    midMajorEtaError midMajorJBase midMajorLocalLog midMajorZ theta38Z
  dsimp only
  rw [show (2 : ℝ) * (80 * aMin) = 160 * aMin by ring,
    show (-4 : ℝ) * (80 * aMin) = -320 * aMin by ring]
  simp only [neg_mul, neg_div, mul_assoc]

private theorem midMajor_tails_formula (x : ℝ) :
    (243 / 100) * midMajorLocalError (Real.exp (-5)) 0.072 1 0.547 +
      (midMajorJBase (80 * 5.29406) + 8 * Real.sqrt (theta38Growth x * x) *
        (Real.exp (-((1.48481 : ℝ) ^ 2 * x / theta38Growth x)) +
          Real.exp (-(theta38Delta 5.29406 (Real.pi / 2)) * (5.29406 * x)))) +
      midMajorEtaError (80 * 5.29406) (theta38Delta 5.29406 (Real.pi / 2))
        (theta38DeltaThree 5.29406 (Real.pi / 2)) =
      theta38TailError x := by
  unfold theta38TailError
  rw [← midMajor_finite_formula]
  simp only [theta38TailB, theta38TailD]
  rw [show (0.072 : ℝ) = 5.76 / 80 by norm_num,
    show -(theta38Delta 5.29406 (Real.pi / 2)) * (5.29406 * x) =
      -(80 * 5.29406 * theta38Delta 5.29406 (Real.pi / 2)) * (x / 80) by ring,
    show -((1.48481 : ℝ) ^ 2 * x / theta38Growth x) =
      -(1.48481 : ℝ) ^ 2 * x / theta38Growth x by ring]
  ring

private theorem midMajor_finite_rows_within {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hlog : Real.log r ≤ 5) :
    ‖midContribution n r 0 0 8 - midMajorMainTerm n r‖ < (0.88 : ℝ) * (saddleAmplitude n r / 2) := by
  have hnp : 0 < n := by omega
  have hrp : 0 < r := by linarith
  have hM := saddleAmplitude_pos hnp hrp
  obtain ⟨i, _, hs, heps, hq, hρ, hbudget⟩ := theta38_finite_rows_verified hn hrp (Real.log_nonneg hr) hlog
  let row := theta38Row i
  let a := (saddleS r).re
  let b := (saddleS r).im
  let x := Real.sqrt (n : ℝ)
  let ρhi := theta38Rho row.aMin row.bMax
  let δ := theta38Delta row.aMin row.bMax
  let δ₃ := theta38DeltaThree row.aMin row.bMax
  obtain ⟨hAmin, hAmax, hρhi, hCutD, hCutB⟩ := theta38_rows_admissible i
  have hh : row.h = 3 / 4 ∨ row.h = 1 := by
    fin_cases i <;> norm_num [row, theta38Row]
  have hκ : midQuarticConstant row.h = row.kappa := by
    fin_cases i <;> norm_num [row, theta38Row, midQuarticConstant]
  obtain ⟨hal, hau, hbl, _⟩ := hs
  have hδ : 0 ≤ δ := by dsimp [δ, theta38Delta]; positivity
  have hδ₃ := theta38_rows_delta_le_three i
  have hx : 80 ≤ x := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have ht : 80 * row.aMin ≤ midOmega n r := by
    change 80 * row.aMin ≤ a * x
    calc
      _ ≤ x * row.aMin := mul_le_mul_of_nonneg_right hx hAmin.le
      _ ≤ x * a := mul_le_mul_of_nonneg_left hal (by positivity)
      _ = _ := mul_comm _ _
  have hMain := midMajor_half_arc_bound hn hr hmax heps hq hh hρ (by linarith only [hρhi])
  rw [hκ] at hMain
  have hJ := midMajor_J_finite_le hAmin hal hau (theta38_rows_b_pos i).le hbl hx hδ
    hCutB.le hCutD.le
  have hEta := midMajor_eta_error_mono (by positivity : (0 : ℝ) < 80 * row.aMin) ht hδ hδ₃
    hCutD.le
  have hRw : midMajorGap ρhi (3 / 2) = δ ∧ midMajorGap ρhi 3 = δ₃ := by
    unfold ρhi δ δ₃ midMajorGap theta38Delta theta38DeltaThree
    constructor <;> ring
  rw [hRw.1, hRw.2] at hMain
  change ‖midContribution n r 0 0 8 - midMajorMainTerm n r‖ ≤
    saddleAmplitude n r / 2 * ((243 / 100) *
      midMajorLocalError (Real.exp (-row.ell)) (row.aMax / 80) row.h row.kappa +
      midMajorJError a b x δ + midMajorEtaError (midOmega n r) δ δ₃) at hMain
  have hBound := hMain.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hJ) hEta) (by positivity : 0 ≤ saddleAmplitude n r / 2))
  rw [midMajor_finite_formula] at hBound
  have hTarget : row.target ≤ 0.88 := by fin_cases i <;> norm_num [row, theta38Row]
  have hstrict : theta38Error row.ell row.aMin row.aMax row.bMin row.bMax row.h row.kappa < 0.88 :=
    hbudget.trans_le hTarget
  exact hBound.trans_lt ((mul_lt_mul_of_pos_left hstrict (by positivity)).trans_eq (mul_comm _ _))

private theorem midMajor_tail_row_within {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hlog : 5 ≤ Real.log r) :
    ‖midContribution n r 0 0 8 - midMajorMainTerm n r‖ < (0.88 : ℝ) * (saddleAmplitude n r / 2) := by
  have hnp : 0 < n := by omega
  have hrp : 0 < r := by linarith
  have hM := saddleAmplitude_pos hnp hrp
  let a := (saddleS r).re
  let b := (saddleS r).im
  let x := Real.sqrt (n : ℝ)
  let ρhi := Real.pi / (2 * 5.29406)
  let δ := theta38Delta 5.29406 (Real.pi / 2)
  let δ₃ := theta38DeltaThree 5.29406 (Real.pi / 2)
  obtain ⟨hal,hbl,_,heps,hq,hρ,hbudget⟩ := theta38_tail_radius_verified hn hrp hlog hmax
  have hρsmall : ρhi ≤ 1 / 2 := by
    unfold ρhi
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2 * 5.29406)).2
    norm_num
    linarith only [Real.pi_lt_d2]
  have hρhi : ρhi ≤ 3 / 2 := hρsmall.trans (by norm_num)
  have hδ : 0 ≤ δ := by dsimp [δ, theta38Delta]; positivity
  have hx : 80 ≤ x := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hA : a ≤ theta38Growth x := by
    have hlogmax := Real.log_le_log hrp hmax
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hnp)).ne',
      Real.log_exp, add_comm] at hlogmax
    have hR := saddleS_exp_re_le_arcGrowth (Real.log_nonneg hr) hlogmax
    simpa only [Real.exp_log hrp, theta38Growth] using hR
  have hδeq : midMajorGap ρhi (3 / 2) = δ ∧ midMajorGap ρhi 3 = δ₃ := by
    unfold ρhi δ δ₃ midMajorGap theta38Delta theta38DeltaThree theta38Rho
    constructor <;> ring
  have hδ₃ : δ ≤ δ₃ := by
    rw [← hδeq.1, ← hδeq.2]
    exact (midMajorGap_monotone (by unfold ρhi; positivity)) hρhi
      (hρhi.trans (by norm_num)) (by norm_num)
  have hD : (1 / 2 : ℝ) ≤ 80 * 5.29406 * δ := by
    have hδ₁ : (1 : ℝ) ≤ 3 / 2 - theta38Rho 5.29406 (Real.pi / 2) := by
      have heq : theta38Rho 5.29406 (Real.pi / 2) = ρhi := by
        unfold theta38Rho ρhi
        ring
      linarith only [hρsmall, heq]
    unfold δ theta38Delta
    have hp := pow_le_pow_left₀ zero_le_one hδ₁ 2
    nlinarith only [hp]
  have ht : 80 * (5.29406 : ℝ) ≤ midOmega n r := by
    change 80 * 5.29406 ≤ a * x
    calc
      _ ≤ x * 5.29406 := mul_le_mul_of_nonneg_right hx (by norm_num)
      _ ≤ x * a := mul_le_mul_of_nonneg_left hal (by positivity)
      _ = _ := mul_comm _ _
  have hMain := midMajor_half_arc_bound hn hr hmax heps hq (h := 1) (Or.inr rfl) hρ hρhi
  rw [hδeq.1, hδeq.2, show midQuarticConstant (1 : ℝ) = 0.547 by norm_num [midQuarticConstant]] at hMain
  have hJ := midMajor_J_tail_le hx hal hbl hA hδ hD
  have hEta := midMajor_eta_error_mono (by norm_num : (0 : ℝ) < 80 * 5.29406) ht hδ hδ₃ hD
  have hBound := hMain.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hJ) hEta) (by positivity : 0 ≤ saddleAmplitude n r / 2))
  rw [midMajor_tails_formula] at hBound
  exact hBound.trans_lt ((mul_lt_mul_of_pos_left (hbudget.trans (by norm_num : (0.212 : ℝ) < 0.88))
    (by positivity)).trans_eq (mul_comm _ _))

/-- The quantitative estimate on the positive main half-arc. -/
theorem midMajor_half_arc_error {n : ℕ} {r : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ)) :
    ‖midContribution n r 0 0 8 - midMajorMainTerm n r‖ < (0.88 : ℝ) * (saddleAmplitude n r / 2) := by
  rcases le_or_gt (Real.log r) 5 with hs | hl
  · exact midMajor_finite_rows_within hn hr hmax hs
  · exact midMajor_tail_row_within hn hr hmax hl.le


end DurfeeCCS.Step09
