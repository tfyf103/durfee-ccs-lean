module

public import DurfeeCCS.Step10.OuterRho
public import DurfeeCCS.Step09.MidPhaseSymmetry
public import DurfeeCCS.Step09.MidOtherPhase
public import DurfeeCCS.Step07.OuterTable

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Comparison of the middle and outer phases at the first outer sample on page 52. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Complex Real Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step09

/-- The geometric majorant for the dilogarithm on the open unit disk. -/
theorem norm_principalDilog_le_geom {z : ℂ} (hz : ‖z‖ < 1) :
    ‖principalDilog z‖ ≤ ‖z‖ / (1 - ‖z‖) := by
  let f (k : ℕ) := z ^ (k + 1) / (((k + 1 : ℕ) : ℂ) ^ 2)
  have hs : HasSum f (principalDilog z) := principalDilog_hasSum hz.le
  have hg : Summable (fun k : ℕ => ‖z‖ ^ (k + 1)) := by
    simpa only [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right ‖z‖
  have hbound (k : ℕ) : ‖f k‖ ≤ ‖z‖ ^ (k + 1) := by
    simp only [f, norm_div, norm_pow, Complex.norm_natCast]
    refine div_le_self (by positivity) (one_le_pow₀ ?_)
    exact_mod_cast Nat.succ_pos k
  have hf : Summable (fun k => ‖f k‖) := hg.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  calc
    _ ≤ ∑' k, ‖f k‖ := hs.tsum_eq ▸ norm_tsum_le_tsum_norm hf
    _ ≤ ∑' k : ℕ, ‖z‖ ^ (k + 1) := hf.tsum_le_tsum hbound hg
    _ = _ := by
      simp only [pow_succ, tsum_mul_right, tsum_geometric_of_lt_one (norm_nonneg z) hz,
        div_eq_mul_inv]
      ring

/-- The principal argument is Lipschitz with constant 1/h on Re z > h > 0. -/
theorem abs_arg_sub_le_of_re_gt {h : ℝ} (hh : 0 < h) {z w : ℂ}
    (hz : h < z.re) (hw : h < w.re) : |z.arg - w.arg| ≤ ‖z - w‖ / h := by
  have hlog : ‖Complex.log z - Complex.log w‖ ≤ h⁻¹ * ‖z - w‖ := by
    apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f' := fun a : ℂ => a⁻¹ • (1 : ℂ →L[ℝ] ℂ)) (s := {a : ℂ | h < a.re})
    · intro a ha
      exact (Complex.hasStrictFDerivAt_log_real
        (Complex.mem_slitPlane_iff.mpr (Or.inl (hh.trans ha)))).hasFDerivAt.hasFDerivWithinAt
    · intro a ha
      have hnorm : h < ‖a‖ := (show h < a.re from ha).trans_le (Complex.re_le_norm _)
      calc
        _ ≤ ‖a⁻¹‖ * ‖(1 : ℂ →L[ℝ] ℂ)‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ h⁻¹ := by
          change ‖a⁻¹‖ * ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ h⁻¹
          simpa only [ContinuousLinearMap.norm_id, mul_one, norm_inv] using
            (inv_le_inv₀ (hh.trans hnorm) hh).mpr hnorm.le
    · exact convex_halfSpace_re_gt h
    · exact hw
    · exact hz
  rw [div_eq_mul_inv, mul_comm]
  exact (show |z.arg - w.arg| ≤ ‖Complex.log z - Complex.log w‖ by
    simpa only [Complex.sub_im, Complex.log_im] using
      Complex.abs_im_le_norm (Complex.log z - Complex.log w)).trans hlog

private theorem twoSaddle_re_gt {h : ℝ} (hh : 0 < h) :
    h < (2 * saddleS (Real.exp (h / 2))).re := by
  have h₁ : 1 ≤ Real.exp (h / 2) := Real.one_le_exp (by positivity)
  have hp := mid_log_lt_saddleRe h₁
  rw [Real.log_exp] at hp
  norm_num [Complex.mul_re]
  linarith

/-- The exact comparison of the squares, using the dilogarithm inversion on its specified branch. -/
theorem twoSaddle_sq_eq_outerRho (h : ℝ) :
    (2 * saddleS (Real.exp (h / 2))) ^ 2 =
      outerRho h π ^ 2 + 8 * principalDilog ((Real.exp (-h / 2) : ℂ) * I) := by
  rw [mul_pow, saddleS_sq_inv_radius (Real.exp_pos _), Real.log_exp, outerRho, outerRhoAt_sq,
    show -h / 2 = -(h / 2) by ring, Real.exp_neg]
  push_cast
  ring

/-- The norm comparison on the two positive-real-part branches from page 52. -/
theorem norm_twoSaddle_sub_outerRho_le {h : ℝ} (hh : 0 < h) :
    ‖2 * saddleS (Real.exp (h / 2)) - outerRho h π‖ ≤
      4 * Real.exp (-h / 2) / (h * (1 - Real.exp (-h / 2))) := by
  let z := 2 * saddleS (Real.exp (h / 2))
  let w := outerRho h π
  let ε := Real.exp (-h / 2)
  have he₀ : 0 < ε := Real.exp_pos _
  have he : ε < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hre : 2 * h ≤ (z + w).re := by
    rw [Complex.add_re]
    linarith only [twoSaddle_re_gt hh, outerRho_re_gt (t := π) hh]
  have hnorm : 2 * h ≤ ‖z + w‖ := hre.trans (Complex.re_le_norm _)
  have hden : 0 < h * (1 - ε) := mul_pos hh (sub_pos.mpr he)
  have hD : ‖principalDilog ((ε : ℂ) * I)‖ ≤ ε / (1 - ε) := by
    have hn : ‖(ε : ℂ) * I‖ = ε := by simp [Complex.norm_real, abs_of_pos he₀]
    simpa only [hn] using (norm_principalDilog_le_geom (z := (ε : ℂ) * I) (by rw [hn]; exact he))
  have hprod : ‖z - w‖ * ‖z + w‖ ≤ 8 * (ε / (1 - ε)) := by
    rw [← norm_mul, show (z - w) * (z + w) = z ^ 2 - w ^ 2 by ring]
    change ‖(2 * saddleS (Real.exp (h / 2))) ^ 2 - outerRho h π ^ 2‖ ≤ _
    rw [twoSaddle_sq_eq_outerRho, add_sub_cancel_left, norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hD (by norm_num)
  have h₂ := (mul_le_mul_of_nonneg_left hnorm (norm_nonneg (z - w))).trans hprod
  change ‖z - w‖ ≤ 4 * ε / (h * (1 - ε))
  apply (le_div_iff₀ hden).mpr
  have h₃ := mul_le_mul_of_nonneg_right h₂ (sub_nonneg.mpr he.le)
  rw [show (8 * (ε / (1 - ε))) * (1 - ε) = 8 * ε by
    field_simp [sub_ne_zero.mpr he.ne']] at h₃
  linarith only [h₃]

theorem arg_saddle_sub_outerRho_le {h : ℝ} (hh : 0 < h) :
    |(saddleS (Real.exp (h / 2))).arg - (outerRho h π).arg| ≤
      4 * Real.exp (-h / 2) / (h ^ 2 * (1 - Real.exp (-h / 2))) := by
  have ha : (2 * saddleS (Real.exp (h / 2))).arg = (saddleS (Real.exp (h / 2))).arg := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.arg_real_mul (saddleS (Real.exp (h / 2))) (r := 2) (by norm_num)
  rw [← ha]
  refine (abs_arg_sub_le_of_re_gt hh (twoSaddle_re_gt hh) (outerRho_re_gt hh)).trans ?_
  calc
    _ ≤ (4 * Real.exp (-h / 2) / (h * (1 - Real.exp (-h / 2)))) / h :=
      div_le_div_of_nonneg_right (norm_twoSaddle_sub_outerRho_le hh) hh.le
    _ = _ := by
      rw [div_div]
      congr 1
      ring

theorem saddlePhase_exp_half_eq (n : ℕ) (h : ℝ) :
    saddlePhase n (Real.exp (h / 2)) =
      Real.sqrt n * (2 * saddleS (Real.exp (h / 2))).im +
      (saddleS (Real.exp (h / 2))).arg - Real.arctan (Real.exp (-h / 2)) / 2 := by
  rw [show -h / 2 = -(h / 2) by ring, Real.exp_neg,
    Real.arctan_inv_of_pos (Real.exp_pos _)]
  unfold saddlePhase
  norm_num [Complex.mul_im]
  ring

private theorem outerLogEighty_sharp : (4.38202663 : ℝ) < Real.log 80 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
  dyadic_interval +kernel [prec := 52]

private def phaseThreshold : ℝ := 8.76405326

private theorem outerPhaseBudget {y Y h ε : ℝ} (hy : 80 ≤ y) (hY : 0 ≤ Y)
    (hY₂ : Y ^ 2 = y ^ 2 + 1 / 12) (hh : 2 * Real.log y ≤ h)
    (he : ε ≤ 1 / y) :
    Y * (4 * ε / (h * (1 - ε))) + (Y - y) * π +
      4 * ε / (h ^ 2 * (1 - ε)) + ε / 2 < 0.470736 := by
  have hy₀ : 0 < y := by linarith
  have hhy : phaseThreshold ≤ h := by
    have hh₁ := outerLogEighty_sharp.trans_le (Real.log_le_log (by norm_num) hy)
    dsimp only [phaseThreshold]
    linarith only [hh, hh₁]
  have hh₀ : 0 < h := (by norm_num [phaseThreshold] : 0 < phaseThreshold).trans_le hhy
  have hE : ε ≤ 1 / 80 := he.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) hy)
  have hgap : Y - y ≤ 1 / (24 * y) := by
    rw [le_div_iff₀ (by positivity : 0 < 24 * y)]
    nlinarith only [hY₂, sq_nonneg (Y - y)]
  have hgap₈₀ : Y - y ≤ 1 / 1920 := hgap.trans
    (div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith only [hy]))
  have hYqy : Y / y ≤ 1.000006511 := by
    have hm : (1 / 1920 : ℝ) ≤ 0.000006511 * y := by linarith only [hy]
    exact (div_le_iff₀ hy₀).mpr (by linarith only [hgap₈₀, hm])
  have hYE : Y * ε ≤ 1.000006511 := by
    exact (mul_le_mul_of_nonneg_left he hY).trans (by simpa only [one_div, div_eq_mul_inv, one_mul] using hYqy)
  have hden : phaseThreshold * (1 - 1 / 80) ≤ h * (1 - ε) :=
    mul_le_mul hhy (by linarith only [hE]) (by norm_num) hh₀.le
  have hden₂ : phaseThreshold ^ 2 * (1 - 1 / 80) ≤ h ^ 2 * (1 - ε) :=
    mul_le_mul (pow_le_pow_left₀ (by norm_num [phaseThreshold]) hhy 2)
      (by linarith only [hE]) (by norm_num) (sq_nonneg h)
  have h₁ : Y * (4 * ε / (h * (1 - ε))) ≤
      4 * 1.000006511 / (phaseThreshold * (1 - 1 / 80)) := by
    rw [← mul_div_assoc, show Y * (4 * ε) = 4 * (Y * ε) by ring]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hYE (by norm_num))
      (by norm_num [phaseThreshold]) hden
  have h₂ : (Y - y) * π ≤ 3.141593 / 1920 := by
    calc
      _ ≤ (1 / 1920 : ℝ) * 3.141593 := mul_le_mul hgap₈₀ Real.pi_lt_d6.le pi_pos.le (by norm_num)
      _ = _ := by ring
  have h₃ : 4 * ε / (h ^ 2 * (1 - ε)) ≤ 4 / (80 * phaseThreshold ^ 2 * (1 - 1 / 80)) := by
    calc
      _ ≤ (4 * (1 / 80)) / (phaseThreshold ^ 2 * (1 - 1 / 80)) :=
        div_le_div₀ (by norm_num) (mul_le_mul_of_nonneg_left hE (by norm_num))
          (by norm_num [phaseThreshold]) hden₂
      _ = _ := by norm_num [phaseThreshold]
  have h₄ : ε / 2 ≤ 1 / 160 := by linarith only [hE]
  unfold phaseThreshold at h₁ h₃
  linarith only [h₁, h₂, h₃, h₄]

/-- Uniform comparison of the actual saddle phase with the outer phase in Corollary 4.4. -/
theorem saddlePhase_outerPhase_lt {n : ℕ} {h : ℝ} (hn : 6401 ≤ n)
    (hh : 2 * Real.log (Real.sqrt ((n : ℝ) - 1 / 12)) ≤ h) :
    |saddlePhase n (Real.exp (h / 2)) -
      (Real.sqrt ((n : ℝ) - 1 / 12) * (outerRho h π).im + (outerRho h π).arg)| <
      0.470736 := by
  let y := Real.sqrt ((n : ℝ) - 1 / 12)
  let Y := Real.sqrt (n : ℝ)
  let z := 2 * saddleS (Real.exp (h / 2))
  let w := outerRho h π
  let ε := Real.exp (-h / 2)
  have hn₁ : (6401 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 80 ≤ y := Real.le_sqrt_of_sq_le (by linarith)
  have hy₀ : 0 < y := by linarith
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hy₂ : y ^ 2 = (n : ℝ) - 1 / 12 := Real.sq_sqrt (by linarith)
  have hY₂ : Y ^ 2 = y ^ 2 + 1 / 12 := by
    rw [hy₂, Real.sq_sqrt (by positivity)]
    ring
  have hYy : y ≤ Y := Real.sqrt_le_sqrt (by norm_num)
  have hh₀ : 0 < h := (mul_pos (by norm_num : (0 : ℝ) < 2)
    (Real.log_pos (by linarith : 1 < y))).trans_le hh
  have hε₀ : 0 < ε := Real.exp_pos _
  have hε : ε ≤ 1 / y := by
    rw [one_div, ← Real.exp_log hy₀, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith only [hh])
  have him : |z.im - w.im| ≤ 4 * ε / (h * (1 - ε)) := by
    have hb := (Complex.abs_im_le_norm (z - w)).trans (norm_twoSaddle_sub_outerRho_le hh₀)
    simpa only [Complex.sub_im] using hb
  have ha : |(saddleS (Real.exp (h / 2))).arg - w.arg| ≤ 4 * ε / (h ^ 2 * (1 - ε)) :=
    arg_saddle_sub_outerRho_le hh₀
  have hw : |w.im| ≤ π := by
    rw [abs_of_pos (outerRho_im_pi_pos hh₀)]
    exact (outerRho_im_pi_lt hh₀).le
  have ht : |Real.arctan ε / 2| ≤ ε / 2 := by
    rw [abs_of_nonneg (div_nonneg (Real.arctan_nonneg.mpr hε₀.le) (by norm_num))]
    exact div_le_div_of_nonneg_right (Real.arctan_lt_self hε₀).le (by norm_num)
  rw [saddlePhase_exp_half_eq]
  change |Y * z.im + (saddleS (Real.exp (h / 2))).arg - Real.arctan ε / 2 -
    (y * w.im + w.arg)| < 0.470736
  rw [show Y * z.im + (saddleS (Real.exp (h / 2))).arg - Real.arctan ε / 2 -
      (y * w.im + w.arg) =
      Y * (z.im - w.im) + (Y - y) * w.im +
        ((saddleS (Real.exp (h / 2))).arg - w.arg) - Real.arctan ε / 2 by ring]
  calc
    _ ≤ |Y * (z.im - w.im)| + |(Y - y) * w.im| +
        |(saddleS (Real.exp (h / 2))).arg - w.arg| + |Real.arctan ε / 2| := by
      have hb : |Y * (z.im - w.im) + (Y - y) * w.im +
          ((saddleS (Real.exp (h / 2))).arg - w.arg) - Real.arctan ε / 2| ≤
          |Y * (z.im - w.im) + (Y - y) * w.im +
            ((saddleS (Real.exp (h / 2))).arg - w.arg)| + |Real.arctan ε / 2| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (Y * (z.im - w.im) + (Y - y) * w.im +
            ((saddleS (Real.exp (h / 2))).arg - w.arg)) (-(Real.arctan ε / 2))
      refine hb.trans ?_
      gcongr
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Y * (4 * ε / (h * (1 - ε))) + (Y - y) * π +
        4 * ε / (h ^ 2 * (1 - ε)) + ε / 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hY, abs_of_nonneg (sub_nonneg.mpr hYy)]
      gcongr
    _ < _ := outerPhaseBudget hy hY hY₂ hh hε

end DurfeeCCS.Step10
