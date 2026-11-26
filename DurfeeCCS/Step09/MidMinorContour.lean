module

public import DurfeeCCS.Step09.MidMinorBudget
public import DurfeeCCS.Step09.MidContourDefs
public import DurfeeCCS.Step09.MidMultiplierRadius
public import DurfeeCCS.Step09.MidOtherGaussian
public import DurfeeCCS.Step06.DurfeePairedAngle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Reduction of the smaller arcs to the individual certified rows in (64). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

theorem midMinorModeBudget_le_actual_row {n : ℕ} {r v : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (i : Fin 18)
    (hl : ((minorArcData i).left : ℝ) ≤ Real.log r)
    (hh : i.val < 17 → Real.log r ≤ ((minorArcData i).right : ℝ))
    (hv : 8 * midU n r ≤ |v|) (hv' : |v| ≤ Real.pi) :
    midMinorModeBudget (midU n r) (Real.log r) v ≤ minorArcQstarRow i := by
  let u := midU n r
  have hn₀ : 0 < n := by omega
  have hr₀ : 0 < r := by linarith
  have ht := Real.log_nonneg hr
  have hu : 0 < u := saddleU_pos hn₀ hr₀
  have hu' : u ≤ 0.072 := (midU_lt_072 hn hr hmax).le
  have hP : (80 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hyl : u ≤ (minorArcYmax (minorArcData i) : ℝ) := by
    unfold minorArcYmax
    rw [Rat.cast_min]
    apply le_min (by simpa using hu')
    by_cases hi : i.val < 17
    · have hR : r ≤ Real.exp ((minorArcData i).right : ℝ) := by
        rw [← Real.exp_log hr₀]
        exact Real.exp_le_exp.mpr (hh hi)
      have ha := (monotoneOn_saddleS_re hr₀ (Real.exp_pos _) hR).trans
        (minorArc_row_amplitude_endpoint i hi)
      have h := div_le_div₀ (show 0 ≤ ((minorArcData i).amplitude : ℝ) from
        ((saddleS_components hr₀).1.trans (saddleS_components hr₀).2).le.trans ha)
        ha (by norm_num : (0:ℝ) < 80) hP
      simpa only [u,midU,saddleU,Rat.cast_div,Rat.cast_ofNat] using h
    · have hi' : i = 17 := Fin.ext (by omega)
      subst i
      norm_num [minorArcData, Rat.cast_ofScientific]
      linarith only [hu']
  apply midMinorModeBudget_le_row hu ht i ?_ ?_ hyl hv hv'
  · split_ifs with hi
    · exact Real.exp_le_exp.mpr (by linarith only [hh hi])
    · exact Real.exp_nonneg _
  · exact Real.exp_le_exp.mpr (by linarith only [hl])

private theorem norm_two_pi_inv :
    ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv, show (2*Real.pi:ℂ) = ↑((2:ℝ)*Real.pi) by push_cast; rfl,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]

private theorem norm_durfeeAnalyticF_le_uniform {r u v C : ℝ} (hu : 0 < u)
    (h : ∀ θ : ℝ, ‖pairedProduct r θ (verticalPoint u v)‖ ≤ C) :
    ‖durfeeAnalyticF (-(r:ℂ)^2) (exp (-verticalPoint u v))‖ ≤ C := by
  rw [durfeeAnalyticF_eq_pairedAngle r (by simpa using hu), norm_mul, norm_two_pi_inv]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi)
    (b := Real.pi) (C := C) (f := fun θ => pairedProduct r θ (verticalPoint u v))
    (fun θ _ => h θ)
  rw [sub_neg_eq_add,← two_mul,abs_of_pos (by positivity)] at hI
  calc
    _ ≤ (2*Real.pi)⁻¹ * (C*(2*Real.pi)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by field_simp

private theorem midMinor_norm_arc_of_pointwise {n : ℕ} {r C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v : ℝ, 8 * midU n r ≤ |v| → |v| ≤ Real.pi → ‖midDurfeeLine n r v‖ ≤ C) :
    ‖midOuterContribution n r‖ ≤ C := by
  let s := Icc (-Real.pi) Real.pi \ Ioo (-(8*midU n r)) (8*midU n r)
  have hs : s ⊆ Icc (-Real.pi) Real.pi := sdiff_subset
  have hπ : volume (Icc (-Real.pi) Real.pi) < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hV := (measure_mono hs).trans_lt hπ
  have hVs : volume.real s ≤ 2*Real.pi := by
    have hv := ENNReal.toReal_mono hπ.ne (measure_mono hs)
    change volume.real s ≤ volume.real (Icc (-Real.pi) Real.pi) at hv
    rw [Real.volume_real_Icc_of_le (by linarith [Real.pi_pos]),sub_neg_eq_add,← two_mul] at hv
    exact hv
  have hI := norm_setIntegral_le_of_norm_le_const (f := midDurfeeLine n r) hV (C := C)
      (fun v hv => h v (le_of_not_gt (fun hlt => hv.2 (abs_lt.mp hlt))) (abs_le.mpr hv.1))
  rw [midOuterContribution, norm_mul, norm_two_pi_inv]
  change (2*Real.pi)⁻¹ * ‖∫ v in s, midDurfeeLine n r v‖ ≤ C
  calc
    _ ≤ (2*Real.pi)⁻¹*(C*volume.real s) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ ≤ (2*Real.pi)⁻¹*(C*(2*Real.pi)) := by gcongr
    _ = _ := by field_simp

theorem midMinor_normalized_bound {n : ℕ} {r q : ℝ} (hn : 6400 ≤ n) (hr : 1 ≤ r)
    (hmax : r ≤ Real.exp 1 * Real.sqrt (n:ℝ))
    (hP : ∀ v : ℝ, 8 * midU n r ≤ |v| → |v| ≤ Real.pi → ∀ θ : ℝ,
      ‖pairedProduct r θ (verticalPoint (midU n r) v)‖ ≤
        Real.exp ((Real.log r^2 + q) / midU n r)) :
    ‖midOuterContribution n r‖ / saddleAmplitude n r ≤
      2*Real.pi*n*Real.exp (-Real.sqrt n * (minorArcSaddleGap (Real.log r) - q) / (saddleS r).re) := by
  let a := (saddleS r).re
  let u := midU n r
  let x := Real.sqrt (n:ℝ)
  let K := -x * (minorArcSaddleGap (Real.log r) - q) / a
  have hn₀ : 0 < n := by omega
  have hr₀ : 0 < r := by linarith
  have ha : 1 < a := (midSaddle_data hn hr hmax).1
  have ha₀ : 0 < a := zero_lt_one.trans ha
  have hm := saddleAmplitude_pos hn₀ hr₀
  have hx : 0 < x := by dsimp [x]; positivity
  have hu : 0 < u := saddleU_pos hn₀ hr₀
  have hf (v : ℝ) (hv : 8*u ≤ |v|) (hv' : |v| ≤ Real.pi) :
      ‖midDurfeeLine n r v‖ ≤ Real.exp (2*midOmega n r)*Real.exp K := by
    have hF := norm_durfeeAnalyticF_le_uniform hu (hP v hv hv')
    unfold midDurfeeLine
    dsimp only
    rw [norm_mul,norm_exp_nat_verticalPoint,saddleU_mul_n hn₀]
    refine (mul_le_mul_of_nonneg_left hF (Real.exp_nonneg _)).trans_eq ?_
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have hgap : minorArcSaddleGap (Real.log r) = a^2 - Real.log r^2 := by
      rw [minorArcSaddleGap,Real.exp_log hr₀]
    rw [show K = -x * (minorArcSaddleGap (Real.log r) - q) / a from rfl,hgap]
    change a*x + (Real.log r^2+q)/(a/x) = 2*(a*x)+-x*(a^2-Real.log r^2-q)/a
    field_simp
    ring
  have hA := saddleAmplitude_gt_mid hn₀ hr₀
  have he₁ : Real.exp (2*midOmega n r) ≤ a*Real.exp (2*midOmega n r) :=
    le_mul_of_one_le_left (Real.exp_nonneg _) ha.le
  have he : Real.exp (2*midOmega n r) / saddleAmplitude n r ≤ 2*Real.pi*n := by
    apply (div_le_iff₀ hm).mpr
    have hh := (div_lt_iff₀ (show 0 < 2*Real.pi*(n:ℝ) by positivity)).mp hA
    exact he₁.trans (by simpa [mul_comm] using hh.le)
  calc
    _ ≤ (Real.exp (2*midOmega n r)*Real.exp K) / saddleAmplitude n r :=
      div_le_div_of_nonneg_right (midMinor_norm_arc_of_pointwise (by positivity) hf) hm.le
    _ = (Real.exp (2*midOmega n r) / saddleAmplitude n r) * Real.exp K := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)

/-- The angle and parameter estimates after (64), applied to a bound on the actual product. -/
theorem lemma39_of_modeEnvelope {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n:ℝ))
    (hP : ∀ v θ : ℝ, ‖pairedProduct r θ (verticalPoint (midU n r) v)‖ ≤
      Real.exp ((Real.log r^2 + midMinorModeBudget (midU n r) (Real.log r) v) / midU n r)) :
    ‖midOuterContribution n r‖ < 0.05 * saddleAmplitude n r := by
  let t := Real.log r
  let M := saddleAmplitude n r
  let x := Real.sqrt (n:ℝ)
  have hX : 80 ≤ x := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hX₀ : 0 < x := (by norm_num : (0:ℝ)<80).trans_le hX
  have hM : 0 < M := saddleAmplitude_pos (by omega) (by linarith)
  have hr₀ : 0 < r := by linarith
  have ht : 0 ≤ t := Real.log_nonneg hr
  have hU : 0 < midU n r := saddleU_pos (by omega) hr₀
  have hq (i : Fin 18) (hl : ((minorArcData i).left : ℝ) ≤ t)
      (hh : i.val < 17 → t ≤ ((minorArcData i).right : ℝ)) :
      ‖midOuterContribution n r‖ / M ≤
        2*Real.pi*x^2*Real.exp (-x*(minorArcSaddleGap t - minorArcQstarRow i)/(saddleS (Real.exp t)).re) := by
    have hB := midMinor_normalized_bound hn hr hmax (q := minorArcQstarRow i) (fun v hv hv' θ =>
      (hP v θ).trans (Real.exp_le_exp.mpr
        (div_le_div_of_nonneg_right (add_le_add_right
          (midMinorModeBudget_le_actual_row hn hr hmax i hl hh hv hv') _) hU.le)))
    change _ ≤ _
    have hXsq : x^2 = (n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    rw [hXsq, show Real.exp t = r from Real.exp_log hr₀]
    exact hB
  apply (div_lt_iff₀ hM).mp
  by_cases h6 : t ≤ 6
  · obtain ⟨i,hi,hl,hh⟩ := minorArc_rows_cover ht h6
    exact (minorArc_first_error_of_gap hX (minorArc_row_gap i hi hl hh).le
      (hq i hl (fun _ => hh))).trans (by norm_num)
  · have h6' : 6 ≤ t := (lt_of_not_ge h6).le
    have htx : t ≤ Real.log x + 1 := by
      have h := Real.log_le_log hr₀ hmax
      rwa [Real.log_mul (Real.exp_ne_zero _) hX₀.ne', Real.log_exp, add_comm] at h
    have hi : minorArcQstarRow 17 < 1.593 := by
      simpa [minorArcData, Rat.cast_ofScientific] using minorArcQstarRow_lt 17
    exact (minorArc_second_error_of_gap hX h6' htx hi
      (hq 17 (by simpa [minorArcData] using h6') (fun h => by norm_num at h))).trans (by norm_num)

end DurfeeCCS.Step09
