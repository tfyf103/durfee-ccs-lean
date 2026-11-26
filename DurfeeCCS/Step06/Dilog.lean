module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The principal dilogarithm from its straight-segment integral. -/

@[expose] public section

namespace DurfeeCCS.Step06

open Complex Filter MeasureTheory Set
open scoped Interval Topology Real

/-- The complement of the principal dilogarithm cut `[1, ∞)`. -/
def dilogCut : Set ℂ := {z | 1 - z ∈ Complex.slitPlane}

theorem isOpen_dilogCut : IsOpen dilogCut :=
  Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)

theorem mem_dilogCut_iff {z : ℂ} : z ∈ dilogCut ↔ z.re < 1 ∨ z.im ≠ 0 := by
  simp [dilogCut, Complex.mem_slitPlane_iff, sub_pos]

theorem mem_dilogCut_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : z ∈ dilogCut :=
  mem_dilogCut_iff.mpr (Or.inl ((Complex.re_le_norm z).trans_lt hz))

theorem dilogCut_ne_one {z : ℂ} (hz : z ∈ dilogCut) : z ≠ 1 := by
  intro heq
  simp [dilogCut, heq] at hz

theorem one_sub_scaled_mem_slitPlane {z : ℂ} (hz : z ∈ dilogCut) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
  rcases eq_or_lt_of_le ht.1 with rfl | htp
  · simp
  rcases mem_dilogCut_iff.mp hz with h | h
  · apply Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact sub_pos.mpr ((mul_lt_mul_of_pos_left h htp).trans_le (by simpa using ht.2))
  · apply Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    simpa [Complex.mul_im, Complex.sub_im] using mul_ne_zero htp.ne' h

/-- The regularized logarithmic integrand on the straight segment from `0` to `z`. -/
noncomputable def dilogKernel (z : ℂ) (t : ℝ) : ℂ :=
  if t = 0 then z else -Complex.log (1 - (t : ℂ) * z) / (t : ℂ)

/-- Principal-branch dilogarithm, defined by the segment integral on `dilogCut`. -/
noncomputable def principalDilog (z : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, dilogKernel z t

@[simp] theorem principalDilog_zero : principalDilog 0 = 0 := by
  simp [principalDilog, dilogKernel]

private theorem hasDerivAt_negLogSegment {z : ℂ} {t : ℝ}
    (ht : 1 - (t : ℂ) * z ∈ Complex.slitPlane) :
    HasDerivAt (fun s : ℝ => -Complex.log (1 - (s : ℂ) * z))
      (z * (1 - (t : ℂ) * z)⁻¹) t := by
  have h := Complex.ofRealCLM.hasDerivAt (x := t)
  have hh := ((h.mul_const z).const_sub 1).clog_real ht
  have hneg : HasDerivAt (fun s : ℝ => -Complex.log (1 - (s : ℂ) * z)) _ t := hh.neg
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, neg_div, neg_mul,
    neg_neg, div_eq_mul_inv] using hneg

private theorem dilogKernel_eq_dslope (z : ℂ) :
    dilogKernel z = dslope (fun s : ℝ => -Complex.log (1 - (s : ℂ) * z)) 0 := by
  funext t
  by_cases ht : t = 0
  · subst t
    have h := hasDerivAt_negLogSegment (z := z) (t := 0) (by simp)
    rw [dilogKernel, ite_eq_left rfl, dslope_same, h.deriv]
    simp
  · rw [dilogKernel, ite_eq_right ht, dslope_of_ne _ ht, slope_def_module]
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem continuousOn_dilogKernel {z : ℂ} (hz : z ∈ dilogCut) :
    ContinuousOn (dilogKernel z) (Icc (0 : ℝ) 1) := by
  rw [dilogKernel_eq_dslope]
  intro t ht
  by_cases h : t = 0
  · subst t
    have hd := hasDerivAt_negLogSegment (z := z) (t := 0) (by simp)
    exact (continuousAt_dslope_same.2 hd.differentiableAt).continuousWithinAt
  · apply (continuousWithinAt_dslope_of_ne h).2
    exact (hasDerivAt_negLogSegment (one_sub_scaled_mem_slitPlane hz ht)).continuousAt.continuousWithinAt

theorem intervalIntegrable_dilogKernel {z : ℂ} (hz : z ∈ dilogCut) :
    IntervalIntegrable (dilogKernel z) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa [uIcc_of_le zero_le_one] using continuousOn_dilogKernel hz

private theorem hasDerivAt_dilogKernel {z : ℂ} (hz : z ∈ dilogCut) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun w => dilogKernel w t) (1 - (t : ℂ) * z)⁻¹ z := by
  by_cases heq : t = 0
  · subst t
    have h : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
    simpa [dilogKernel] using h
  simp only [dilogKernel, ite_eq_right heq]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast heq
  have h := (((hasDerivAt_id z).const_mul (t : ℂ)).const_sub 1).clog
    (one_sub_scaled_mem_slitPlane hz ht)
  convert h.neg.div_const (t : ℂ) using 1 <;> simp
  field_simp

private theorem integral_hasDerivAt_principalDilog {z : ℂ} (hz : z ∈ dilogCut) :
    HasDerivAt principalDilog (∫ t in (0 : ℝ)..1, (1 - (t : ℂ) * z)⁻¹) z := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (isOpen_dilogCut.mem_nhds hz)
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hclosed : Metric.closedBall z ε ⊆ dilogCut :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball
  let K := Metric.closedBall z ε ×ˢ Icc (0 : ℝ) 1
  let f : ℂ × ℝ → ℝ := fun wt => ‖1 - (wt.2 : ℂ) * wt.1‖
  have hK : IsCompact K := (isCompact_closedBall z ε).prod isCompact_Icc
  have hzK : (z, (0 : ℝ)) ∈ K := by simp [K, hε.le]
  have hf : Continuous f := by fun_prop
  obtain ⟨wt, hwt, hwmin⟩ := hK.exists_isMinOn ⟨(z, 0), hzK⟩ hf.continuousOn
  have hpos : 0 < f wt :=
    norm_pos_iff.mpr (Complex.slitPlane_ne_zero (one_sub_scaled_mem_slitPlane (hclosed hwt.1) hwt.2))
  have hne (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1 - (t : ℂ) * z ≠ 0 :=
    Complex.slitPlane_ne_zero (one_sub_scaled_mem_slitPlane hz ht)
  have hcont : ContinuousOn (fun t : ℝ => (1 - (t : ℂ) * z)⁻¹) (Icc 0 1) :=
    (show ContinuousOn (fun t : ℝ => 1 - (t : ℂ) * z) (Icc 0 1) by fun_prop).inv₀ hne
  have haU : uIoc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc (a := (0 : ℝ)) (b := 1))
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := dilogKernel) (F' := fun w t => (1 - (t : ℂ) * w)⁻¹)
    (bound := fun _ => (f wt)⁻¹) (Metric.closedBall_mem_nhds z hε) ?_
    (intervalIntegrable_dilogKernel hz) ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [Metric.closedBall_mem_nhds z hε] with w hw
    exact ((continuousOn_dilogKernel (hclosed hw)).mono haU).aestronglyMeasurable measurableSet_uIoc
  · exact (hcont.mono haU).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [] with t ht w hw
    have hle : f wt ≤ f (w, t) := hwmin ⟨hw, haU ht⟩
    rw [norm_inv]
    exact (inv_le_inv₀ (hpos.trans_le hle) hpos).2 hle
  · filter_upwards [] with t ht w hw
    exact hasDerivAt_dilogKernel (hclosed hw) (haU ht)

theorem hasDerivAt_principalDilog {z : ℂ} (hz : z ∈ dilogCut) :
    HasDerivAt principalDilog (if z = 0 then 1 else -Complex.log (1 - z) / z) z := by
  have h := integral_hasDerivAt_principalDilog hz
  by_cases heq : z = 0
  · subst z
    simpa using h
  rw [ite_eq_right heq]
  have hF (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => -Complex.log (1 - (s : ℂ) * z))
        (z * (1 - (t : ℂ) * z)⁻¹) t := by
    exact hasDerivAt_negLogSegment (one_sub_scaled_mem_slitPlane hz (by simpa using ht))
  have hcont : ContinuousOn (fun t : ℝ => (1 - (t : ℂ) * z)⁻¹) (uIcc 0 1) :=
    (show ContinuousOn (fun t : ℝ => 1 - (t : ℂ) * z) (uIcc 0 1) by fun_prop).inv₀
      (fun _ ht => Complex.slitPlane_ne_zero (one_sub_scaled_mem_slitPlane hz (by simpa using ht)))
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (hcont.intervalIntegrable.const_mul z)
  rw [intervalIntegral.integral_const_mul] at heval
  simp at heval
  convert h using 1
  symm
  apply (eq_div_iff heq).2
  simpa [mul_comm] using heval

theorem differentiableOn_principalDilog : DifferentiableOn ℂ principalDilog dilogCut :=
  fun _ hz => (hasDerivAt_principalDilog hz).differentiableAt.differentiableWithinAt

theorem continuousOn_principalDilog : ContinuousOn principalDilog dilogCut :=
  differentiableOn_principalDilog.continuousOn

private theorem zero_mem_dilogCut : (0 : ℂ) ∈ dilogCut := by
  simp [dilogCut]

private theorem isPreconnected_dilogCut : IsPreconnected dilogCut := by
  have h : StarConvex ℝ (0 : ℂ) dilogCut := by
    intro z hz a b ha hb hab
    simp only [smul_zero, zero_add, Complex.real_smul]
    exact one_sub_scaled_mem_slitPlane hz ⟨hb, by linarith⟩
  exact (h.isPathConnected zero_mem_dilogCut).isConnected.isPreconnected

private theorem inv_mem_slitPlane' {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    z⁻¹ ∈ Complex.slitPlane := by
  have hn : z ≠ 0 := Complex.slitPlane_ne_zero hz
  apply Complex.mem_slitPlane_iff.mp at hz
  apply Complex.mem_slitPlane_iff.mpr
  rcases hz with h | h
  · exact Or.inl (by simpa [Complex.inv_re] using div_pos h (Complex.normSq_pos.mpr hn))
  · exact Or.inr (by simp [Complex.inv_im, h, hn])

private theorem log_inv_of_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.log z⁻¹ = -Complex.log z := by
  apply Complex.log_inv
  apply ne_of_lt (Complex.arg_lt_pi_iff.mpr ?_)
  exact (Complex.mem_slitPlane_iff.mp hz).imp le_of_lt id

private theorem one_sub_landenMap {z : ℂ} (hz : z ∈ dilogCut) :
    1 - z / (z - 1) = (1 - z)⁻¹ := by
  have h₁ : z - 1 ≠ 0 := sub_ne_zero.mpr (dilogCut_ne_one hz)
  have h₂ : 1 - z ≠ 0 := sub_ne_zero.mpr (dilogCut_ne_one hz).symm
  field_simp; ring

private theorem landenMap_mem_dilogCut {z : ℂ} (hz : z ∈ dilogCut) :
    z / (z - 1) ∈ dilogCut := by
  change 1 - z / (z - 1) ∈ Complex.slitPlane
  rw [one_sub_landenMap hz]
  exact inv_mem_slitPlane' hz

private theorem hasDerivAt_landenMap {z : ℂ} (hz : z ∈ dilogCut) :
    HasDerivAt (fun w : ℂ => w / (w - 1)) (-((z - 1)^2)⁻¹) z := by
  have h : HasDerivAt (fun w : ℂ => w / (w - 1))
      ((1 * (z - 1) - z * 1) / (z - 1)^2) z :=
    (hasDerivAt_id z).div ((hasDerivAt_id z).sub_const 1)
    (sub_ne_zero.mpr (dilogCut_ne_one hz))
  convert h using 1
  rw [div_eq_mul_inv]
  ring

/-- The principal-branch Landen identity, the first identity in equation (5). -/
theorem principalDilog_landen {z : ℂ} (hz : z ∈ dilogCut) :
    principalDilog z + principalDilog (z / (z - 1)) = -Complex.log (1 - z)^2 / 2 := by
  let f : ℂ → ℂ := fun w => principalDilog w + principalDilog (w / (w - 1))
  let g : ℂ → ℂ := fun w => -Complex.log (1 - w)^2 / 2
  have hf (w : ℂ) (hw : w ∈ dilogCut) :=
    (hasDerivAt_principalDilog hw).add
      ((hasDerivAt_principalDilog (landenMap_mem_dilogCut hw)).comp w (hasDerivAt_landenMap hw))
  have hg (w : ℂ) (hw : w ∈ dilogCut) :=
    ((((hasDerivAt_id w).const_sub 1).clog hw).pow 2).neg.div_const (2 : ℂ)
  have h' : dilogCut.EqOn (deriv f) (deriv g) := by
    intro w hw
    have hf' : deriv f w = _ := (hf w hw).deriv
    have hg' : deriv g w = _ := (hg w hw).deriv
    rw [hf', hg']
    by_cases h₀ : w = 0
    · subst w
      norm_num
    have h₁ : w - 1 ≠ 0 := sub_ne_zero.mpr (dilogCut_ne_one hw)
    have h₂ : 1 - w ≠ 0 := sub_ne_zero.mpr (dilogCut_ne_one hw).symm
    have h₃ : w / (w - 1) ≠ 0 := div_ne_zero h₀ h₁
    simp only [id, ite_eq_right h₀, ite_eq_right h₃, one_sub_landenMap hw, log_inv_of_slitPlane hw]
    field_simp; ring
  apply isOpen_dilogCut.eqOn_of_deriv_eq isPreconnected_dilogCut
    (fun w hw => (hf w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hg w hw).differentiableAt.differentiableWithinAt)
    h' zero_mem_dilogCut (by simp) hz

private noncomputable def dilogIntegrandTerm (z : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n

private theorem continuous_dilogIntegrandTerm (z : ℂ) (n : ℕ) :
    Continuous (dilogIntegrandTerm z n) := by unfold dilogIntegrandTerm; fun_prop

private theorem hasSum_dilogKernel {z : ℂ} (hz : ‖z‖ ≤ 1) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasSum (fun n => dilogIntegrandTerm z n t) (dilogKernel z t) := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
  have hnorm : ‖(t : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
    exact (mul_le_of_le_one_right ht.1.le hz).trans_lt ht.2
  unfold dilogKernel
  rw [ite_eq_right ht.1.ne']
  convert (Complex.hasSum_taylorSeries_neg_log' hnorm).div_const (t : ℂ) using 1
  ext n
  simp [dilogIntegrandTerm, mul_pow, pow_succ]
  field_simp

private theorem integral_real_pow (n : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ n) = 1 / ((n + 1 : ℕ) : ℝ) := by
  rw [integral_pow]
  simp

private theorem integral_dilogIntegrandTerm (z : ℂ) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, dilogIntegrandTerm z n t) =
      z ^ (n + 1) / (((n + 1 : ℕ) : ℂ)^2) := by
  simp only [dilogIntegrandTerm, ← Complex.ofReal_pow, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_ofReal (f := fun t => t ^ n), integral_real_pow,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast, pow_two, ← div_div]
  ring

/-- The paper's series, including the whole closed unit disk. -/
theorem principalDilog_hasSum {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / (((n + 1 : ℕ) : ℂ)^2)) (principalDilog z) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  have hint (n : ℕ) : Integrable (dilogIntegrandTerm z n) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((continuous_dilogIntegrandTerm z n).intervalIntegrable 0 1)
  have hnorm (n : ℕ) :
      (∫ t, ‖dilogIntegrandTerm z n t‖ ∂μ) = ‖z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)‖ /
        ((n + 1 : ℕ) : ℝ) := by
    calc
      _ = ∫ t in Ioc (0 : ℝ) 1, ‖z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)‖ * t ^ n := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        simp [dilogIntegrandTerm, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
      _ = _ := by
        rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
          integral_real_pow]
        ring
  have hsummable : Summable fun n : ℕ => ∫ t, ‖dilogIntegrandTerm z n t‖ ∂μ := by
    apply ((summable_nat_add_iff 1).mpr hasSum_zeta_two.summable).of_nonneg_of_le
    · exact fun n => integral_nonneg (fun _ => norm_nonneg _)
    · intro n
      rw [hnorm, norm_div, norm_pow, Complex.norm_natCast, pow_two, ← div_div]
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg z) hz) (by positivity))
        (by positivity)
  have hsum := hasSum_integral_of_summable_integral_norm hint hsummable
  convert hsum using 1
  · funext n
    rw [← integral_dilogIntegrandTerm, intervalIntegral.integral_of_le zero_le_one]
  · rw [principalDilog, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    change _ = ∫ t in Ioc (0 : ℝ) 1, ∑' n, dilogIntegrandTerm z n t
    rw [integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo (fun t ht => (hasSum_dilogKernel hz ht).tsum_eq.symm)

theorem principalDilog_one : principalDilog 1 = (π : ℂ)^2 / 6 := by
  apply HasSum.unique (principalDilog_hasSum (z := 1) (by simp))
  have h : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)^2) (π^2 / 6) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^2) 1).mpr
    simpa using hasSum_zeta_two
  simpa using Complex.ofRealCLM.hasSum h

theorem principalDilog_neg_one : principalDilog (-1) = -(π : ℂ)^2 / 12 := by
  let f : ℕ → ℂ := fun n => 1 / (n : ℂ)^2
  let g : ℕ → ℂ := fun n => (-1 : ℂ)^n / (n : ℂ)^2
  let c : ℂ := (π : ℂ)^2 / 6
  have hf : HasSum f c := by
    simpa [f, c] using Complex.ofRealCLM.hasSum hasSum_zeta_two
  have hg : HasSum g (principalDilog (-1)) := by
    have h := (hasSum_nat_add_iff (f := g) 1).mp (principalDilog_hasSum (z := -1) (by simp))
    simpa [g] using h
  have he : HasSum (fun n => f (2 * n)) (c / 4) := by
    convert hf.div_const (4 : ℂ) using 1
    funext n
    simp only [f, Nat.cast_mul, Nat.cast_ofNat, mul_pow, div_div]
    congr 1
    ring
  have ho : Summable (fun n => f (2 * n + 1)) :=
    hf.summable.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  have hge : (fun n => g (2 * n)) = fun n => f (2 * n) := by
    funext n
    simp only [f, g, even_two, Even.mul_right, Even.neg_pow, one_pow]
  have hgo : (fun n => g (2 * n + 1)) = fun n => -f (2 * n + 1) := by
    funext n
    simp only [f, g, pow_add, even_two, Even.mul_right, Even.neg_pow, one_pow, pow_one,
      one_mul, neg_div]
  have hes : Summable (fun n => g (2 * n)) := hge ▸ he.summable
  have hos : Summable (fun n => g (2 * n + 1)) := hgo ▸ ho.neg
  have hbase := tsum_even_add_odd he.summable ho
  have halt := tsum_even_add_odd hes hos
  rw [hf.tsum_eq, he.tsum_eq] at hbase
  rw [hg.tsum_eq, hge, hgo, tsum_neg, he.tsum_eq] at halt
  calc
    principalDilog (-1) = c / 4 + -(∑' n, f (2 * n + 1)) := halt.symm
    _ = 2 * (c / 4) - (c / 4 + ∑' n, f (2 * n + 1)) := by ring
    _ = _ := by rw [hbase]; dsimp [c]; ring

/-- The complement of the inversion identity's cut `[0, ∞)`. -/
def dilogInvCut : Set ℂ := {z | -z ∈ Complex.slitPlane}

theorem mem_dilogInvCut_iff {z : ℂ} : z ∈ dilogInvCut ↔ z.re < 0 ∨ z.im ≠ 0 := by
  simp [dilogInvCut, Complex.mem_slitPlane_iff]

private theorem isOpen_dilogInvCut : IsOpen dilogInvCut :=
  Complex.isOpen_slitPlane.preimage continuous_neg

private theorem neg_one_mem_dilogInvCut : (-1 : ℂ) ∈ dilogInvCut := by
  simp [dilogInvCut]

private theorem isPreconnected_dilogInvCut : IsPreconnected dilogInvCut := by
  have h : StarConvex ℝ (-1 : ℂ) dilogInvCut := by
    intro z hz a b ha hb hab
    change -(a • (-1 : ℂ) + b • z) ∈ Complex.slitPlane
    rw [neg_add, ← smul_neg, ← smul_neg, neg_neg]
    exact Complex.starConvex_one_slitPlane hz ha hb hab
  exact (h.isPathConnected neg_one_mem_dilogInvCut).isConnected.isPreconnected

private theorem dilogInvCut_ne_zero {z : ℂ} (hz : z ∈ dilogInvCut) : z ≠ 0 := by
  intro h
  simp [dilogInvCut, h] at hz

private theorem dilogInvCut_subset : dilogInvCut ⊆ dilogCut := by
  intro z hz
  exact mem_dilogCut_iff.mpr ((mem_dilogInvCut_iff.mp hz).imp (fun h => h.trans zero_lt_one) id)

private theorem inv_mem_dilogInvCut {z : ℂ} (hz : z ∈ dilogInvCut) : z⁻¹ ∈ dilogInvCut := by
  change -z⁻¹ ∈ Complex.slitPlane
  rw [← inv_neg]
  exact inv_mem_slitPlane' hz

private theorem log_sub_log_inv {z : ℂ} (hz : z ∈ dilogInvCut) :
    Complex.log (1 - z) - Complex.log (1 - z⁻¹) = Complex.log (-z) := by
  let f : ℂ → ℂ := fun w => Complex.log (1 - w) - Complex.log (1 - w⁻¹)
  let g : ℂ → ℂ := fun w => Complex.log (-w)
  have hf (w : ℂ) (hw : w ∈ dilogInvCut) :=
    (((hasDerivAt_id w).const_sub 1).clog (dilogInvCut_subset hw)).sub
      ((((hasDerivAt_id w).inv (dilogInvCut_ne_zero hw)).const_sub 1).clog
        (dilogInvCut_subset (inv_mem_dilogInvCut hw)))
  have hg (w : ℂ) (hw : w ∈ dilogInvCut) := ((hasDerivAt_id w).neg).clog hw
  have h' : dilogInvCut.EqOn (deriv f) (deriv g) := by
    intro w hw
    have hf' : deriv f w = _ := (hf w hw).deriv
    have hg' : deriv g w = _ := (hg w hw).deriv
    rw [hf', hg']
    have h₀ := dilogInvCut_ne_zero hw
    have h₁ : 1 - w ≠ 0 := sub_ne_zero.mpr (dilogCut_ne_one (dilogInvCut_subset hw)).symm
    have h₂ : 1 - w⁻¹ ≠ 0 :=
      sub_ne_zero.mpr (dilogCut_ne_one (dilogInvCut_subset (inv_mem_dilogInvCut hw))).symm
    have h₃ : w - 1 ≠ 0 := sub_ne_zero.mpr (dilogCut_ne_one (dilogInvCut_subset hw))
    have hdiv : 1 - w⁻¹ = (w - 1) / w := by field_simp
    simp only [id, Pi.inv_apply, Pi.neg_apply, hdiv]
    field_simp; ring
  exact isOpen_dilogInvCut.eqOn_of_deriv_eq isPreconnected_dilogInvCut
    (fun w hw => (hf w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hg w hw).differentiableAt.differentiableWithinAt)
    h' neg_one_mem_dilogInvCut (by simp) hz

/-- The principal-branch inversion identity, the second identity in equation (5). -/
theorem principalDilog_inversion {z : ℂ} (hz : z ∈ dilogInvCut) :
    principalDilog z + principalDilog z⁻¹ = -(π : ℂ)^2 / 6 - Complex.log (-z)^2 / 2 := by
  let f : ℂ → ℂ := fun w => principalDilog w + principalDilog w⁻¹
  let g : ℂ → ℂ := fun w => -(π : ℂ)^2 / 6 - Complex.log (-w)^2 / 2
  have hf (w : ℂ) (hw : w ∈ dilogInvCut) :=
    (hasDerivAt_principalDilog (dilogInvCut_subset hw)).add
      ((hasDerivAt_principalDilog (dilogInvCut_subset (inv_mem_dilogInvCut hw))).comp w
        ((hasDerivAt_id w).inv (dilogInvCut_ne_zero hw)))
  have hg (w : ℂ) (hw : w ∈ dilogInvCut) :=
    (((((hasDerivAt_id w).neg).clog hw).pow 2).div_const (2 : ℂ)).const_sub (-(π : ℂ)^2 / 6)
  have h' : dilogInvCut.EqOn (deriv f) (deriv g) := by
    intro w hw
    have hf' : deriv f w = _ := (hf w hw).deriv
    have hg' : deriv g w = _ := (hg w hw).deriv
    rw [hf', hg']
    have h₀ := dilogInvCut_ne_zero hw
    have h₁ := inv_ne_zero h₀
    simp only [Pi.neg_apply, id, ite_eq_right h₀, ite_eq_right h₁]
    rw [← log_sub_log_inv hw]
    field_simp; ring
  have hanchor : f (-1) = g (-1) := by
    simp [f, g, principalDilog_neg_one]; ring
  exact isOpen_dilogInvCut.eqOn_of_deriv_eq isPreconnected_dilogInvCut
    (fun w hw => (hf w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hg w hw).differentiableAt.differentiableWithinAt)
    h' neg_one_mem_dilogInvCut hanchor hz

end DurfeeCCS.Step06
