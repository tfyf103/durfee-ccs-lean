module

public import DurfeeCCS.Step08.MidpointLogSeries
public import DurfeeCCS.Step08.MidpointRule
public import DurfeeCCS.Step06.Saddle
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Differentiation and integration of the logarithm along a ray. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06 Filter MeasureTheory Set
open scoped Topology

/-- The decaying argument of the logarithmic ray. -/
noncomputable def rayArgument (w α : ℂ) (x : ℝ) : ℂ :=
  w * Complex.exp (-α * (x : ℂ))

noncomputable def rayLog (w α : ℂ) (x : ℝ) : ℂ :=
  Complex.log (1 - rayArgument w α x)

noncomputable def rayLogDeriv (w α : ℂ) (x : ℝ) : ℂ :=
  α * rayArgument w α x / (1 - rayArgument w α x)

noncomputable def rayLogSecond (w α : ℂ) (x : ℝ) : ℂ :=
  -α ^ 2 * rayArgument w α x / (1 - rayArgument w α x) ^ 2

theorem norm_rayArgument (w : ℂ) {α : ℂ} (hα : α.re = 1) (x : ℝ) :
    ‖rayArgument w α x‖ = ‖w‖ * Real.exp (-x) := by
  rw [rayArgument, norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, hα]

private theorem hasDerivAt_rayArgument (w α : ℂ) (x : ℝ) :
    HasDerivAt (rayArgument w α) (-α * rayArgument w α x) x := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-α)).cexp).const_mul w
  convert h using 1
  · rfl
  · simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, rayArgument]
    ring

private theorem rayArgument_norm_lt_one {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1)
    {x : ℝ} (hx : 0 ≤ x) : ‖rayArgument w α x‖ < 1 := by
  rw [norm_rayArgument w hα]
  exact (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))).trans_lt hw

private theorem rayLog_slit {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1)
    {x : ℝ} (hx : 0 ≤ x) : 1 - rayArgument w α x ∈ Complex.slitPlane :=
  (mem_dilogCut_of_norm_lt_one (rayArgument_norm_lt_one hw hα hx) : _)

theorem hasDerivAt_rayLog {w α : ℂ} {x : ℝ}
    (hx : 1 - rayArgument w α x ∈ Complex.slitPlane) :
    HasDerivAt (rayLog w α) (rayLogDeriv w α x) x := by
  have h := ((hasDerivAt_rayArgument w α x).const_sub 1).clog_real hx
  convert h using 1
  · rfl
  · simp [rayLogDeriv]

theorem hasDerivAt_rayLogDeriv {w α : ℂ} {x : ℝ}
    (hx : 1 - rayArgument w α x ≠ 0) :
    HasDerivAt (rayLogDeriv w α) (rayLogSecond w α x) x := by
  have h := hasDerivAt_rayArgument w α x
  convert (h.const_mul α).div (h.const_sub 1) hx using 1
  · rfl
  · rw [rayLogSecond]
    congr 1
    ring

/-- Equation (43), in the normalization `α.re = 1`. -/
theorem norm_rayLogSecond {w α : ℂ} (hα : α.re = 1) (x : ℝ) :
    ‖rayLogSecond w α x‖ = ‖α‖ ^ 2 * ‖w‖ * Real.exp (-x) /
      ‖1 - rayArgument w α x‖ ^ 2 := by
  rw [rayLogSecond, norm_div, norm_mul, norm_neg, norm_pow, norm_pow, norm_rayArgument w hα]
  ring

private theorem norm_rayLog_le {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1)
    {x : ℝ} (hx : 0 ≤ x) :
    ‖rayLog w α x‖ ≤ (‖w‖ / (1 - ‖w‖)) * Real.exp (-x) := by
  let z := rayArgument w α x
  have ha : ‖z‖ < 1 := rayArgument_norm_lt_one hw hα hx
  have hb : ‖z‖ ≤ ‖w‖ := by
    dsimp only [z]
    rw [norm_rayArgument w hα]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))
  have hlog := Complex.norm_log_one_add_le (z := -z) (by simpa using ha)
  simp only [norm_neg, ← sub_eq_add_neg] at hlog
  change ‖Complex.log (1 - z)‖ ≤ _
  refine hlog.trans ?_
  calc
    _ ≤ ‖z‖ / (1 - ‖z‖) := by
      have hn : 0 < 1 - ‖z‖ := by linarith
      apply (le_div_iff₀ hn).2
      field_simp
      nlinarith [sq_nonneg ‖z‖]
    _ ≤ ‖z‖ / (1 - ‖w‖) := div_le_div_of_nonneg_left (norm_nonneg _)
      (by linarith) (by linarith)
    _ = _ := by dsimp only [z]; rw [norm_rayArgument w hα]; ring

private theorem integrableOn_of_ray_decay {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {C : ℝ} (hc : ContinuousOn f (Ici 0))
    (hb : ∀ x ≥ 0, ‖f x‖ ≤ C * Real.exp (-x)) : IntegrableOn f (Ioi 0) := by
  apply ((integrableOn_exp_neg_Ioi 0).const_mul C).mono'
    ((hc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  exact hb x (mem_Ioi.mp hx).le

theorem integrableOn_rayLog {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1) :
    IntegrableOn (rayLog w α) (Ioi 0) :=
  integrableOn_of_ray_decay (fun _ hx => (hasDerivAt_rayLog (rayLog_slit hw hα hx)).continuousAt.continuousWithinAt)
    (fun _ hx => norm_rayLog_le hw hα hx)

private theorem rayArgument_tendsto_zero (w : ℂ) {α : ℂ} (hα : α.re = 1) :
    Tendsto (rayArgument w α) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [norm_rayArgument w hα]
  simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul ‖w‖

private theorem raySlope_ne_zero {α : ℂ} (hα : α.re = 1) : α ≠ 0 := by
  rintro rfl
  norm_num at hα

/-- Exact integral of the ray logarithm, with its principal dilogarithm branch. -/
theorem integral_rayLog {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1) :
    (∫ x in Ioi (0 : ℝ), rayLog w α x) = -principalDilog w / α := by
  let F (x : ℝ) : ℂ := principalDilog (rayArgument w α x) / α
  have hder (x : ℝ) (hx : x ∈ Ici (0 : ℝ)) : HasDerivAt F (rayLog w α x) x := by
    have hd := hasDerivAt_rayArgument w α x
    have hL := hasDerivAt_principalDilog (rayLog_slit hw hα hx)
    have h := (hL.comp x hd).div_const α
    convert h using 1
    · rfl
    · by_cases hz : rayArgument w α x = 0
      · simp [rayLog, hz]
      · simp only [rayLog, ite_eq_right hz]
        field_simp [raySlope_ne_zero hα, hz]
  have hcont : ContinuousAt principalDilog (0 : ℂ) :=
    (hasDerivAt_principalDilog (mem_dilogCut_of_norm_lt_one (by simp))).continuousAt
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h := ((hcont.tendsto.comp (rayArgument_tendsto_zero w hα)).div_const α)
    simpa only [F, Function.comp_apply, principalDilog_zero, zero_div] using h
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hder (integrableOn_rayLog hw hα) hlim
  simpa [F, rayArgument, zero_sub, neg_div] using h

/-- The positive real function dominating the second derivative. -/
noncomputable def raySecondMajorant (r x : ℝ) : ℝ :=
  r * Real.exp (-x) / (1 - r * Real.exp (-x)) ^ 2

private theorem one_sub_exp_pos {r x : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) (hx : 0 ≤ x) :
    0 < 1 - r * Real.exp (-x) :=
  sub_pos.mpr ((mul_le_of_le_one_right h₀ (Real.exp_le_one_iff.mpr (by linarith))).trans_lt h₁)

theorem norm_rayLogSecond_le {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1)
    {x : ℝ} (hx : 0 ≤ x) :
    ‖rayLogSecond w α x‖ ≤ ‖α‖ ^ 2 * raySecondMajorant ‖w‖ x := by
  have hpos := one_sub_exp_pos (norm_nonneg w) hw hx
  have h := norm_sub_norm_le (1 : ℂ) (rayArgument w α x)
  rw [norm_one, norm_rayArgument w hα] at h
  rw [norm_rayLogSecond hα, raySecondMajorant, ← mul_div_assoc, ← mul_assoc]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hpos.le h 2)

private theorem continuousOn_rayLogSecond {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1) :
    ContinuousOn (rayLogSecond w α) (Ici 0) := by
  unfold rayLogSecond
  apply ContinuousOn.div (by unfold rayArgument; fun_prop) (by unfold rayArgument; fun_prop)
  intro x hx
  exact pow_ne_zero _ (Complex.slitPlane_ne_zero (rayLog_slit hw hα hx))

private theorem integrableOn_raySecondMajorant {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) :
    IntegrableOn (raySecondMajorant r) (Ioi 0) := by
  have hc : ContinuousOn (raySecondMajorant r) (Ici 0) := by
    unfold raySecondMajorant
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (one_sub_exp_pos h₀ h₁ hx).ne'
  apply integrableOn_of_ray_decay (C := r / (1 - r) ^ 2) hc
  intro x hx
  have h₁' : 0 < 1 - r := by linarith
  have hpos := one_sub_exp_pos h₀ h₁ hx
  have hred : r * Real.exp (-x) ≤ r := mul_le_of_le_one_right h₀ (Real.exp_le_one_iff.mpr (by linarith))
  rw [Real.norm_of_nonneg (by unfold raySecondMajorant; positivity), raySecondMajorant]
  calc
    _ ≤ r * Real.exp (-x) / (1 - r) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ h₁'.le (by linarith) 2)
    _ = _ := by ring

theorem integral_raySecondMajorant {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) :
    (∫ x in Ioi (0 : ℝ), raySecondMajorant r x) = r / (1 - r) := by
  let F (x : ℝ) := -(1 - r * Real.exp (-x))⁻¹
  have hD (x : ℝ) (hx : x ∈ Ici (0 : ℝ)) : HasDerivAt F (raySecondMajorant r x) x := by
    have hd := (((hasDerivAt_id x).neg.exp.const_mul r).const_sub 1).inv (one_sub_exp_pos h₀ h₁ hx).ne'
    convert hd.neg using 1
    · rfl
    · unfold raySecondMajorant
      simp
      ring
  have hlim : Tendsto F atTop (𝓝 (-1)) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul r)).inv₀ (by simp)
    simpa [F] using h.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hD (integrableOn_raySecondMajorant h₀ h₁) hlim]
  dsimp [F]
  simp only [neg_zero, Real.exp_zero, mul_one]
  field_simp
  ring

theorem integrableOn_rayLogSecond {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1) :
    IntegrableOn (rayLogSecond w α) (Ioi 0) := by
  apply ((integrableOn_raySecondMajorant (norm_nonneg w) hw).const_mul (‖α‖ ^ 2)).mono'
    (((continuousOn_rayLogSecond hw hα).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  exact norm_rayLogSecond_le hw hα (mem_Ioi.mp hx).le

theorem integral_norm_rayLogSecond_le {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1) :
    (∫ x in Ioi (0 : ℝ), ‖rayLogSecond w α x‖) ≤ ‖α‖ ^ 2 * (‖w‖ / (1 - ‖w‖)) := by
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), ‖α‖ ^ 2 * raySecondMajorant ‖w‖ x := by
      apply integral_mono_ae (integrableOn_rayLogSecond hw hα).norm
        ((integrableOn_raySecondMajorant (norm_nonneg w) hw).const_mul _)
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      exact norm_rayLogSecond_le hw hα (mem_Ioi.mp hx).le
    _ = _ := by rw [integral_const_mul, integral_raySecondMajorant (norm_nonneg w) hw]

set_option maxHeartbeats 600000 in
private theorem summable_sampled_rayLog {w α : ℂ} (hw : ‖w‖ < 1) (hα : α.re = 1) {u : ℝ} (hu : 0 < u) :
    Summable (fun j : ℕ => rayLog w α (((j : ℝ) + 1 / 2) * u)) := by
  have h := summable_geometric_of_lt_one (Real.exp_nonneg (-u))
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu))
  have hb (j : ℕ) : ‖rayLog w α (((j : ℝ) + 1 / 2) * u)‖ ≤
      (‖w‖ / (1 - ‖w‖) * Real.exp (-u / 2)) * Real.exp (-u) ^ j := by
    refine (norm_rayLog_le hw hα (x := ((j : ℝ) + 1 / 2) * u) (by positivity)).trans_eq ?_
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    (h.mul_left (‖w‖ / (1 - ‖w‖) * Real.exp (-u / 2)))).of_norm

/-- Midpoint estimate specialized to the logarithmic ray and its exact dilogarithmic integral. -/
theorem norm_rayLog_midpoint_sub_dilog_le_integral {w α : ℂ} (hw : ‖w‖ < 1)
    (hα : α.re = 1) {u : ℝ} (hu : 0 < u) :
    ‖(∑' j : ℕ, rayLog w α (((j : ℝ) + 1 / 2) * u)) -
      (-principalDilog w / ((u : ℂ) * α))‖ ≤ (u / 8) * ∫ x in Ioi (0 : ℝ), ‖rayLogSecond w α x‖ := by
  have hd := midpoint_rule_Ioi (f := rayLog w α) (f' := rayLogDeriv w α)
    (f'' := rayLogSecond w α) hu (fun x hx => hasDerivAt_rayLog (rayLog_slit hw hα hx))
    (fun x hx => hasDerivAt_rayLogDeriv (Complex.slitPlane_ne_zero (rayLog_slit hw hα hx)))
    (continuousOn_rayLogSecond hw hα) (integrableOn_rayLog hw hα) (integrableOn_rayLogSecond hw hα)
    (summable_sampled_rayLog hw hα hu)
  rw [integral_rayLog hw hα, Complex.real_smul, Complex.ofReal_inv] at hd
  have he : (u : ℂ)⁻¹ * (-principalDilog w / α) = -principalDilog w / ((u : ℂ) * α) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rwa [he] at hd

theorem norm_rayLog_midpoint_sub_dilog_le {w α : ℂ} (hw : ‖w‖ < 1)
    (hα : α.re = 1) {u : ℝ} (hu : 0 < u) :
    ‖(∑' j : ℕ, rayLog w α (((j : ℝ) + 1 / 2) * u)) -
      (-principalDilog w / ((u : ℂ) * α))‖ ≤ (u / 8) * ‖α‖ ^ 2 * (‖w‖ / (1 - ‖w‖)) := by
  rw [mul_assoc]
  exact (norm_rayLog_midpoint_sub_dilog_le_integral hw hα hu).trans
    (mul_le_mul_of_nonneg_left (integral_norm_rayLogSecond_le hw hα) (by positivity))

theorem norm_ray_phase (r θ : ℝ) :
    ‖(-(r : ℂ) * I) * Complex.exp (θ * I)‖ = |r| := by
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    Complex.norm_exp]
  simp [Complex.mul_re]

/-- Midpoint error for the pair of rays, bounded by their second-derivative integrals. -/
theorem norm_pairedLog_sub_saddleG_div_le_signed_integrals (r θ u η B : ℝ)
    (hr : |r| < 1) (hu : 0 < u)
    (hB : ∀ t : ℝ, |t| ≤ |θ| →
      (∫ x in Ioi (0 : ℝ), ‖rayLogSecond (-(r : ℂ) * I * Complex.exp (t * I))
        (1 + (η : ℂ) * I) x‖) ≤ B) :
    let ζ : ℂ := (u : ℂ) * (1 + (η : ℂ) * I)
    ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤ u / 4 * B := by
  let α := 1 + (η : ℂ) * I
  let ζ := (u : ℂ) * α
  let w (t : ℝ) := (-(r : ℂ) * I) * Complex.exp (t * I)
  have hα : α.re = 1 := by simp [α, Complex.mul_re]
  have hζ : 0 < ζ.re := by simpa [ζ, Complex.mul_re, hα] using hu
  have hw₁ (t : ℝ) : ‖w t‖ < 1 := by simpa only [w, norm_ray_phase] using hr
  have hℓ (t : ℝ) (j : ℕ) : Complex.log (1 + pairedTerm r t ζ j) =
      rayLog (w t) α (((j : ℝ) + 1 / 2) * u) := by
    simp only [pairedTerm, rayLog, rayArgument, w, ζ, Complex.exp_add]
    push_cast
    rw [show -((j : ℂ) + 1 / 2) * ((u : ℂ) * α) = -α * (((j : ℂ) + 1 / 2) * u) by ring]
    congr 1
    ring
  have hlog : pairedLog r θ ζ = (∑' j : ℕ, rayLog (w θ) α (((j : ℝ) + 1 / 2) * u)) +
      (∑' j : ℕ, rayLog (w (-θ)) α (((j : ℝ) + 1 / 2) * u)) := by
    simp_rw [pairedLog, hℓ]
    exact (summable_sampled_rayLog (hw₁ θ) hα hu).tsum_add (summable_sampled_rayLog (hw₁ (-θ)) hα hu)
  have hg : saddleG r θ / ζ = (-principalDilog (w θ) / ζ) + (-principalDilog (w (-θ)) / ζ) := by
    simp only [saddleG, w, Complex.ofReal_neg, ← sub_eq_add_neg, sub_div, neg_div]
  have ha := (norm_rayLog_midpoint_sub_dilog_le_integral (hw₁ θ) hα hu).trans
    (mul_le_mul_of_nonneg_left (hB θ le_rfl) (by positivity : 0 ≤ u / 8))
  have hb := (norm_rayLog_midpoint_sub_dilog_le_integral (hw₁ (-θ)) hα hu).trans
    (mul_le_mul_of_nonneg_left (hB (-θ) (by rw [abs_neg])) (by positivity : 0 ≤ u / 8))
  change ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤ _
  rw [hlog, hg, add_sub_add_comm]
  exact (norm_add_le _ _).trans ((add_le_add ha hb).trans_eq (by ring))

theorem norm_pairedLog_sub_saddleG_div_le_integrals (r θ u η B : ℝ)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hu : 0 < u)
    (hB : ∀ t : ℝ, |t| ≤ |θ| →
      (∫ x in Ioi (0 : ℝ), ‖rayLogSecond (-(r : ℂ) * I * Complex.exp (t * I))
        (1 + (η : ℂ) * I) x‖) ≤ B) :
    let ζ : ℂ := (u : ℂ) * (1 + (η : ℂ) * I)
    ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤ u / 4 * B :=
  norm_pairedLog_sub_saddleG_div_le_signed_integrals r θ u η B
    (by rwa [abs_of_nonneg hr₀]) hu hB

/-- The signed-radius form of the midpoint bound (44). -/
theorem norm_pairedLog_sub_saddleG_div_le_signed (r θ u η : ℝ) (hr : |r| < 1)
    (hu : 0 < u) :
    let ζ : ℂ := (u : ℂ) * (1 + (η : ℂ) * I)
    ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤ u * (1 + η ^ 2) * |r| / (4 * (1 - |r|)) := by
  let α := 1 + (η : ℂ) * I
  have hα : α.re = 1 := by simp [α, Complex.mul_re]
  have hsq : ‖α‖ ^ 2 = 1 + η ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [α, Complex.mul_re, Complex.mul_im]
    ring
  have hB (t : ℝ) (_ht : |t| ≤ |θ|) :
      (∫ x in Ioi (0 : ℝ), ‖rayLogSecond (-(r : ℂ) * I * Complex.exp (t * I)) α x‖) ≤
        (1 + η ^ 2) * (|r| / (1 - |r|)) := by
    have hw : ‖-(r : ℂ) * I * Complex.exp (t * I)‖ < 1 := by
      rwa [norm_ray_phase]
    simpa only [norm_ray_phase, hsq] using integral_norm_rayLogSecond_le hw hα
  refine (norm_pairedLog_sub_saddleG_div_le_signed_integrals r θ u η _ hr hu hB).trans_eq ?_
  field_simp [show 1 - |r| ≠ 0 by linarith]

/-- Equation (44), including the exact constant multiplying the midpoint error. -/
theorem norm_pairedLog_sub_saddleG_div_le (r θ u η : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hu : 0 < u) :
    let ζ : ℂ := (u : ℂ) * (1 + (η : ℂ) * I)
    ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤ u * (1 + η ^ 2) * r / (4 * (1 - r)) := by
  simpa only [abs_of_nonneg hr₀] using
    norm_pairedLog_sub_saddleG_div_le_signed r θ u η (by rwa [abs_of_nonneg hr₀]) hu

end DurfeeCCS.Step08
