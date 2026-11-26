module

public import DurfeeCCS.Step08.NearOriginMiddleBounds
public import DurfeeCCS.Step08.NearOriginOuterBounds

/-! The intermediate logarithmic error integral in (18). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex MeasureTheory Set

private theorem middle_exp_pointwise (f a b : ℂ) {W E : ℝ}
    (hW : 0 ≤ W) (hf : f.re ≤ W) (hR : ‖a + b‖ ≤ E) :
    ‖(exp f - 1) * (a + b) + exp f * (exp (a + b) - 1 - (a + b))‖ ≤
      Real.exp (W + E) * (‖f * a‖ + ‖f * b‖ + ‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hE : 0 ≤ E := (norm_nonneg _).trans hR
  have hWW : Real.exp W ≤ Real.exp (W + E) := Real.exp_le_exp.mpr (by linarith)
  have hab (z : ℂ) : ‖(exp f - 1) * z‖ ≤ Real.exp (W + E) * ‖f * z‖ := by
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (‖f‖ * Real.exp (max 0 f.re)) * ‖z‖ :=
        mul_le_mul_of_nonneg_right (norm_exp_sub_one_le f) (norm_nonneg _)
      _ ≤ (‖f‖ * Real.exp W) * ‖z‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (max_le hW hf)) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ (‖f‖ * Real.exp (W + E)) * ‖z‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hWW (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hlin : ‖(exp f - 1) * (a + b)‖ ≤ Real.exp (W + E) * (‖f * a‖ + ‖f * b‖) := by
    rw [mul_add, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hab _) (hab _))
  have hsq : ‖a + b‖ ^ 2 / 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hR' : max 0 (a + b).re ≤ E := max_le hE ((Complex.re_le_norm _).trans hR)
  have hquad : ‖exp f * (exp (a + b) - 1 - (a + b))‖ ≤
      Real.exp (W + E) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    rw [norm_mul, Complex.norm_exp]
    calc
      _ ≤ Real.exp W * (‖a + b‖ ^ 2 / 2 * Real.exp (max 0 (a + b).re)) :=
        mul_le_mul (Real.exp_le_exp.mpr hf) (norm_exp_sub_one_sub_le _) (norm_nonneg _) (by positivity)
      _ ≤ Real.exp W * ((‖a‖ ^ 2 + ‖b‖ ^ 2) * Real.exp E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsq (Real.exp_le_exp.mpr hR') (by positivity) (by positivity))
          (by positivity)
      _ = _ := by rw [Real.exp_add]; ring
  refine (norm_add_le _ _).trans ((add_le_add hlin hquad).trans_eq ?_)
  ring

def nearOriginMiddleError (r u v : ℝ) : ℂ :=
  angularAverage (fun θ => exp (pairedLog r θ (verticalPoint u v)) -
    exp (nearOriginMainLog r θ (verticalPoint u v)))

theorem continuous_nearOriginMiddleError {r u : ℝ} (hr : |r| ≤ 1) (hu : 0 < u) :
    Continuous (nearOriginMiddleError r u) := by
  unfold nearOriginMiddleError angularAverage
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    ((Complex.continuous_exp.comp (continuous_pairedLog_vertical r hr hu)).sub
      (Complex.continuous_exp.comp (continuous_nearOriginMainLog r hu))) _ _).const_mul _

private theorem norm_nearOriginMiddleError_le {r u v : ℝ} (hu₀ : 0 < u) (hur : u ≤ r)
    (hr : r ≤ 1 / 40) (hv0 : 4 * u ≤ |v|) (hv1 : |v| ≤ Real.pi) :
    ‖nearOriginMiddleError r u v‖ ≤ Real.exp (r / u / 2 + 1.02 * (r ^ 2 / u)) *
      (angularMean (fun θ => ‖nearOriginMainLog r θ (verticalPoint u v) *
           nearOriginFirstRemainder r θ (verticalPoint u v)‖) +
       angularMean (fun θ => ‖nearOriginMainLog r θ (verticalPoint u v) *
           nearOriginTailRemainder r θ (verticalPoint u v)‖) +
       angularMean (fun θ => ‖nearOriginFirstRemainder r θ (verticalPoint u v)‖ ^ 2) +
       angularMean (fun θ => ‖nearOriginTailRemainder r θ (verticalPoint u v)‖ ^ 2)) := by
  have hr₀ : 0 ≤ r := hu₀.le.trans hur
  have hr' : |r| ≤ 1 := by rw [abs_of_nonneg hr₀]; linarith
  have hz : 0 < (verticalPoint u v).re := by simpa only [verticalPoint_re] using hu₀
  let F (θ : ℝ) := pairedLog r θ (verticalPoint u v)
  let f (θ : ℝ) := nearOriginMainLog r θ (verticalPoint u v)
  let a (θ : ℝ) := nearOriginFirstRemainder r θ (verticalPoint u v)
  let b (θ : ℝ) := nearOriginTailRemainder r θ (verticalPoint u v)
  let R (θ : ℝ) := a θ + b θ
  let e (θ : ℝ) := (exp (f θ) - 1) * R θ + exp (f θ) * (exp (R θ) - 1 - R θ)
  let W := r / u / 2
  let E := 1.02 * (r ^ 2 / u)
  let C := Real.exp (W + E)
  have hP : Continuous (fun θ : ℝ => (v, θ)) := continuous_const.prodMk continuous_id
  have hF₀ := (continuous_pairedLog_vertical r hr' (u := u) hu₀).comp hP
  have hf₀ := (continuous_nearOriginMainLog r (u := u) hu₀).comp hP
  have ha₀ := (continuous_nearOriginFirstRemainder r (u := u) hu₀).comp hP
  have hb₀ := (continuous_nearOriginTailRemainder r hr' (u := u) hu₀).comp hP
  simp only [Function.comp_def] at hF₀ hf₀ ha₀ hb₀
  have hF : Continuous F := hF₀
  have hf : Continuous f := hf₀
  have ha : Continuous a := ha₀
  have hb : Continuous b := hb₀
  have hR : Continuous R := ha.add hb
  have hef : Continuous (fun θ => exp (f θ)) := Complex.continuous_exp.comp hf
  have heR : Continuous (fun θ => exp (R θ)) := Complex.continuous_exp.comp hR
  have he : Continuous e := ((hef.sub (continuous_const (y := (1 : ℂ)))).mul hR).add
    (hef.mul ((heR.sub (continuous_const (y := (1 : ℂ)))).sub hR))
  have hprof (θ : ℝ) : F θ - f θ = R θ := pairedLog_sub_main_eq_remainders r θ hr' hz
  have hzero : angularAverage R = 0 := by
    have hh : R = fun θ => F θ - f θ := funext (fun θ => (hprof θ).symm)
    rw [hh, angularAverage_sub (hF.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
    change angularAverage (fun θ => pairedLog r θ (verticalPoint u v)) -
      angularAverage (fun θ => nearOriginMainLog r θ (verticalPoint u v)) = 0
    rw [angularAverage_pairedLog r hr' hz, angularAverage_nearOriginMainLog, sub_zero]
  have heq (θ : ℝ) : exp (F θ) - exp (f θ) = e θ + R θ := by
    have h : F θ = f θ + R θ := by rw [← hprof]; ring
    rw [h, exp_add]
    dsimp only [e]
    ring
  have hpoint (θ : ℝ) : ‖e θ‖ ≤
      C * (‖f θ * a θ‖ + ‖f θ * b θ‖ + ‖a θ‖ ^ 2 + ‖b θ‖ ^ 2) := by
    refine middle_exp_pointwise (f θ) (a θ) (b θ) (show 0 ≤ W by dsimp only [W]; positivity)
      (nearOriginMainLog_re_vertical_le hr₀ hu₀ hv0 θ) ?_
    change ‖R θ‖ ≤ E
    rw [← hprof]
    simpa only [E, F, f, verticalPoint_re] using norm_pairedLog_sub_main_le θ hz
      (by simpa only [verticalPoint_re] using hur) hr (by simpa only [verticalPoint_im] using hv1)
  change ‖angularAverage (fun θ => exp (F θ) - exp (f θ))‖ ≤
    C * (angularMean (fun θ => ‖f θ * a θ‖) + angularMean (fun θ => ‖f θ * b θ‖) +
       angularMean (fun θ => ‖a θ‖ ^ 2) + angularMean (fun θ => ‖b θ‖ ^ 2))
  simp_rw [heq]
  rw [angularAverage_add (he.intervalIntegrable _ _) (hR.intervalIntegrable _ _), hzero, add_zero]
  refine (norm_angularAverage_le e).trans ?_
  have h1 : Continuous (fun θ => ‖f θ * a θ‖) := (hf.mul ha).norm
  have h2 : Continuous (fun θ => ‖f θ * b θ‖) := (hf.mul hb).norm
  have h3 : Continuous (fun θ => ‖a θ‖ ^ 2) := ha.norm.pow 2
  have h4 : Continuous (fun θ => ‖b θ‖ ^ 2) := hb.norm.pow 2
  have h12 : Continuous (fun θ => ‖f θ * a θ‖ + ‖f θ * b θ‖) := h1.add h2
  have h123 : Continuous (fun θ => ‖f θ * a θ‖ + ‖f θ * b θ‖ + ‖a θ‖ ^ 2) := h12.add h3
  have hG : Continuous (fun θ => C * (‖f θ * a θ‖ + ‖f θ * b θ‖ + ‖a θ‖ ^ 2 + ‖b θ‖ ^ 2)) :=
    (h123.add h4).const_mul C
  have h := angularMean_mono_on he.norm hG (fun θ _ => hpoint θ)
  rwa [angularMean_const_mul, angularMean_add_continuous h123 h4,
    angularMean_add_continuous h12 h3, angularMean_add_continuous h1 h2] at h

private theorem continuous_angularMean {F : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry F)) : Continuous (fun v => angularMean (F v)) := by
  unfold angularMean
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf _ _).const_mul _

/-- The intermediate-arc error, multiplied by the vertical average normalization. -/
theorem integral_norm_nearOriginMiddleError_lt {r u : ℝ} (hu : 0 < u)
    (hu_r : u ≤ r) (hr : r ≤ 1 / 40) (hΔ : r ^ 2 / u ≤ 1) :
    (2 * Real.pi)⁻¹ * (∫ v in {v : ℝ | 4 * u < |v| ∧ |v| ≤ Real.pi},
      ‖nearOriginMiddleError r u v‖) < Real.exp (r / u / 2 + 1.02 * (r ^ 2 / u)) *
        (0.48 * r ^ 2 + 0.36 * (r ^ 3 / u)) := by
  let L (v θ : ℝ) := nearOriginMainLog r θ (verticalPoint u v)
  let a (v θ : ℝ) := nearOriginFirstRemainder r θ (verticalPoint u v)
  let b (v θ : ℝ) := nearOriginTailRemainder r θ (verticalPoint u v)
  let q1 (v : ℝ) := angularMean (fun θ => ‖L v θ * a v θ‖)
  let q2 (v : ℝ) := angularMean (fun θ => ‖L v θ * b v θ‖)
  let q3 (v : ℝ) := angularMean (fun θ => ‖a v θ‖ ^ 2)
  let q4 (v : ℝ) := angularMean (fun θ => ‖b v θ‖ ^ 2)
  let Q (v : ℝ) := q1 v + q2 v + q3 v + q4 v
  let C := Real.exp (r / u / 2 + 1.02 * (r ^ 2 / u))
  let s := {v : ℝ | 4 * u < |v| ∧ |v| ≤ Real.pi}
  let t := Icc (-Real.pi) Real.pi
  have hr₀ : 0 < r := hu.trans_le hu_r
  have hr' : |r| ≤ 1 := by rw [abs_of_pos hr₀]; linarith
  have hL : Continuous (Function.uncurry L) := continuous_nearOriginMainLog r hu
  have ha : Continuous (Function.uncurry a) := continuous_nearOriginFirstRemainder r hu
  have hb : Continuous (Function.uncurry b) := continuous_nearOriginTailRemainder r hr' hu
  have hc1 : Continuous q1 := continuous_angularMean ((hL.mul ha).norm)
  have hc2 : Continuous q2 := continuous_angularMean ((hL.mul hb).norm)
  have hc3 : Continuous q3 := continuous_angularMean (ha.norm.pow 2)
  have hc4 : Continuous q4 := continuous_angularMean (hb.norm.pow 2)
  have hQ : Continuous Q := ((hc1.add hc2).add hc3).add hc4
  have hs : MeasurableSet s := (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)
  have hst : s ⊆ t := fun v hv => abs_le.mp hv.2
  have hi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hQpos (v : ℝ) : 0 ≤ Q v := by
    have hmean (f : ℝ → ℝ) (hf : ∀ θ, 0 ≤ f θ) : 0 ≤ angularMean f := by
      unfold angularMean
      exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hi fun θ _ => hf θ)
    unfold Q q1 q2 q3 q4
    exact add_nonneg (add_nonneg (add_nonneg
      (hmean (fun θ => ‖L v θ * a v θ‖) (fun _ => norm_nonneg _))
      (hmean (fun θ => ‖L v θ * b v θ‖) (fun _ => norm_nonneg _)))
      (hmean (fun θ => ‖a v θ‖ ^ 2) (fun _ => sq_nonneg _)))
      (hmean (fun θ => ‖b v θ‖ ^ 2) (fun _ => sq_nonneg _))
  have hCt : IntegrableOn (fun v => C * Q v) t :=
    (hQ.const_mul C).continuousOn.integrableOn_Icc
  have hbound : (∫ v in s, ‖nearOriginMiddleError r u v‖) ≤ ∫ v in t, C * Q v := by
    have hInt : IntegrableOn (fun v => ‖nearOriginMiddleError r u v‖) t :=
      (continuous_nearOriginMiddleError hr' hu).norm.continuousOn.integrableOn_Icc
    calc
      _ ≤ ∫ v in s, C * Q v := by
        apply setIntegral_mono_on (hInt.mono_set hst) (hCt.mono_set hst) hs
        intro v hv
        exact norm_nearOriginMiddleError_le hu hu_r hr hv.1.le hv.2
      _ ≤ _ := setIntegral_mono_set hCt
        (ae_of_all _ fun v => mul_nonneg (Real.exp_nonneg _) (hQpos v))
        (ae_of_all _ fun v hv => hst hv)
  have hq1 : angularMean q1 ≤ 0.16 * r ^ 2 := by
    refine (angularMean_mono_on (g := fun _ => 0.16 * r ^ 2)
      hc1 continuous_const (fun v hv => ?_)).trans_eq ?_
    · exact angularMean_abs_main_mul_first_le hr₀.le hu (hu_r.trans hr) (abs_le.mpr hv)
    · exact angularMean_const_real _
  have hq3 : angularMean q3 ≤ 0.206 ^ 2 * r ^ 2 :=
    double_angularMean_sq_first_remainder_le hr₀.le hu (hu_r.trans hr)
  have hq4 : angularMean q4 ≤ 0.354 ^ 2 * (r ^ 4 / u) :=
    double_angularMean_sq_tail_remainder_le hr₀.le hr hu
  have hq2 : angularMean q2 ≤ 0.354 * (r ^ 3 / u) := by
    let w := 0.354 * r
    let q (v : ℝ) := angularMean (fun θ => ‖L v θ‖ ^ 2)
    have hq : Continuous q :=
      continuous_angularMean (F := fun v θ => ‖L v θ‖ ^ 2) (hL.norm.pow 2)
    have hD : Continuous (fun v => (w * q v + w⁻¹ * q4 v) / 2) :=
      ((hq.const_mul w).add (hc4.const_mul w⁻¹)).div_const _
    have hdom : angularMean q2 ≤ angularMean (fun v => (w * q v + w⁻¹ * q4 v) / 2) := by
      apply angularMean_mono_on hc2 hD
      intro v _
      have hP : Continuous (fun θ : ℝ => (v, θ)) := continuous_const.prodMk continuous_id
      exact angularMean_norm_mul_le_weighted_sq (hL.comp hP) (hb.comp hP) (by positivity)
    have heq : (fun v => (w * q v + w⁻¹ * q4 v) / 2) =
        (fun v => (2 : ℝ)⁻¹ * (w * q v + w⁻¹ * q4 v)) := by funext v; ring
    rw [heq, angularMean_const_mul, angularMean_add_continuous (hq.const_mul _) (hc4.const_mul _),
      angularMean_const_mul, angularMean_const_mul] at hdom
    refine hdom.trans ((mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (double_angularMean_nearOriginMainLog_sq_le hu) (by positivity))
        (mul_le_mul_of_nonneg_left hq4 (by positivity))) (by positivity)).trans_eq ?_)
    dsimp only [w]
    field_simp [hr₀.ne', hu.ne']
    ring
  change (2 * Real.pi)⁻¹ * (∫ v in s, ‖nearOriginMiddleError r u v‖) < _
  refine (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_lt ?_
  rw [MeasureTheory.integral_const_mul, show t = Icc (-Real.pi) Real.pi by rfl,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hi, ← mul_left_comm C]
  change C * angularMean Q < C * _
  apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
  change angularMean (fun v => q1 v + q2 v + q3 v + q4 v) < _
  have h12 : Continuous (fun v => q1 v + q2 v) := hc1.add hc2
  have h123 : Continuous (fun v => q1 v + q2 v + q3 v) := h12.add hc3
  rw [angularMean_add_continuous h123 hc4,
    angularMean_add_continuous h12 hc3, angularMean_add_continuous hc1 hc2]
  refine (add_le_add (add_le_add (add_le_add hq1 hq2) hq3) hq4).trans_lt ?_
  have hΔ' : r ^ 4 / u ≤ r ^ 2 := by
    convert mul_le_mul_of_nonneg_left hΔ (sq_nonneg r) using 1 <;> ring
  have hb0 : 0 ≤ r ^ 3 / u := by positivity
  linarith only [hΔ', hb0, sq_pos_of_pos hr₀]

theorem integral_norm_nearOriginMiddleError_le {r u : ℝ} (hu : 0 < u)
    (hu_r : u ≤ r) (hr : r ≤ 1 / 40) (hΔ : r ^ 2 / u ≤ 1) :
    (2 * Real.pi)⁻¹ * (∫ v in {v : ℝ | 4 * u < |v| ∧ |v| ≤ Real.pi},
      ‖nearOriginMiddleError r u v‖) ≤ Real.exp (r / u / 2 + 1.02 * (r ^ 2 / u)) *
        (0.48 * r ^ 2 + 0.36 * (r ^ 3 / u)) :=
  (integral_norm_nearOriginMiddleError_lt hu hu_r hr hΔ).le

end DurfeeCCS.Step08
