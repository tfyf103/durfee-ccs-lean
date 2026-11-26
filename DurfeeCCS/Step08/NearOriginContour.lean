module

public import DurfeeCCS.Step08.DurfeeContour
public import DurfeeCCS.Step08.NearOriginArcBounds
public import DurfeeCCS.Step08.NearOriginMiddleEstimate
public import DurfeeCCS.Step08.NearOriginOuterBounds

/-! The four comparisons in the near-origin contour split (18). -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Complex MeasureTheory Set DurfeeCCS.Step06

private theorem norm_contour_difference_with_correction_le {A B C : ℝ → ℂ}
    {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t)
    (hA : IntegrableOn A t) (hB : Integrable B) (hC : Integrable C) :
    ‖(∫ v in t, A v) - ∫ v, B v + C v‖ ≤
      (∫ v in s, ‖A v - B v - C v‖) + (∫ v in t \ s, ‖A v - B v‖) +
        (∫ v in tᶜ, ‖B v‖) + ∫ v in sᶜ, ‖C v‖ := by
  have hdis : Disjoint s (t \ s) := Set.disjoint_left.mpr (fun _ ha hb => hb.2 ha)
  have hUnion : s ∪ (t \ s) = t := by
    ext v
    constructor
    · rintro (hv | hv)
      · exact hst hv
      · exact hv.1
    · intro hv
      by_cases hin : v ∈ s
      · exact Or.inl hin
      · exact Or.inr ⟨hv, hin⟩
  have hsplit (F : ℝ → ℂ) (hF : IntegrableOn F t) :
      (∫ v in t, F v) = (∫ v in s, F v) + ∫ v in t \ s, F v := by
    calc
      _ = ∫ v in s ∪ (t \ s), F v := congrArg (fun q => ∫ v in q, F v) hUnion.symm
      _ = _ := setIntegral_union hdis (ht.diff hs) (hF.mono_set hst) (hF.mono_set sdiff_subset)
  have hAs : IntegrableOn A s := hA.mono_set hst
  have hAt : IntegrableOn A (t \ s) := hA.mono_set sdiff_subset
  have hABs : IntegrableOn (fun v => A v - B v) s := hAs.sub hB.integrableOn
  have heq : (∫ v in t, A v) - (∫ v, B v + C v) =
      ((∫ v in s, A v - B v - C v) + ∫ v in t \ s, A v - B v) -
        ((∫ v in tᶜ, B v) + ∫ v in sᶜ, C v) := by
    rw [integral_add hB hC, ← integral_add_compl ht hB, ← integral_add_compl hs hC,
      hsplit A hA, hsplit B hB.integrableOn,
      integral_sub hABs hC.integrableOn,
      integral_sub hAs hB.integrableOn, integral_sub hAt hB.integrableOn]
    abel
  rw [heq]
  have h1 := norm_sub_le ((∫ v in s, A v - B v - C v) + ∫ v in t \ s, A v - B v)
    ((∫ v in tᶜ, B v) + ∫ v in sᶜ, C v)
  have h2 := norm_add_le (∫ v in s, A v - B v - C v) (∫ v in t \ s, A v - B v)
  have h3 := norm_add_le (∫ v in tᶜ, B v) (∫ v in sᶜ, C v)
  have h4 := norm_integral_le_integral_norm (μ := volume.restrict s) (fun v => A v - B v - C v)
  have h5 := norm_integral_le_integral_norm (μ := volume.restrict (t \ s)) (fun v => A v - B v)
  have h6 := norm_integral_le_integral_norm (μ := volume.restrict (tᶜ)) B
  have h7 := norm_integral_le_integral_norm (μ := volume.restrict (sᶜ)) C
  linarith only [h1, h2, h3, h4, h5, h6, h7]

set_option maxHeartbeats 800000 in
theorem nearOrigin_contour_difference_le {n : ℕ} {r u σ : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hr₁ : r ≤ 1/40) (hu : 0 < u) (hup : 4*u ≤ Real.pi)
    (hσ : σ^2 = (n : ℝ)*r) :
    ‖(durfeeNegativeValue n r : ℂ) - nearOriginModel σ n‖ ≤
      Real.exp ((n : ℝ)*u) / (2*Real.pi) *
        ((∫ v in Icc (-(4*u)) (4*u), ‖nearOriginCentralError r u v‖) +
         (∫ v in {v : ℝ | 4*u < |v| ∧ |v| ≤ Real.pi}, ‖nearOriginMiddleError r u v‖) +
         (∫ v in {v : ℝ | Real.pi < |v|},
            ‖angularAverage (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) - 1)‖) +
         (∫ v in {v : ℝ | 4*u < |v|}, ‖angularAverage (fun θ =>
            exp (nearOriginMainLog r θ (verticalPoint u v)) *
              nearOriginCorrection r θ (verticalPoint u v))‖)) := by
  let s := Icc (-(4*u)) (4*u)
  let t := Icc (-Real.pi) Real.pi
  let E (v : ℝ) := exp ((n : ℂ) * verticalPoint u v)
  let L := durfeeExponentialMean r u
  let B (v : ℝ) := angularAverage (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) - 1)
  let C (v : ℝ) := angularAverage (fun θ =>
    exp (nearOriginMainLog r θ (verticalPoint u v)) * nearOriginCorrection r θ (verticalPoint u v))
  have hr' : |r| ≤ 1 := by rw [abs_of_pos hr]; linarith
  have hst : s ⊆ t := Icc_subset_Icc (by linarith) hup
  have hmidSet : t \ s = {v : ℝ | 4*u < |v| ∧ |v| ≤ Real.pi} := by
    ext v
    change ((-Real.pi ≤ v ∧ v ≤ Real.pi) ∧ ¬ (-(4*u) ≤ v ∧ v ≤ 4*u)) ↔
      (4*u < |v| ∧ |v| ≤ Real.pi)
    rw [← abs_le, ← abs_le, not_le, and_comm]
  have htailSet : tᶜ = {v : ℝ | Real.pi < |v|} := by
    ext v
    change ¬(-Real.pi ≤ v ∧ v ≤ Real.pi) ↔ Real.pi < |v|
    rw [← abs_le, not_le]
  have hcorrSet : sᶜ = {v : ℝ | 4*u < |v|} := by
    ext v
    change ¬(-(4*u) ≤ v ∧ v ≤ 4*u) ↔ 4*u < |v|
    rw [← abs_le, not_le]
  have hE : Continuous E := by dsimp [E, verticalPoint]; fun_prop
  have hA : IntegrableOn (fun v => E v * L v) t :=
    (hE.mul (continuous_durfeeExponentialMean hr' hu)).integrableOn_Icc
  have hB : Integrable (fun v => E v * B v) := by
    simpa only [E, B, Complex.ofReal_natCast, nearOriginAngleAverage, angularAverage] using
      integrable_nearOriginAngularBase hu r (n : ℝ)
  have hC : Integrable (fun v => E v * C v) := by
    simpa only [E, C, Complex.ofReal_natCast, nearOriginAngleAverage, angularAverage] using
      integrable_nearOriginAngularCorrection hu r (n : ℝ)
  have hsplit := norm_contour_difference_with_correction_le
    (A := fun v => E v * L v) (B := fun v => E v * B v) (C := fun v => E v * C v)
    (s := s) (t := t) measurableSet_Icc measurableSet_Icc hst hA hB hC
  have hD : (durfeeNegativeValue n r : ℂ) =
      (2 * Real.pi : ℂ)⁻¹ * ∫ v in t, E v * L v := by
    rw [durfeeNegativeValue_eq_contour hn hr' hu, angularAverage]
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_Icc_eq_integral_Ioc]
  have hQ : nearOriginModel σ n = (2 * Real.pi : ℂ)⁻¹ * ∫ v, E v * B v + E v * C v := by
    simpa only [E, B, C, nearOriginAngularModel_eq_add, nearOriginAngleAverage, angularAverage,
      mul_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (integral_nearOriginAngularModel_eq_nearOriginModel hu hn hσ).symm
  have hparam (v : ℝ) : Continuous (fun θ : ℝ => (v, θ)) :=
    continuous_const.prodMk continuous_id
  have hpair (v : ℝ) : Continuous (fun θ => exp (pairedLog r θ (verticalPoint u v))) := by
    have h := (continuous_pairedLog_vertical r hr' hu).comp (hparam v)
    exact Complex.continuous_exp.comp h
  have hmain (v : ℝ) : Continuous (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v))) := by
    have h := (continuous_nearOriginMainLog r hu).comp (hparam v)
    exact Complex.continuous_exp.comp h
  have hmid (v : ℝ) : L v - B v = nearOriginMiddleError r u v := by
    dsimp only [L, B, durfeeExponentialMean, nearOriginMiddleError]
    rw [angularAverage_sub ((hpair v).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      angularAverage_sub ((hmain v).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      angularAverage_sub ((hpair v).intervalIntegrable _ _) ((hmain v).intervalIntegrable _ _)]
    ring
  have hcentral (v : ℝ) : L v - B v - C v = nearOriginCentralError r u v := by
    rw [hmid]
    have hcorr : Continuous (fun θ => nearOriginCorrection r θ (verticalPoint u v)) :=
      (continuous_nearOriginCorrection r hu).comp (hparam v)
    dsimp only [C, nearOriginMiddleError, nearOriginCentralError]
    have hsub := angularAverage_sub
      (f := fun θ => exp (pairedLog r θ (verticalPoint u v)) -
        exp (nearOriginMainLog r θ (verticalPoint u v)))
      (g := fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) *
        nearOriginCorrection r θ (verticalPoint u v))
      (((hpair v).sub (hmain v)).intervalIntegrable _ _)
      (((hmain v).mul hcorr).intervalIntegrable _ _)
    rw [← hsub]
    congr 1
    funext θ
    ring
  have hW (v : ℝ) : ‖E v‖ = Real.exp ((n : ℝ)*u) := by
    simp [E, Complex.norm_exp, Complex.mul_re]
  have hfactor : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_of_nonneg (by positivity)]
  simp_rw [← mul_sub, norm_mul, hW, integral_const_mul] at hsplit
  rw [hD, hQ, ← mul_sub, norm_mul, hfactor]
  refine (mul_le_mul_of_nonneg_left hsplit (by positivity)).trans_eq ?_
  rw [hmidSet, htailSet, hcorrSet]
  simp_rw [hcentral, hmid]
  ring

end DurfeeCCS.Step08
