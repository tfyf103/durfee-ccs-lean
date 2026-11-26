module

public import DurfeeCCS.Step06.AngleCoefficients
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Fourier inversion and uniform local approximation for finitely supported lattice laws. -/

@[expose] public section

open Complex Filter MeasureTheory Set Topology

namespace DurfeeCCS

/-- The density of a standard normal law. -/
noncomputable def standardNormalDensity (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- The characteristic function of a standard normal law. -/
noncomputable def standardNormalChar (t : ℝ) : ℂ :=
  Complex.exp (((-(t ^ 2) / 2 : ℝ)) : ℂ)

/-- The characteristic function of a centered and scaled finite lattice mass. -/
noncomputable def latticeChar (s : Finset ℤ) (mass : ℤ → ℝ) (μ σ t : ℝ) : ℂ :=
  ∑ j ∈ s, (mass j : ℂ) * Complex.exp (((j : ℝ) - μ) * (t / σ) * I)

noncomputable def latticeFourierPhase (x t : ℝ) : ℂ :=
  Complex.exp (((-x * t : ℝ) : ℂ) * I)

private theorem continuous_phase (x : ℝ) : Continuous (latticeFourierPhase x) := by
  unfold latticeFourierPhase
  fun_prop

private theorem norm_phase (x t : ℝ) : ‖latticeFourierPhase x t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

private theorem continuous_standardNormalChar : Continuous standardNormalChar := by
  unfold standardNormalChar
  fun_prop

private theorem norm_standardNormalChar (t : ℝ) :
    ‖standardNormalChar t‖ = Real.exp (-t ^ 2 / 2) := by
  exact Complex.norm_exp_ofReal _

/-- The positive Gaussian density is the inverse Fourier transform of its characteristic
function in the angular normalization. -/
theorem standardNormal_fourier_inversion (x : ℝ) :
    (∫ t : ℝ, latticeFourierPhase x t * standardNormalChar t) =
      ((2 * Real.pi * standardNormalDensity x : ℝ) : ℂ) := by
  have heq (t : ℝ) :
      latticeFourierPhase x t * standardNormalChar t =
        Complex.exp (I * (-(x : ℂ)) * (t : ℂ)) *
          Complex.exp (-(1 / 2 : ℂ) * (t : ℂ) ^ 2) := by
    unfold latticeFourierPhase standardNormalChar
    push_cast
    congr 1 <;> congr 1 <;> ring
  simp_rw [heq]
  rw [fourierIntegral_gaussian (by norm_num : 0 < (1 / 2 : ℂ).re)]
  have hπ : 0 < 2 * Real.pi := by positivity
  have hp : (Real.pi : ℂ) / (1 / 2 : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  have he : (-( -(x : ℂ)) ^ 2 / (4 * (1 / 2 : ℂ))) =
      (((-(x ^ 2) / 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  have hpow : ((2 * Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hπ.le]
    norm_num
  rw [hp, he, hpow, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  congr 1
  unfold standardNormalDensity
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 hπ
  have hsq := Real.sq_sqrt hπ.le
  calc
    _ = Real.sqrt (2 * Real.pi) ^ 2 *
        (Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)) := by
      field_simp [hs.ne']
    _ = _ := by rw [hsq]

private theorem integrable_standardNormal_phase (x : ℝ) :
    Integrable (fun t ↦ latticeFourierPhase x t * standardNormalChar t) := by
  refine (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 / 2 by norm_num)).mono'
    (((continuous_phase x).mul continuous_standardNormalChar).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_mul, norm_phase, one_mul, norm_standardNormalChar]
  exact le_of_eq (congrArg Real.exp (by ring))

private theorem continuous_latticeChar (s : Finset ℤ) (mass : ℤ → ℝ) (μ σ : ℝ) :
    Continuous (latticeChar s mass μ σ) := by
  unfold latticeChar
  fun_prop

/-- Inversion for an integer-valued finite mass, after scaling the Fourier variable. -/
theorem latticeChar_fourier_inversion (s : Finset ℤ) (mass : ℤ → ℝ) (μ σ : ℝ)
    (hσ : 0 < σ) (hmass : ∀ k ∉ s, mass k = 0) (k : ℤ) :
    (∫ t in -(Real.pi * σ)..(Real.pi * σ),
        latticeFourierPhase (((k : ℝ) - μ) / σ) t * latticeChar s mass μ σ t) =
      ((2 * Real.pi * σ * mass k : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun v ↦ ∑ j ∈ s, (mass j : ℂ) * Complex.exp (((j - k : ℤ) : ℂ) * I * v)
  have hf (v : ℝ) :
      latticeFourierPhase (((k : ℝ) - μ) / σ) (v * σ) * latticeChar s mass μ σ (v * σ) = f v := by
    unfold latticeChar f latticeFourierPhase
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    have h1 : (-(((k : ℝ) - μ) / σ) * (v * σ)) = -((k : ℝ) - μ) * v := by
      field_simp
    have h2 : ((v * σ : ℝ) : ℂ) / (σ : ℂ) = (v : ℂ) := by
      rw [Complex.ofReal_mul, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hσ.ne')]
    rw [h1, h2]
    push_cast
    ring
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (a := -Real.pi) (b := Real.pi)
    (fun t ↦ latticeFourierPhase (((k : ℝ) - μ) / σ) t * latticeChar s mass μ σ t) σ
  simp_rw [hf] at hsub
  rw [neg_mul] at hsub
  rw [← hsub]
  have hterm (j : ℤ) :
      (∫ v : ℝ in -Real.pi..Real.pi,
        (mass j : ℂ) * Complex.exp (((j - k : ℤ) : ℂ) * I * v)) =
        if j = k then (2 * Real.pi : ℂ) * mass k else 0 := by
    rw [intervalIntegral.integral_const_mul, Step06.integral_integer_mode]
    by_cases hj : j = k
    · subst j
      simp only [sub_self, ↓reduceIte, mul_comm (mass k : ℂ)]
    · simp [sub_ne_zero.mpr hj, hj]
  unfold f
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [hterm]
    rw [Finset.sum_ite_eq']
    by_cases hk : k ∈ s
    · simp only [hk, ↓reduceIte, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    · simp [hk, hmass k hk]
  · intro j hj
    exact Continuous.intervalIntegrable (by fun_prop) _ _

private noncomputable def fourierCutoff (σ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Ioc (-(Real.pi * σ)) (Real.pi * σ)).indicator f

private theorem latticeFourierPhase_mul_cutoff (x σ : ℝ) (f : ℝ → ℂ) (t : ℝ) :
    latticeFourierPhase x t * fourierCutoff σ f t =
      fourierCutoff σ (fun u ↦ latticeFourierPhase x u * f u) t := by
  unfold fourierCutoff
  by_cases ht : t ∈ Ioc (-(Real.pi * σ)) (Real.pi * σ)
  · simp [Set.indicator_of_mem ht]
  · simp [Set.indicator_of_notMem ht]

private theorem integrable_fourierCutoff (σ : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (fourierCutoff σ f) :=
  (hf.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator
    measurableSet_Ioc

/-- Under a Gaussian bound in the Fourier window, pointwise characteristic convergence gives
convergence uniformly over all integer lattice points. -/
theorem tendsto_iSup_latticeMass_standardNormal
    (s : ℕ → Finset ℤ) (mass : ℕ → ℤ → ℝ) (μ σ : ℕ → ℝ)
    (hmass : ∀ n k, k ∉ s n → mass n k = 0)
    (hσ : Tendsto σ atTop atTop)
    (hchar : ∀ t, Tendsto (fun n ↦ latticeChar (s n) (mass n) (μ n) (σ n) t)
      atTop (𝓝 (standardNormalChar t)))
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ n in atTop, ∀ t, |t| ≤ Real.pi * σ n →
      ‖latticeChar (s n) (mass n) (μ n) (σ n) t‖ ≤ Real.exp (-c * t ^ 2)) :
    Tendsto (fun n ↦ ⨆ k : ℤ,
      |σ n * mass n k - standardNormalDensity (((k : ℝ) - μ n) / σ n)|)
      atTop (𝓝 0) := by
  let F : ℕ → ℝ → ℂ := fun n ↦ fourierCutoff (σ n) (latticeChar (s n) (mass n) (μ n) (σ n))
  let err : ℕ → ℝ → ℝ := fun n t ↦ ‖F n t - standardNormalChar t‖
  have hσpos : ∀ᶠ n in atTop, 0 < σ n := hσ.eventually (eventually_gt_atTop 0)
  have hFi (n : ℕ) : Integrable (F n) :=
    integrable_fourierCutoff _ (continuous_latticeChar _ _ _ _)
  have hFi_phase (n : ℕ) (x : ℝ) : Integrable (fun t ↦ latticeFourierPhase x t * F n t) := by
    simp_rw [F, latticeFourierPhase_mul_cutoff]
    exact integrable_fourierCutoff _ ((continuous_phase _).mul (continuous_latticeChar _ _ _ _))
  have hlim (t : ℝ) : Tendsto (fun n ↦ F n t) atTop (𝓝 (standardNormalChar t)) := by
    apply (hchar t).congr'
    filter_upwards [hσ.eventually (eventually_gt_atTop (|t| / Real.pi))] with n hn
    have h : |t| < Real.pi * σ n := by
      rw [div_lt_iff₀ Real.pi_pos] at hn
      simpa only [mul_comm] using hn
    have ht : t ∈ Ioc (-(Real.pi * σ n)) (Real.pi * σ n) :=
      ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le⟩
    exact (Set.indicator_of_mem ht _).symm
  have hdom : ∀ᶠ n in atTop, ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      ‖err n t‖ ≤ Real.exp (-c * t ^ 2) + Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    filter_upwards [hbound] with n hn
    filter_upwards with t
    have hF : ‖F n t‖ ≤ Real.exp (-c * t ^ 2) := by
      unfold F fourierCutoff
      by_cases ht : t ∈ Ioc (-(Real.pi * σ n)) (Real.pi * σ n)
      · rw [Set.indicator_of_mem ht]
        exact hn t (abs_le.mpr ⟨ht.1.le, ht.2⟩)
      · rw [Set.indicator_of_notMem ht, norm_zero]
        positivity
    have hG : ‖standardNormalChar t‖ = Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [norm_standardNormalChar]
      congr 1
      ring
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (add_le_add hF hG.le)
  have herr : Tendsto (fun n ↦ ∫ t : ℝ, err n t) atTop (𝓝 0) := by
    have hd := tendsto_integral_filter_of_dominated_convergence
      (F := err) (f := fun _ ↦ (0 : ℝ))
      (fun t ↦ Real.exp (-c * t ^ 2) + Real.exp (-(1 / 2 : ℝ) * t ^ 2))
      (.of_forall fun n ↦ ((hFi n).aestronglyMeasurable.sub
        continuous_standardNormalChar.aestronglyMeasurable).norm)
      hdom
      ((integrable_exp_neg_mul_sq hc).add (integrable_exp_neg_mul_sq (by norm_num)))
      (ae_of_all _ fun t ↦ by
        simpa [err] using ((hlim t).sub (tendsto_const_nhds (x := standardNormalChar t))).norm)
    simpa using hd
  have hπ : 0 < 2 * Real.pi := by positivity
  have hUpper : ∀ᶠ n in atTop, ∀ k : ℤ,
      |σ n * mass n k - standardNormalDensity (((k : ℝ) - μ n) / σ n)| ≤
      (2 * Real.pi)⁻¹ * ∫ t : ℝ, err n t := by
    filter_upwards [hσpos] with n hn k
    let x : ℝ := ((k : ℝ) - μ n) / σ n
    change |σ n * mass n k - standardNormalDensity x| ≤ _
    have hF : (∫ t : ℝ, latticeFourierPhase x t * F n t) = ((2 * Real.pi * σ n * mass n k : ℝ) : ℂ) := by
      simp_rw [F, latticeFourierPhase_mul_cutoff]
      unfold fourierCutoff
      rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (neg_le_self (mul_nonneg Real.pi_pos.le hn.le))]
      exact latticeChar_fourier_inversion _ _ _ _ hn (hmass n) k
    have hG := standardNormal_fourier_inversion x
    have hh : (∫ t : ℝ, latticeFourierPhase x t * (F n t - standardNormalChar t)) =
        ((2 * Real.pi * (σ n * mass n k - standardNormalDensity x) : ℝ) : ℂ) := by
      simp_rw [mul_sub]
      rw [integral_sub (hFi_phase n x) (integrable_standardNormal_phase x), hF, hG]
      rw [← Complex.ofReal_sub]
      congr 1
      ring
    have hu := norm_integral_le_integral_norm (μ := volume)
      (fun t : ℝ ↦ latticeFourierPhase x t * (F n t - standardNormalChar t))
    simp_rw [norm_mul, norm_phase, one_mul] at hu
    rw [hh, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hπ] at hu
    have hu' := (le_inv_mul_iff₀ hπ).2 hu
    simpa only [err] using hu'
  have herrorlim : Tendsto (fun n ↦ (2 * Real.pi)⁻¹ * ∫ t : ℝ, err n t) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := (2 * Real.pi)⁻¹)).mul herr
  apply squeeze_zero' ?_ ?_ herrorlim
  · filter_upwards [hUpper] with n hn
    have hb : BddAbove (range fun k : ℤ ↦
        |σ n * mass n k - standardNormalDensity (((k : ℝ) - μ n) / σ n)|) := by
      refine ⟨(2 * Real.pi)⁻¹ * ∫ t : ℝ, err n t, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact hn k
    exact (abs_nonneg _).trans (le_ciSup hb 0)
  · exact hUpper.mono fun n hn ↦ ciSup_le hn

end DurfeeCCS
