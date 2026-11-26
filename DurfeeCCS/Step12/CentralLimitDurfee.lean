module

public import DurfeeCCS.Step12.Probability
public import DurfeeCCS.Step12.BernoulliChar
public import DurfeeCCS.Step12.CentralLimit

/-! The conditional central limit theorem in the manuscript. -/

public section

namespace DurfeeCCS

open Filter MeasureTheory ProbabilityTheory Step12
open scoped Topology BigOperators

/-- One choice of Bernoulli parameters for each Durfee law. The index type is empty at size zero. -/
@[expose]
noncomputable def durfeeBernoulliParameters (n : ℕ) :
    Fin (n.sqrt - 1) → Set.Icc (0 : ℝ) 1 :=
  if hn : 1 ≤ n then
    let h := durfee_factorization n hn
    fun i => durfeeRootProbability (h.choose i) (h.choose_spec.1 i)
  else fun _ => ⟨0, by simp⟩

/-- The standardized Durfee side, using the mean and variance of the uniform law. -/
@[expose]
noncomputable def durfeeStandardized (n : ℕ) (d : ℕ) : ℝ :=
  ((d : ℝ) - durfeeMean n) / Real.sqrt (durfeeVariance n)

theorem durfeeVariance_eq_bernoulliVariance {n : ℕ} (hn : 1 ≤ n) :
    durfeeVariance n = bernoulliVariance (fun i => (durfeeBernoulliParameters n i : ℝ)) := by
  let h := durfee_factorization n hn
  let q := fun i => durfeeRootProbability (h.choose i) (h.choose_spec.1 i)
  have hl := durfeeSide_bernoulliLaw_of_factorization h.choose h.choose_spec.1 h.choose_spec.2
  have hc : Measurable (fun d : ℕ => (d : ℝ)) := Measurable.of_discrete
  rw [durfeeBernoulliParameters, dite_eq_left hn, durfeeVariance, ← hl.map_eq,
    variance_map hc.aemeasurable hl.aemeasurable]
  exact variance_shiftedBernoulliCount q

theorem charFun_durfeeStandardized {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    charFun ((durfeeDistribution n).map (durfeeStandardized n)) t =
      ∏ i, centeredBernoulliChar (durfeeBernoulliParameters n i : ℝ)
        (t / Real.sqrt (durfeeVariance n)) := by
  let h := durfee_factorization n hn
  let q := fun i => durfeeRootProbability (h.choose i) (h.choose_spec.1 i)
  have hl := durfeeSide_bernoulliLaw_of_factorization h.choose h.choose_spec.1 h.choose_spec.2
  have hμ : durfeeMean n = 1 + ∑ i, (q i : ℝ) := by
    simpa [q] using
      (durfeeSide_moments_of_factorization h.choose h.choose_spec.1 h.choose_spec.2).1
  rw [durfeeBernoulliParameters, dite_eq_left hn, ← hl.map_eq,
    Measure.map_map (show Measurable (durfeeStandardized n) from Measurable.of_discrete)
      measurable_shiftedBernoulliCount]
  change charFun ((bernoulliProduct q).map (fun ω =>
    ((shiftedBernoulliCount ω : ℝ) - durfeeMean n) / Real.sqrt (durfeeVariance n))) t = _
  rw [hμ]
  exact charFun_centered_shiftedBernoulliCount q _ _

/-- If the variance tends to infinity, the standardized side of a uniformly chosen
ordinary partition converges in distribution to the standard Gaussian. -/
theorem durfeeSide_central_limit (hV : Tendsto durfeeVariance atTop atTop) :
    TendstoInDistribution
      (fun n (P : Nat.Partition n) => durfeeStandardized n (partitionSide P)) atTop
      (id : ℝ → ℝ) uniformPartitionMeasure (gaussianReal 0 1) := by
  have hn : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hV' : Tendsto
      (fun n => bernoulliVariance (fun i => (durfeeBernoulliParameters n i : ℝ))) atTop atTop :=
    hV.congr' (hn.mono fun _ hn' => durfeeVariance_eq_bernoulliVariance hn')
  apply TendstoInDistribution.of_tendsto_charFun
    (fun _ => Measurable.of_discrete.aemeasurable) measurable_id.aemeasurable
  intro t
  have hG : charFun (gaussianReal 0 1) t = Complex.exp (↑(-(t ^ 2) / 2 : ℝ)) := by
    rw [charFun_gaussianReal]
    push_cast
    ring_nf
  rw [Measure.map_id, hG]
  apply (tendsto_prod_centeredBernoulliChar
    (fun n i => (durfeeBernoulliParameters n i : ℝ))
    (fun n i => (durfeeBernoulliParameters n i).property) hV' t).congr'
  filter_upwards [hn] with n hn'
  rw [show (fun P : Nat.Partition n => durfeeStandardized n (partitionSide P)) =
      durfeeStandardized n ∘ partitionSide by rfl,
    ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    ← durfeeDistribution, charFun_durfeeStandardized hn',
    durfeeVariance_eq_bernoulliVariance hn']

end DurfeeCCS
