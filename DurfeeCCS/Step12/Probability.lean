module

public import DurfeeCCS.Step12.FiniteLaw
public import DurfeeCCS.Step12.Bernoulli

/-! The Bernoulli representation and moments of the uniform Durfee side (Corollary 1.3). -/

public section

namespace DurfeeCCS

open MeasureTheory ProbabilityTheory Polynomial Step12
open scoped BigOperators

/-- The expectation of the Durfee side for a partition chosen uniformly at size n. -/
noncomputable def durfeeMean (n : ℕ) : ℝ :=
  ∫ d : ℕ, (d : ℝ) ∂durfeeDistribution n

/-- The variance of the Durfee side under the same uniform law. -/
@[expose]
noncomputable def durfeeVariance (n : ℕ) : ℝ :=
  variance (fun d : ℕ => (d : ℝ)) (durfeeDistribution n)

/-- Equality of the Durfee law and the law of the shifted sum of independent Bernoulli
variables, with the probabilities determined by the radii of the roots. -/
theorem durfeeSide_bernoulliLaw_of_factorization {n : ℕ}
    (r : Fin (n.sqrt - 1) ↪ ℝ) (hr : ∀ i, 0 < r i)
    (hfac : durfeePolynomialReal n = C (p n n.sqrt : ℝ) * X * ∏ i, (X + C (r i))) :
    HasLaw shiftedBernoulliCount (durfeeDistribution n)
      (bernoulliProduct (fun i => durfeeRootProbability (r i) (hr i))) := by
  let q (i : Fin (n.sqrt - 1)) := durfeeRootProbability (r i) (hr i)
  have hm : Measurable (shiftedBernoulliCount : (Fin (n.sqrt - 1) → Bool) → ℕ) :=
    measurable_shiftedBernoulliCount
  refine ⟨hm.aemeasurable, ?_⟩
  have hpgf : shiftedBernoulliPGF q = durfeePGF n := by
    rw [shiftedBernoulliPGF_factorization, durfeePGF_factorization r hr hfac]
  change (bernoulliProduct q).map shiftedBernoulliCount = durfeeDistribution n
  let : IsProbabilityMeasure ((bernoulliProduct q).map shiftedBernoulliCount) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply ext_iff_measureReal_singleton.mpr
  intro d
  rw [map_measureReal_apply hm (measurableSet_singleton d),
    ← shiftedBernoulliPGF_coeff, hpgf, coeff_durfeePGF,
    durfeeDistribution_singleton_toReal]

/-- The expectation and variance for any enumeration of the nonzero roots. -/
theorem durfeeSide_moments_of_factorization {n : ℕ}
    (r : Fin (n.sqrt - 1) ↪ ℝ) (hr : ∀ i, 0 < r i)
    (hfac : durfeePolynomialReal n = C (p n n.sqrt : ℝ) * X * ∏ i, (X + C (r i))) :
    durfeeMean n = 1 + ∑ i, 1 / (1 + r i) ∧
      durfeeVariance n = ∑ i, r i / (1 + r i) ^ 2 := by
  let q (i : Fin (n.sqrt - 1)) := durfeeRootProbability (r i) (hr i)
  have hl := durfeeSide_bernoulliLaw_of_factorization r hr hfac
  have hcast : Measurable (fun d : ℕ => (d : ℝ)) := Measurable.of_discrete
  constructor
  · rw [durfeeMean, ← hl.map_eq, integral_map hl.aemeasurable hcast.aestronglyMeasurable]
    simpa [q] using integral_shiftedBernoulliCount q
  · rw [durfeeVariance, ← hl.map_eq, variance_map hcast.aemeasurable hl.aemeasurable]
    change variance (fun ω => (shiftedBernoulliCount ω : ℝ)) (bernoulliProduct q) = _
    rw [variance_shiftedBernoulliCount q]
    apply Finset.sum_congr rfl
    intro i _
    have hne : (1 : ℝ) + r i ≠ 0 := ne_of_gt (by linarith [hr i])
    simp only [q, durfeeRootProbability_val]
    field_simp [hne]
    ring

/-- Corollary 1.3: the explicit independent Bernoulli model of the uniform Durfee side,
with the stated expectation and variance. -/
theorem durfeeSide_bernoulli_mean_variance (n : ℕ) (hn : 1 ≤ n) :
    ∃ (r : Fin (n.sqrt - 1) ↪ ℝ) (hr : ∀ i, 0 < r i),
      durfeePolynomialReal n = C (p n n.sqrt : ℝ) * X * (∏ i, (X + C (r i))) ∧
      (let q := fun i => durfeeRootProbability (r i) (hr i)
       iIndepFun bernoulliCoordinate (bernoulliProduct q) ∧
        (∀ i, HasLaw (bernoulliCoordinate i) (bernoulliMeasure (1 : ℕ) 0 (q i))
          (bernoulliProduct q)) ∧
        HasLaw shiftedBernoulliCount (durfeeDistribution n) (bernoulliProduct q) ∧
        durfeeMean n = 1 + ∑ i, 1 / (1 + r i) ∧
        durfeeVariance n = ∑ i, r i / (1 + r i) ^ 2) := by
  obtain ⟨r, hr, hfac⟩ := durfee_factorization n hn
  exact ⟨r, hr, hfac, iIndepFun_bernoulliCoordinate _, hasLaw_bernoulliCoordinate _,
    durfeeSide_bernoulliLaw_of_factorization r hr hfac,
    durfeeSide_moments_of_factorization r hr hfac⟩

/-- When the degree is one, the empty Bernoulli sum gives mean one and variance zero. -/
theorem durfeeSide_moments_of_sqrt_eq_one {n : ℕ} (h : n.sqrt = 1) :
    durfeeMean n = 1 ∧ durfeeVariance n = 0 := by
  have hn : 1 ≤ n := by simpa [h] using Nat.sqrt_le n
  obtain ⟨r, hr, hfac⟩ := durfee_factorization n hn
  have : IsEmpty (Fin (n.sqrt - 1)) := by rw [h, Nat.sub_self]; infer_instance
  simpa using durfeeSide_moments_of_factorization r hr hfac

end DurfeeCCS
