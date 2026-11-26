module

public import DurfeeCCS.Step12.CentralLimitDurfee
public import DurfeeCCS.Step12.LatticeLaw
public import DurfeeCCS.Step12.LocalLimit

/-! The local central limit theorem for the Durfee side of a uniform partition. -/

public section

namespace DurfeeCCS

open Filter Topology MeasureTheory ProbabilityTheory

/-- The density in the local theorem agrees with the standard Gaussian density
used for the central limit theorem. -/
theorem standardNormalDensity_eq_gaussianPDFReal (x : ℝ) :
    standardNormalDensity x = gaussianPDFReal 0 1 x := by
  rw [standardNormalDensity, gaussianPDFReal_def]
  simp [div_eq_mul_inv, mul_comm]

/-- The lattice mass is the probability that a uniform partition has the given
Durfee side, including when the given integer is negative. -/
theorem durfeeLatticeMass_eq_uniform_probability (n : ℕ) (k : ℤ) :
    durfeeLatticeMass n k =
      (uniformPartitionMeasure n).real {P | (partitionSide P : ℤ) = k} := by
  rw [durfeeLatticeMass]
  by_cases hk : 0 ≤ k
  · have hcast := Int.toNat_of_nonneg hk
    have hevent : {P : Nat.Partition n | (partitionSide P : ℤ) = k} =
        (@partitionSide n) ⁻¹' {k.toNat} := by
      ext P
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      omega
    rw [ite_eq_left hk, hevent, ← map_measureReal_apply Measurable.of_discrete
      (measurableSet_singleton k.toNat), ← durfeeDistribution, durfeeDistribution_singleton_toReal]
  · have hevent : {P : Nat.Partition n | (partitionSide P : ℤ) = k} = ∅ := by
      ext P
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    simp [hk, hevent]

/-- Whenever the variance of the uniform Durfee side diverges, its masses, scaled
by the standard deviation, approach the normal density uniformly over the lattice. -/
theorem durfeeSide_local_limit (hVar : Tendsto durfeeVariance atTop atTop) :
    Tendsto (fun n : ℕ => ⨆ k : ℤ,
      |Real.sqrt (durfeeVariance n) * durfeeLatticeMass n k -
        standardNormalDensity (((k : ℝ) - durfeeMean n) / Real.sqrt (durfeeVariance n))|)
      atTop (𝓝 0) := by
  let q (n : ℕ) (i : Fin (n.sqrt - 1)) : ℝ := durfeeBernoulliParameters n i
  have hq (n : ℕ) (i : Fin (n.sqrt - 1)) : q n i ∈ Set.Icc (0 : ℝ) 1 :=
    (durfeeBernoulliParameters n i).property
  have hvar {n : ℕ} (hn : 1 ≤ n) : durfeeVariance n = bernoulliVariance (q n) :=
    durfeeVariance_eq_bernoulliVariance hn
  have hV : Tendsto (fun n => bernoulliVariance (q n)) atTop atTop := by
    apply hVar.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact hvar hn
  have hfactor : ∀ᶠ n in atTop, ∀ t,
      latticeChar (durfeeLatticeSupport n) (durfeeLatticeMass n) (durfeeMean n)
          (Real.sqrt (bernoulliVariance (q n))) t =
        ∏ i, centeredBernoulliChar (q n i) (t / Real.sqrt (bernoulliVariance (q n))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    intro t
    rw [← hvar hn]
    have hsum := charFun_durfeeDistribution_centered n (durfeeMean n)
      (Real.sqrt (durfeeVariance n)) t
    change charFun ((durfeeDistribution n).map (durfeeStandardized n)) t = _ at hsum
    rw [charFun_durfeeStandardized hn t] at hsum
    simpa only [latticeChar, q, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div]
      using hsum.symm
  have hlimit := tendsto_iSup_bernoulliLatticeMass_standardNormal q hq
    durfeeLatticeSupport durfeeLatticeMass durfeeMean (fun _ _ => durfeeLatticeMass_outside)
    hV hfactor
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [← hvar hn]

end DurfeeCCS
