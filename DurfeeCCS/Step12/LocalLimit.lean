module

public import DurfeeCCS.Step12.CentralLimitChar
public import DurfeeCCS.Step12.LocalLimitBounds
public import DurfeeCCS.Step12.LocalLimitFourier

/-! The lattice local central limit theorem for sums of finite Bernoulli rows. -/

@[expose] public section

open Filter Topology

namespace DurfeeCCS

/-- For finitely supported integer masses whose standardized characteristic functions are
products of centered Bernoulli factors, divergence of total variance implies uniform
local convergence to the standard normal density. The center `μ` may include a
deterministic shift, which disappears in the standardized characteristic function. -/
theorem tendsto_iSup_bernoulliLatticeMass_standardNormal
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (p : ∀ n, ι n → ℝ)
    (hp : ∀ n i, p n i ∈ Set.Icc (0 : ℝ) 1)
    (s : ℕ → Finset ℤ) (mass : ℕ → ℤ → ℝ) (μ : ℕ → ℝ)
    (hmass : ∀ n k, k ∉ s n → mass n k = 0)
    (hV : Tendsto (fun n ↦ bernoulliVariance (p n)) atTop atTop)
    (hfactor : ∀ᶠ n in atTop, ∀ t,
      latticeChar (s n) (mass n) (μ n) (Real.sqrt (bernoulliVariance (p n))) t =
        ∏ i, centeredBernoulliChar (p n i) (t / Real.sqrt (bernoulliVariance (p n)))) :
    Tendsto (fun n ↦ ⨆ k : ℤ,
      |Real.sqrt (bernoulliVariance (p n)) * mass n k -
        standardNormalDensity (((k : ℝ) - μ n) / Real.sqrt (bernoulliVariance (p n)))|)
      atTop (𝓝 0) := by
  refine tendsto_iSup_latticeMass_standardNormal s mass μ _ hmass
    (Real.tendsto_sqrt_atTop.comp hV) ?_ (c := 2 / Real.pi ^ 2) (by positivity) ?_
  · intro t
    apply (tendsto_prod_centeredBernoulliChar p hp hV t).congr'
    exact hfactor.mono fun n hn ↦ (hn t).symm
  · filter_upwards [hfactor, hV.eventually (eventually_gt_atTop 0)] with n hn hpos t ht
    rw [hn t, prod_centeredBernoulliChar_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_prod_bernoulliFactor_le_gaussian (p n) _ rfl hpos t ht

end DurfeeCCS
