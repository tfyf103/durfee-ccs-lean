module

public import DurfeeCCS.Scalars
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Ring

/-! The finite product model for sums of independent Bernoulli random variables. -/

public section

namespace DurfeeCCS.Step12

open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The product of the binary Bernoulli probability measures for the given success probabilities. -/
@[expose]
noncomputable def bernoulliProduct (q : ι → Set.Icc (0 : ℝ) 1) : Measure (ι → Bool) :=
  Measure.pi fun i => bernoulliMeasure true false (q i)

instance (q : ι → Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (bernoulliProduct q) := by
  unfold bernoulliProduct
  infer_instance

/-- The value of a coordinate, regarded as a natural number. -/
@[expose]
def bernoulliCoordinate (i : ι) (ω : ι → Bool) : ℕ := (ω i).toNat

/-- The value of the sum of the coordinates, shifted by one. -/
@[expose]
def shiftedBernoulliCount (ω : ι → Bool) : ℕ := 1 + ∑ i, bernoulliCoordinate i ω

theorem measurable_shiftedBernoulliCount : Measurable (shiftedBernoulliCount : (ι → Bool) → ℕ) :=
  Measurable.of_discrete

theorem iIndepFun_bernoulliCoordinate (q : ι → Set.Icc (0 : ℝ) 1) :
    iIndepFun bernoulliCoordinate (bernoulliProduct q) :=
  iIndepFun_pi (X := fun _ => Bool.toNat) (fun _ => Measurable.of_discrete.aemeasurable)

theorem hasLaw_bernoulliCoordinate (q : ι → Set.Icc (0 : ℝ) 1) (i : ι) :
    HasLaw (bernoulliCoordinate i) (bernoulliMeasure (1 : ℕ) 0 (q i)) (bernoulliProduct q) := by
  refine ⟨Measurable.of_discrete.aemeasurable, ?_⟩
  change (bernoulliProduct q).map (Bool.toNat ∘ fun ω : ι → Bool => ω i) = _
  unfold bernoulliProduct
  rw [← Measure.map_map (g := Bool.toNat) Measurable.of_discrete (measurable_pi_apply i),
    (measurePreserving_eval (fun i => bernoulliMeasure true false (q i)) i).map_eq,
    map_bernoulliMeasure]
  rfl

theorem measureReal_bernoulliCoordinate_one (q : ι → Set.Icc (0 : ℝ) 1) (i : ι) :
    (bernoulliProduct q).real (bernoulliCoordinate i ⁻¹' {1}) = (q i : ℝ) := by
  classical
  have h := hasLaw_bernoulliCoordinate q i
  rw [← map_measureReal_apply_of_aemeasurable h.aemeasurable (measurableSet_singleton _), h.map_eq]
  simp

/-- The probability generating function of the shifted sum. -/
noncomputable def shiftedBernoulliPGF (q : ι → Set.Icc (0 : ℝ) 1) : ℝ[X] := by
  classical
  exact ∑ ω : ι → Bool, C ((bernoulliProduct q).real {ω}) * X ^ shiftedBernoulliCount ω

/-- The coefficients of the finite generating function are the probabilities of the count. -/
theorem shiftedBernoulliPGF_coeff (q : ι → Set.Icc (0 : ℝ) 1) (d : ℕ) :
    (shiftedBernoulliPGF q).coeff d = (bernoulliProduct q).real (shiftedBernoulliCount ⁻¹' {d}) := by
  classical
  let s : Finset (ι → Bool) := Finset.univ.filter fun ω => shiftedBernoulliCount ω = d
  have hs : (s : Set (ι → Bool)) = shiftedBernoulliCount ⁻¹' {d} := by
    ext ω
    simp [s]
  rw [← hs, ← sum_measureReal_singleton]
  simp only [shiftedBernoulliPGF, finsetSum_coeff, coeff_C_mul_X_pow, s, Finset.sum_filter, eq_comm]

/-- The factorization into the generating functions of the independent coordinates. -/
theorem shiftedBernoulliPGF_factorization (q : ι → Set.Icc (0 : ℝ) 1) :
    shiftedBernoulliPGF q = X * ∏ i, (C (1 - (q i : ℝ)) + C (q i : ℝ) * X) := by
  classical
  let f (i : ι) (b : Bool) : ℝ[X] :=
    C ((bernoulliMeasure true false (q i)).real {b}) * X ^ b.toNat
  have hsingle (ω : ι → Bool) :
      (bernoulliProduct q).real {ω} = ∏ i, (bernoulliMeasure true false (q i)).real {ω i} := by
    simp [bernoulliProduct, measureReal_def, ENNReal.toReal_prod]
  calc
    shiftedBernoulliPGF q = X * ∑ ω : ι → Bool, ∏ i, f i (ω i) := by
      rw [shiftedBernoulliPGF, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [hsingle, map_prod, shiftedBernoulliCount, pow_add]
      simp only [f, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, bernoulliCoordinate, pow_one]
      ring
    _ = X * ∏ i, ∑ b : Bool, f i b := by rw [Fintype.prod_sum]
    _ = _ := by
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Fintype.sum_bool]
      simp [f, bernoulliMeasure_real_apply, add_comm]

private theorem coe_shiftedBernoulliCount (ω : ι → Bool) :
    (shiftedBernoulliCount ω : ℝ) = 1 + ∑ i, ((ω i).toNat : ℝ) := by
  simp [shiftedBernoulliCount, bernoulliCoordinate]

/-- The expectation of a shifted sum of independent Bernoulli coordinates. -/
theorem integral_shiftedBernoulliCount (q : ι → Set.Icc (0 : ℝ) 1) :
    ∫ ω, (shiftedBernoulliCount ω : ℝ) ∂(bernoulliProduct q) = 1 + ∑ i, (q i : ℝ) := by
  simp only [coe_shiftedBernoulliCount]
  rw [integral_add (integrable_const _) (Integrable.of_finite), integral_const, integral_finsetSum]
  · simp only [probReal_univ, one_smul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    let h : HasLaw (fun ω : ι → Bool => ω i)
        (bernoulliMeasure true false (q i)) (bernoulliProduct q) :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
    exact (h.integral_comp (f := fun b => (b.toNat : ℝ)) .of_discrete).trans
      (by simp [integral_bernoulliMeasure])
  · exact fun _ _ => Integrable.of_finite

/-- The variance is the sum of the coordinate variances. -/
theorem variance_shiftedBernoulliCount (q : ι → Set.Icc (0 : ℝ) 1) :
    variance (fun ω => (shiftedBernoulliCount ω : ℝ)) (bernoulliProduct q) =
      ∑ i, (q i : ℝ) * (1 - (q i : ℝ)) := by
  simp only [coe_shiftedBernoulliCount]
  rw [variance_const_add AEStronglyMeasurable.of_discrete]
  rw [← Finset.sum_fn Finset.univ (fun i (ω : ι → Bool) => ((ω i).toNat : ℝ))]
  rw [bernoulliProduct, variance_sum_pi (μ := fun i => bernoulliMeasure true false (q i))
    (X := fun _ b => (b.toNat : ℝ)) (fun _ => .of_discrete)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [variance_eq_integral Measurable.of_discrete.aemeasurable]
  simp [integral_bernoulliMeasure]
  ring

/-- For an empty index type, the count is deterministically one. -/
theorem shiftedBernoulliCount_of_isEmpty [IsEmpty ι] (ω : ι → Bool) :
    shiftedBernoulliCount ω = 1 := by
  simp [shiftedBernoulliCount]

/-- The shifted sum over an empty family has a point mass at one. -/
theorem map_shiftedBernoulliCount_of_isEmpty [IsEmpty ι] (q : ι → Set.Icc (0 : ℝ) 1) :
    (bernoulliProduct q).map shiftedBernoulliCount = Measure.dirac 1 := by
  have h : (shiftedBernoulliCount : (ι → Bool) → ℕ) = fun _ => 1 :=
    funext shiftedBernoulliCount_of_isEmpty
  simp [h]

end DurfeeCCS.Step12
