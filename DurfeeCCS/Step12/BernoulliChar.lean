module

public import DurfeeCCS.Step12.Bernoulli
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-! Characteristic functions under the finite Bernoulli product measure. -/

public section

namespace DurfeeCCS.Step12

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The shift cancels when the shifted Bernoulli sum is centered at its expectation. -/
theorem charFun_centered_shiftedBernoulliCount
    (q : ι → Set.Icc (0 : ℝ) 1) (σ t : ℝ) :
    charFun ((bernoulliProduct q).map (fun ω =>
      ((shiftedBernoulliCount ω : ℝ) - (1 + ∑ i, (q i : ℝ))) / σ)) t =
      ∏ i, (((1 - (q i : ℝ) : ℝ) : ℂ) *
          Complex.exp ((↑(-(q i : ℝ) * (t / σ) : ℝ) : ℂ) * Complex.I) +
        (q i : ℂ) *
          Complex.exp ((↑((1 - (q i : ℝ)) * (t / σ) : ℝ) : ℂ) * Complex.I)) := by
  have hm : Measurable (fun ω : ι → Bool =>
      ((shiftedBernoulliCount ω : ℝ) - (1 + ∑ i, (q i : ℝ))) / σ) :=
    Measurable.of_discrete
  rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
  have harg (ω : ι → Bool) :
      (t : ℂ) * (↑(((shiftedBernoulliCount ω : ℝ) - (1 + ∑ i, (q i : ℝ))) / σ) : ℂ) *
          Complex.I =
        ∑ i, (↑(((ω i).toNat : ℝ) - (q i : ℝ)) : ℂ) * (↑(t / σ) : ℂ) * Complex.I := by
    simp only [shiftedBernoulliCount, Nat.cast_add, Nat.cast_one, Nat.cast_sum,
      bernoulliCoordinate, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
      Complex.ofReal_div, Complex.ofReal_sum, ← Finset.sum_mul]
    ring
  simp_rw [harg, Complex.exp_sum]
  unfold bernoulliProduct
  rw [integral_fintype_prod_eq_prod (E := fun _ => Bool) (fun i b =>
    Complex.exp ((↑((b.toNat : ℝ) - (q i : ℝ)) : ℂ) * (↑(t / σ) : ℂ) * Complex.I))]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_bernoulliMeasure]
  simp only [Bool.toNat_true, Bool.toNat_false, Nat.cast_one, Nat.cast_zero, zero_sub,
    Complex.real_smul, ← Complex.ofReal_mul, add_comm]

end DurfeeCCS.Step12
