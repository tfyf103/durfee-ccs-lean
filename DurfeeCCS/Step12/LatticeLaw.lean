module

public import DurfeeCCS.Step12.FiniteLaw
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! The finite Fourier sum of the centered and scaled Durfee law. -/

public section

namespace DurfeeCCS

open MeasureTheory Complex
open scoped BigOperators

/-- The Durfee law viewed on the integer lattice, with zero mass at negative integers. -/
@[expose]
noncomputable def durfeeLatticeMass (n : ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k then durfeeMass n k.toNat else 0

/-- A finite set containing the support of the integer-valued Durfee side. -/
def durfeeLatticeSupport (n : ℕ) : Finset ℤ :=
  (Finset.range (n.sqrt + 1)).map ⟨Int.ofNat, Int.ofNat_injective⟩

theorem durfeeLatticeMass_outside {n : ℕ} {k : ℤ} (hk : k ∉ durfeeLatticeSupport n) :
    durfeeLatticeMass n k = 0 := by
  by_cases h : 0 ≤ k
  · rw [durfeeLatticeMass, ite_eq_left h]
    apply durfeeMass_zero_of_sqrt_lt
    by_contra! hle
    apply hk
    exact Finset.mem_map.mpr ⟨k.toNat, Finset.mem_range.mpr (by omega), Int.toNat_of_nonneg h⟩
  · simp [durfeeLatticeMass, h]

private theorem durfeeDistribution_eq_sum_dirac (n : ℕ) :
    durfeeDistribution n =
      ∑ d ∈ Finset.range (n.sqrt + 1), durfeeDistribution n {d} • Measure.dirac d := by
  apply Measure.ae_mem_finset_iff.mp
  rw [durfeeDistribution, ae_map_iff (p := fun d : ℕ => d ∈ Finset.range (n.sqrt + 1))
    Measurable.of_discrete.aemeasurable
    (Finset.measurableSet (Finset.range (n.sqrt + 1)))]
  refine Filter.Eventually.of_forall fun P => Finset.mem_range_succ_iff.mpr (Nat.le_sqrt.mpr ?_)
  simpa only [partitionSide, YoungDiagram.card_ofPartition] using
    durfeeSquare_le_card (YoungDiagram.ofPartition P)

/-- The characteristic function of the Durfee side after any centering and scaling,
written as a finite sum over the integer lattice. -/
theorem charFun_durfeeDistribution_centered (n : ℕ) (a σ t : ℝ) :
    charFun ((durfeeDistribution n).map (fun d : ℕ => ((d : ℝ) - a) / σ)) t =
      ∑ k ∈ durfeeLatticeSupport n, (durfeeLatticeMass n k : ℂ) *
        exp ((↑(((k : ℝ) - a) * (t / σ)) : ℂ) * I) := by
  rw [charFun_apply_real, integral_map (Measurable.of_discrete.aemeasurable) (by fun_prop),
    durfeeDistribution_eq_sum_dirac, integral_finsetSum_measure]
  · rw [durfeeLatticeSupport, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro d _
    rw [integral_smul_measure, integral_dirac]
    change _ = (durfeeLatticeMass n (d : ℤ) : ℂ) *
      exp ((↑((((d : ℤ) : ℝ) - a) * (t / σ)) : ℂ) * I)
    simp only [durfeeLatticeMass, Int.natCast_nonneg, ite_true, Int.toNat_natCast,
      Int.cast_natCast, real_smul]
    rw [← durfeeDistribution_singleton_toReal]
    unfold Measure.real
    congr 2
    push_cast
    ring
  · intro d _
    exact (integrable_dirac (by simp)).smul_measure (measure_ne_top _ _)

end DurfeeCCS
