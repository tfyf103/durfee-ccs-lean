module

public import DurfeeCCS.Core
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram

/-! Express the Durfee counting function and polynomial directly in terms of integer partitions. -/

public section

namespace DurfeeCCS

open scoped BigOperators

/-- The side length of the Durfee square of an integer partition. -/
@[expose] noncomputable def partitionSide {n : ℕ} (P : Nat.Partition n) : ℕ :=
  durfeeSide (YoungDiagram.ofPartition P)

/-- Passing to a partition preserves size and the side length of the Durfee square. -/
noncomputable def diagramFiberEquivPartitions (n d : ℕ) :
    DiagramFiber n d ≃ {P : Nat.Partition n // partitionSide P = d} where
  toFun Y :=
    ⟨Y.1.toPartition Y.2.1, by simpa [partitionSide] using Y.2.2⟩
  invFun P :=
    ⟨YoungDiagram.ofPartition P.1, YoungDiagram.card_ofPartition _, P.2⟩
  left_inv Y := Subtype.ext (YoungDiagram.ofPartition_toPartition Y.2.1)
  right_inv _ := Subtype.ext YoungDiagram.toPartition_ofPartition

theorem p_eq_card_partitions_side (n d : ℕ) :
    p n d = Nat.card {P : Nat.Partition n // partitionSide P = d} :=
  Nat.card_congr (diagramFiberEquivPartitions n d)

/-- The manuscript's definition of the polynomial, as one monomial per integer partition. -/
theorem durfeePolynomial_eq_sum_partitions (n : ℕ) :
    durfeePolynomial n = ∑ P : Nat.Partition n, (Polynomial.X : Polynomial ℤ) ^ partitionSide P := by
  classical
  ext d
  rw [coeff_durfeePolynomial, p_eq_card_partitions_side, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  have h (P : Nat.Partition n) :
      (if d = partitionSide P then (1 : ℤ) else 0) =
        if partitionSide P = d then 1 else 0 := by
    by_cases hs : partitionSide P = d
    · simp [hs]
    · have hs' : d ≠ partitionSide P := fun he => hs he.symm
      simp [hs, hs']
  simp_rw [h, ← Finset.sum_filter]
  simp

end DurfeeCCS
