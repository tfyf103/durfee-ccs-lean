module

public import DurfeeCCS.Square
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.SetTheory.Cardinal.Finite

/-! The counting function and integral Durfee polynomial of the manuscript. -/

@[expose] public section

namespace DurfeeCCS

open scoped BigOperators

instance finiteDiagramFiber (n d : ℕ) : Finite (DiagramFiber n d) :=
  Finite.of_injective
    (fun Y => YoungDiagram.equivPartition (n := n) ⟨Y.1, Y.2.1⟩)
    (fun _ _ h => Subtype.ext (congrArg (fun Y : {Y : YoungDiagram // Y.card = n} => Y.val)
      (YoungDiagram.equivPartition.injective h)))

/-- The number of partitions of `n` whose Durfee square has side `d`. -/
noncomputable def p (n d : ℕ) : ℕ := Nat.card (DiagramFiber n d)

theorem p_eq_zero_of_sq_gt {n d : ℕ} (h : n < d * d) : p n d = 0 := by
  have hEmpty : IsEmpty (DiagramFiber n d) := ⟨fun Y => by
    have hs := durfeeSquare_le_card Y.1
    rw [Y.2.1, Y.2.2] at hs
    exact (Nat.not_le_of_lt h) hs⟩
  exact Nat.card_eq_zero.2 (Or.inl hEmpty)

/-- The polynomial over the integers, including the empty partition at `n = 0`. -/
noncomputable def durfeePolynomial (n : ℕ) : Polynomial ℤ :=
  ∑ d ∈ Finset.range (n.sqrt + 1), Polynomial.monomial d (p n d : ℤ)

@[simp] theorem coeff_durfeePolynomial (n d : ℕ) :
    (durfeePolynomial n).coeff d = (p n d : ℤ) := by
  classical
  simp only [durfeePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · have hlt : n.sqrt < d := by simpa [Finset.mem_range] using hd
    rw [p_eq_zero_of_sq_gt (Nat.sqrt_lt.mp hlt)]
    rfl

end DurfeeCCS
