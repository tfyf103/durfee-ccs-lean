module

public import DurfeeCCS.Core
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Nat.Sqrt

/-! # Support, degree, and boundary coefficients of Durfee polynomials -/

@[expose] public section

namespace DurfeeCCS

/-- The Young diagram consisting of a single column with `m` cells. -/
private def column (m : ℕ) : YoungDiagram where
  cells := (Finset.range m).product {0}
  isLowerSet := by
    intro b a hab hb
    change b ∈ (Finset.range m).product {0} at hb
    rcases Finset.mem_product.mp hb with ⟨hr, hc⟩
    have hbrow := Finset.mem_range.mp hr
    have hbcol := Finset.mem_singleton.mp hc
    have hab' : a.1 ≤ b.1 ∧ a.2 ≤ b.2 := hab
    change a ∈ (Finset.range m).product {0}
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt hab'.1 hbrow),
      Finset.mem_singleton.mpr (Nat.eq_zero_of_le_zero (hbcol ▸ hab'.2))⟩

@[simp] private theorem column_card (m : ℕ) : (column m).card = m := by
  simp [column, YoungDiagram.card]

private theorem widthBounded_column (m : ℕ) {d : ℕ} (hd : 0 < d) :
    WidthBounded d (column m) := by
  intro x hx
  change x ∈ (Finset.range m).product {0} at hx
  have hx' : x.2 = 0 := Finset.mem_singleton.mp (Finset.mem_product.mp hx).2
  simpa [hx'] using hd

private theorem widthBounded_bot (d : ℕ) : WidthBounded d (⊥ : YoungDiagram) := by
  intro x hx
  exact (YoungDiagram.notMem_bot x hx).elim

private theorem eq_bot_of_card_zero {Y : YoungDiagram} (hY : Y.card = 0) : Y = ⊥ := by
  apply YoungDiagram.ext
  exact Finset.card_eq_zero.mp hY

private theorem eq_column_of_width_one {Y : YoungDiagram} (hY : WidthBounded 1 Y) :
    Y = column Y.card := by
  have hcol : Y.col 0 = Y.cells := by
    ext x
    rw [YoungDiagram.mem_col_iff, YoungDiagram.mem_cells]
    exact ⟨And.left, fun hx => ⟨hx, Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (hY x hx))⟩⟩
  have hlen : Y.colLen 0 = Y.card := (YoungDiagram.colLen_eq_card Y).trans (congrArg Finset.card hcol)
  apply YoungDiagram.ext
  change Y.cells = (Finset.range Y.card).product {0}
  calc
    Y.cells = Y.col 0 := hcol.symm
    _ = (Finset.range (Y.colLen 0)).product {0} := YoungDiagram.col_eq_prod
    _ = (Finset.range Y.card).product {0} := by rw [hlen]

private abbrev Arms (n d : ℕ) := {ab : YoungDiagram × YoungDiagram //
  WidthBounded d ab.1 ∧ WidthBounded d ab.2 ∧ d * d + ab.1.card + ab.2.card = n}

/-- Every admissible positive Durfee side occurs. Place the extra cells in one arm. -/
theorem p_pos_of_square_le {n d : ℕ} (hd : 0 < d) (hn : d * d ≤ n) : 0 < p n d := by
  let arms : Arms n d := ⟨(column (n - d * d), ⊥), widthBounded_column _ hd,
    widthBounded_bot d, by simp [YoungDiagram.card]; omega⟩
  change 0 < Nat.card (DiagramFiber n d)
  exact Nat.card_pos_iff.mpr ⟨⟨(durfeeDecomposition n d).symm arms⟩, inferInstance⟩

/-- At size `d*d`, the two arms are both empty, so the square is the unique diagram. -/
theorem p_square (d : ℕ) : p (d * d) d = 1 := by
  change Nat.card (DiagramFiber (d * d) d) = 1
  rw [Nat.card_congr (durfeeDecomposition (d * d) d)]
  apply Nat.card_eq_one_iff_exists.mpr
  let emptyArms : Arms (d * d) d :=
    ⟨(⊥, ⊥), widthBounded_bot d, widthBounded_bot d, by simp [YoungDiagram.card]⟩
  refine ⟨emptyArms, fun arms => Subtype.ext (Prod.ext ?_ ?_)⟩
  · apply eq_bot_of_card_zero
    have h := arms.property.2.2
    omega
  · apply eq_bot_of_card_zero
    have h := arms.property.2.2
    omega

@[simp] theorem p_zero_zero : p 0 0 = 1 := by
  simpa using p_square 0

/-- A positive-size Young diagram has a positive Durfee side. -/
theorem p_zero_of_pos {n : ℕ} (hn : 0 < n) : p n 0 = 0 := by
  change Nat.card (DiagramFiber n 0) = 0
  apply Nat.card_eq_zero.mpr (Or.inl ⟨fun Y => ?_⟩)
  have hy := (durfeeSide_eq_zero_iff Y.val).mp Y.property.2
  have hcard := Y.property.1
  rw [hy] at hcard
  have hnzero : n = 0 := by simpa [YoungDiagram.card] using hcard.symm
  exact hn.ne' hnzero

/-- A hook of size `n` is uniquely determined by the number of cells in one arm. -/
private def hookArmsEquiv (n : ℕ) : Arms n 1 ≃ Fin n where
  toFun ab := ⟨ab.val.1.card, by have h := ab.property.2.2; omega⟩
  invFun k := ⟨(column k.val, column (n - (k.val + 1))), widthBounded_column _ Nat.one_pos,
    widthBounded_column _ Nat.one_pos, by simp; have hk := k.isLt; omega⟩
  left_inv ab := by
    apply Subtype.ext
    apply Prod.ext
    · exact (eq_column_of_width_one ab.property.1).symm
    · change column (n - (ab.val.1.card + 1)) = ab.val.2
      have h := ab.property.2.2
      rw [show n - (ab.val.1.card + 1) = ab.val.2.card by omega]
      exact (eq_column_of_width_one ab.property.2.1).symm
  right_inv k := Fin.ext (column_card k.val)

@[simp] theorem p_one (n : ℕ) : p n 1 = n :=
  Nat.card_eq_of_equiv_fin ((durfeeDecomposition n 1).trans (hookArmsEquiv n))

@[simp] theorem durfeePolynomial_zero : durfeePolynomial 0 = 1 := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro d
  rw [coeff_durfeePolynomial, Polynomial.coeff_one]
  by_cases hd : d = 0
  · simp [hd]
  · have hd' := Nat.pos_of_ne_zero hd
    simp [hd, p_eq_zero_of_sq_gt (Nat.mul_pos hd' hd')]

/-- The degree is the largest admissible Durfee side. -/
theorem natDegree_durfeePolynomial (n : ℕ) : (durfeePolynomial n).natDegree = n.sqrt := by
  by_cases hn : n = 0
  · simp [hn]
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    rw [coeff_durfeePolynomial, p_eq_zero_of_sq_gt ((Nat.sqrt_lt).mp hd), Nat.cast_zero]
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [coeff_durfeePolynomial]
    exact Int.ofNat_ne_zero.mpr
      (p_pos_of_square_le (Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hn)) (Nat.sqrt_le n)).ne'

theorem durfeePolynomial_ne_zero (n : ℕ) : durfeePolynomial n ≠ 0 := by
  by_cases hn : n = 0
  · simp [hn]
  intro h
  have hc := congrArg (fun f : Polynomial ℤ => f.coeff 1) h
  simp [hn] at hc

theorem degree_durfeePolynomial (n : ℕ) : (durfeePolynomial n).degree = (n.sqrt : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (durfeePolynomial_ne_zero n), natDegree_durfeePolynomial]

/-- The vanishing constant coefficient and the nonzero linear coefficient make zero a simple root. -/
theorem rootMultiplicity_zero_durfeePolynomial {n : ℕ} (hn : 0 < n) :
    (durfeePolynomial n).rootMultiplicity 0 = 1 := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    simp [hn.ne']
  · apply Polynomial.le_natTrailingDegree (durfeePolynomial_ne_zero n)
    intro j hj
    have hjzero : j = 0 := by omega
    simp [hjzero, p_zero_of_pos hn]

theorem degree_and_zeroMultiplicity {n : ℕ} (hn : 0 < n) :
    (∀ d, 1 ≤ d → d ≤ n.sqrt → 0 < p n d) ∧ p n 1 = n ∧
    (durfeePolynomial n).degree = (n.sqrt : WithBot ℕ) ∧
    (durfeePolynomial n).rootMultiplicity 0 = 1 :=
  ⟨fun _ hd hs => p_pos_of_square_le hd (Nat.le_sqrt.mp hs), p_one n,
    degree_durfeePolynomial n, rootMultiplicity_zero_durfeePolynomial hn⟩

/-- For a square size, the coefficient of the highest power is one. -/
theorem monic_durfeePolynomial_square (d : ℕ) : (durfeePolynomial (d * d)).Monic := by
  rw [Polynomial.Monic.def, ← Polynomial.coeff_natDegree, natDegree_durfeePolynomial,
    Nat.sqrt_eq, coeff_durfeePolynomial, p_square]
  rfl

end DurfeeCCS
