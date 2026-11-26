module

public import Mathlib.Combinatorics.Young.YoungDiagram

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Find

/-! The Durfee square and the two restricted pieces of a Young diagram. -/

public section

namespace DurfeeCCS

private theorem exists_missing_diagonal (Y : YoungDiagram) : ∃ i, (i, i) ∉ Y := by
  let i := Y.cells.sup Prod.fst + 1
  refine ⟨i, ?_⟩
  intro hi
  have bound : i ≤ Y.cells.sup Prod.fst :=
    Finset.le_sup (f := Prod.fst) ((YoungDiagram.mem_cells _).2 hi)
  dsimp [i] at bound
  omega

/-- The side length of the largest square in the top left corner. Coordinates start at zero,
so the side length is the index of the first absent diagonal cell. -/
noncomputable def durfeeSide (Y : YoungDiagram) : ℕ := by
  classical
  exact Nat.find (exists_missing_diagonal Y)

@[simp] theorem mem_diagonal_iff (Y : YoungDiagram) (i : ℕ) :
    (i, i) ∈ Y ↔ i < durfeeSide Y := by
  classical
  change (i, i) ∈ Y ↔ i < Nat.find (exists_missing_diagonal Y)
  constructor
  · intro hi
    by_contra! h
    exact Nat.find_spec (exists_missing_diagonal Y) (Y.up_left_mem h h hi)
  · exact fun hi => not_not.mp (Nat.find_min (exists_missing_diagonal Y) hi)

theorem durfeeSide_eq_zero_iff (Y : YoungDiagram) : durfeeSide Y = 0 ↔ Y = ⊥ := by
  constructor
  · intro h
    apply SetLike.ext
    rintro ⟨i, j⟩
    simp only [YoungDiagram.notMem_bot, iff_false]
    intro hij
    have hz := (mem_diagonal_iff Y 0).1 (Y.up_left_mem (Nat.zero_le i) (Nat.zero_le j) hij)
    omega
  · intro h
    subst Y
    by_contra! hd
    have hm := (mem_diagonal_iff (⊥ : YoungDiagram) 0).2 (by omega)
    exact YoungDiagram.notMem_bot _ hm

/-- Young diagrams of size `n` with Durfee side `d`. -/
@[expose] def DiagramFiber (n d : ℕ) := {Y : YoungDiagram // Y.card = n ∧ durfeeSide Y = d}

/-- All row lengths of a width-bounded diagram are at most `d`. -/
@[expose] def WidthBounded (d : ℕ) (Y : YoungDiagram) : Prop := ∀ p ∈ Y, p.2 < d

/-- Young diagrams of size `n` with width at most `d`. -/
@[expose] def RestrictedDiagram (d n : ℕ) := {Y : YoungDiagram // Y.card = n ∧ WidthBounded d Y}

private def squareCells (d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range d).product (Finset.range d)

private theorem mem_squareCells {d i j : ℕ} :
    (i, j) ∈ squareCells d ↔ i < d ∧ j < d := by
  simp [squareCells]

private theorem square_mem {Y : YoungDiagram} {d i j : ℕ} (hd : durfeeSide Y = d)
    (hi : i < d) (hj : j < d) : (i, j) ∈ Y := by
  have h := (mem_diagonal_iff Y (max i j)).2 (by omega)
  exact Y.up_left_mem (le_max_left i j) (le_max_right i j) h

theorem durfeeSquare_le_card (Y : YoungDiagram) :
    durfeeSide Y * durfeeSide Y ≤ Y.card := by
  have hs : squareCells (durfeeSide Y) ⊆ Y.cells := by
    rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj⟩ := mem_squareCells.1 hij
    exact (YoungDiagram.mem_cells _).2 (square_mem rfl hi hj)
  simpa [squareCells] using Finset.card_le_card hs

private def shiftDown (d : ℕ) : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun p := (d + p.1, p.2)
  inj' := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    change (d + i, j) = (d + k, l) at h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (by omega) h₂

private def shiftRight (d : ℕ) : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun p := (p.2, d + p.1)
  inj' := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    change (j, d + i) = (l, d + k) at h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (by omega) h₁

/-- The piece below the square, moved up by its side length. -/
noncomputable def belowSquare (d : ℕ) (Y : YoungDiagram) : YoungDiagram where
  cells := Y.cells.preimage (shiftDown d) (shiftDown d).injective.injOn
  isLowerSet := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hxy h
    simp only [Finset.mem_coe, Finset.mem_preimage, YoungDiagram.mem_cells] at h ⊢
    exact Y.up_left_mem (Nat.add_le_add_left hxy.1 d) hxy.2 h

@[simp] theorem mem_belowSquare {d : ℕ} {Y : YoungDiagram} {i j : ℕ} :
    (i, j) ∈ belowSquare d Y ↔ (d + i, j) ∈ Y := by
  change (i, j) ∈ Y.cells.preimage (shiftDown d) (shiftDown d).injective.injOn ↔
    shiftDown d (i, j) ∈ Y.cells
  exact Finset.mem_preimage

/-- The piece to the right of the square, moved left and then transposed. -/
noncomputable def rightOfSquare (d : ℕ) (Y : YoungDiagram) : YoungDiagram where
  cells := Y.cells.preimage (shiftRight d) (shiftRight d).injective.injOn
  isLowerSet := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hxy h
    simp only [Finset.mem_coe, Finset.mem_preimage, YoungDiagram.mem_cells] at h ⊢
    exact Y.up_left_mem hxy.2 (Nat.add_le_add_left hxy.1 d) h

@[simp] theorem mem_rightOfSquare {d : ℕ} {Y : YoungDiagram} {i j : ℕ} :
    (i, j) ∈ rightOfSquare d Y ↔ (j, d + i) ∈ Y := by
  change (i, j) ∈ Y.cells.preimage (shiftRight d) (shiftRight d).injective.injOn ↔
    shiftRight d (i, j) ∈ Y.cells
  exact Finset.mem_preimage

private theorem no_below_right {Y : YoungDiagram} {d i j : ℕ} (hd : durfeeSide Y = d)
    (hi : d ≤ i) (hj : d ≤ j) : (i, j) ∉ Y := by
  intro h
  have := (mem_diagonal_iff Y d).1 (Y.up_left_mem hi hj h)
  omega

theorem width_belowSquare {d : ℕ} {Y : YoungDiagram} (hd : durfeeSide Y = d) :
    WidthBounded d (belowSquare d Y) := by
  rintro ⟨i, j⟩ h
  by_contra! hj
  exact no_below_right hd (by omega) hj (mem_belowSquare.1 h)

theorem width_rightOfSquare {d : ℕ} {Y : YoungDiagram} (hd : durfeeSide Y = d) :
    WidthBounded d (rightOfSquare d Y) := by
  rintro ⟨i, j⟩ h
  by_contra! hj
  exact no_below_right hd hj (by omega) (mem_rightOfSquare.1 h)

private def joinCells (d : ℕ) (A B : YoungDiagram) : Finset (ℕ × ℕ) :=
  squareCells d ∪ A.cells.map (shiftDown d) ∪ B.cells.map (shiftRight d)

private theorem mem_map_shiftDown {d i j : ℕ} {A : YoungDiagram} :
    (i, j) ∈ A.cells.map (shiftDown d) ↔ d ≤ i ∧ (i - d, j) ∈ A := by
  simp only [Finset.mem_map, YoungDiagram.mem_cells]
  constructor
  · rintro ⟨⟨x, y⟩, hxy, he⟩
    change (d + x, y) = (i, j) at he
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
    refine ⟨by omega, ?_⟩
    have hx : i - d = x := by omega
    simpa [hx, ← h₂] using hxy
  · rintro ⟨hi, h⟩
    exact ⟨(i - d, j), h, Prod.ext (by change d + (i - d) = i; omega) rfl⟩

private theorem mem_map_shiftRight {d i j : ℕ} {B : YoungDiagram} :
    (i, j) ∈ B.cells.map (shiftRight d) ↔ d ≤ j ∧ (j - d, i) ∈ B := by
  simp only [Finset.mem_map, YoungDiagram.mem_cells]
  constructor
  · rintro ⟨⟨x, y⟩, hxy, he⟩
    change (y, d + x) = (i, j) at he
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
    refine ⟨by omega, ?_⟩
    have hx : j - d = x := by omega
    simpa [hx, ← h₁] using hxy
  · rintro ⟨hj, h⟩
    exact ⟨(j - d, i), h, Prod.ext rfl (by change d + (j - d) = j; omega)⟩

private theorem mem_joinCells {d i j : ℕ} {A B : YoungDiagram} :
    (i, j) ∈ joinCells d A B ↔
      ((i < d ∧ j < d) ∨ (d ≤ i ∧ (i - d, j) ∈ A)) ∨
        (d ≤ j ∧ (j - d, i) ∈ B) := by
  simp only [joinCells, Finset.mem_union, mem_squareCells, mem_map_shiftDown, mem_map_shiftRight]

/-- Glue two width-bounded diagrams to a square. Transpose the second diagram before
placing it on the right. -/
def glueSquare (d : ℕ) (A B : YoungDiagram) (hA : WidthBounded d A) (hB : WidthBounded d B) :
    YoungDiagram where
  cells := joinCells d A B
  isLowerSet := by
    rintro ⟨k, l⟩ ⟨i, j⟩ hxy h
    simp only [Finset.mem_coe, mem_joinCells] at h ⊢
    have hik : i ≤ k := hxy.1
    have hjl : j ≤ l := hxy.2
    rcases h with (⟨hk, hl⟩ | ⟨hk, ha⟩) | ⟨hl, hb⟩
    · exact Or.inl (Or.inl ⟨by omega, by omega⟩)
    · have hl : l < d := hA _ ha
      by_cases hi : i < d
      · exact Or.inl (Or.inl ⟨hi, by omega⟩)
      · exact Or.inl (Or.inr ⟨by omega, A.up_left_mem (by omega) hjl ha⟩)
    · have hk : k < d := hB _ hb
      by_cases hj : j < d
      · exact Or.inl (Or.inl ⟨by omega, hj⟩)
      · exact Or.inr ⟨by omega, B.up_left_mem (by omega) hik hb⟩

private theorem mem_glueSquare {d i j : ℕ} {A B : YoungDiagram}
    {hA : WidthBounded d A} {hB : WidthBounded d B} :
    (i, j) ∈ glueSquare d A B hA hB ↔
      ((i < d ∧ j < d) ∨ (d ≤ i ∧ (i - d, j) ∈ A)) ∨
        (d ≤ j ∧ (j - d, i) ∈ B) :=
  mem_joinCells

theorem durfeeSide_glueSquare (d : ℕ) (A B : YoungDiagram)
    (hA : WidthBounded d A) (hB : WidthBounded d B) :
    durfeeSide (glueSquare d A B hA hB) = d := by
  have h (i : ℕ) : (i, i) ∈ glueSquare d A B hA hB ↔ i < d := by
    rw [mem_glueSquare]
    constructor
    · rintro ((⟨hi, _⟩ | ⟨_, ha⟩) | ⟨_, hb⟩)
      · exact hi
      · exact hA _ ha
      · exact hB _ hb
    · exact fun hi => Or.inl (Or.inl ⟨hi, hi⟩)
  have hs (i : ℕ) : i < durfeeSide (glueSquare d A B hA hB) ↔ i < d :=
    (mem_diagonal_iff _ _).symm.trans (h i)
  have h₁ := (hs d).1
  have h₂ := (hs (durfeeSide (glueSquare d A B hA hB))).2
  omega

theorem card_glueSquare (d : ℕ) (A B : YoungDiagram)
    (hA : WidthBounded d A) (hB : WidthBounded d B) :
    (glueSquare d A B hA hB).card = d * d + A.card + B.card := by
  have h₁ : Disjoint (squareCells d) (A.cells.map (shiftDown d)) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hs ha
    have hi := (mem_squareCells.1 hs).1
    have hd := (mem_map_shiftDown.1 ha).1
    omega
  have h₂ : Disjoint (squareCells d ∪ A.cells.map (shiftDown d))
      (B.cells.map (shiftRight d)) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h hb
    obtain ⟨hj, hb⟩ := mem_map_shiftRight.1 hb
    rcases Finset.mem_union.1 h with hs | ha
    · have hl := (mem_squareCells.1 hs).2
      omega
    · have hl : j < d := hA _ (mem_map_shiftDown.1 ha).2
      omega
  change (joinCells d A B).card = _
  rw [joinCells, Finset.card_union_of_disjoint h₂, Finset.card_union_of_disjoint h₁]
  simp [squareCells]

theorem glueSquare_split {d : ℕ} {Y : YoungDiagram} (hd : durfeeSide Y = d) :
    glueSquare d (belowSquare d Y) (rightOfSquare d Y)
      (width_belowSquare hd) (width_rightOfSquare hd) = Y := by
  apply SetLike.ext
  rintro ⟨i, j⟩
  rw [mem_glueSquare, mem_belowSquare, mem_rightOfSquare]
  constructor
  · rintro ((⟨hi, hj⟩ | ⟨hi, h⟩) | ⟨hj, h⟩)
    · exact square_mem hd hi hj
    · rwa [show d + (i - d) = i by omega] at h
    · rwa [show d + (j - d) = j by omega] at h
  · intro h
    by_cases hi : i < d
    · by_cases hj : j < d
      · exact Or.inl (Or.inl ⟨hi, hj⟩)
      · exact Or.inr ⟨by omega, by rwa [show d + (j - d) = j by omega]⟩
    · exact Or.inl (Or.inr ⟨by omega, by rwa [show d + (i - d) = i by omega]⟩)

theorem belowSquare_glueSquare (d : ℕ) (A B : YoungDiagram)
    (hA : WidthBounded d A) (hB : WidthBounded d B) :
    belowSquare d (glueSquare d A B hA hB) = A := by
  apply SetLike.ext
  rintro ⟨i, j⟩
  rw [mem_belowSquare, mem_glueSquare]
  constructor
  · rintro ((⟨hi, _⟩ | ⟨_, ha⟩) | ⟨_, hb⟩)
    · omega
    · simpa using ha
    · have h := hB _ hb
      omega
  · intro ha
    exact Or.inl (Or.inr ⟨by omega, by simpa using ha⟩)

theorem rightOfSquare_glueSquare (d : ℕ) (A B : YoungDiagram)
    (hA : WidthBounded d A) (hB : WidthBounded d B) :
    rightOfSquare d (glueSquare d A B hA hB) = B := by
  apply SetLike.ext
  rintro ⟨i, j⟩
  rw [mem_rightOfSquare, mem_glueSquare]
  constructor
  · rintro ((⟨_, hi⟩ | ⟨_, ha⟩) | ⟨_, hb⟩)
    · omega
    · have h := hA _ ha
      omega
    · simpa using hb
  · intro hb
    exact Or.inr ⟨by omega, by simpa using hb⟩

/-- Cutting off a Durfee square leaves an ordered pair of diagrams, each of width at most
`d`, with total size `n - d*d`. The additive equality also enforces `d*d ≤ n`. -/
noncomputable def durfeeDecomposition (n d : ℕ) :
    DiagramFiber n d ≃ {ab : YoungDiagram × YoungDiagram //
      WidthBounded d ab.1 ∧ WidthBounded d ab.2 ∧ d*d + ab.1.card + ab.2.card = n} where
  toFun Y := by
    refine ⟨(belowSquare d Y.1, rightOfSquare d Y.1), width_belowSquare Y.2.2,
      width_rightOfSquare Y.2.2, ?_⟩
    have h := card_glueSquare d _ _ (width_belowSquare Y.2.2) (width_rightOfSquare Y.2.2)
    rwa [glueSquare_split Y.2.2, Y.2.1, eq_comm] at h
  invFun ab :=
    ⟨glueSquare d ab.1.1 ab.1.2 ab.2.1 ab.2.2.1,
      (card_glueSquare d _ _ _ _).trans ab.2.2.2, durfeeSide_glueSquare d _ _ _ _⟩
  left_inv Y := Subtype.ext (glueSquare_split Y.2.2)
  right_inv ab := Subtype.ext (Prod.ext
    (belowSquare_glueSquare d _ _ ab.2.1 ab.2.2.1)
    (rightOfSquare_glueSquare d _ _ ab.2.1 ab.2.2.1))

end DurfeeCCS
