module

public import DurfeeCCS.Core
public import DurfeeCCS.GeneratingFunction

/-! Equation (1), interpreted coefficientwise in the ring of formal power series. -/

open scoped BigOperators
open PowerSeries

@[expose] public section

namespace DurfeeCCS

theorem widthBounded_iff_parts_le (d : ℕ) (Y : YoungDiagram) (hY : Y.card = n) :
    WidthBounded d Y ↔ ∀ i ∈ (Y.toPartition hY).parts, i ≤ d := by
  change (∀ c ∈ Y, c.2 < d) ↔ ∀ i ∈ Y.rowLens, i ≤ d
  constructor
  · intro h i hi
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hi
    rw [YoungDiagram.get_rowLens]
    by_contra! hbad
    exact (Nat.lt_irrefl d) (h (r, d) (YoungDiagram.mem_iff_lt_rowLen.mpr hbad))
  · rintro h ⟨i, j⟩ hij
    have hi0 := Y.up_left_mem (Nat.le_refl i) (Nat.zero_le j) hij
    have hi : i < Y.rowLens.length := by
      rw [YoungDiagram.length_rowLens]
      exact YoungDiagram.mem_iff_lt_colLen.mp hi0
    have hrow : Y.rowLen i ≤ d := by
      rw [← YoungDiagram.get_rowLens (h := hi)]
      exact h _ (List.getElem_mem hi)
    exact (YoungDiagram.mem_iff_lt_rowLen.mp hij).trans_le hrow

/-- A diagram is width-bounded exactly when all parts of its partition are at most `d`. -/
noncomputable def restrictedDiagramEquiv (d n : ℕ) :
    RestrictedDiagram d n ≃ {P // P ∈ Nat.Partition.restricted n (· ≤ d)} where
  toFun Y := ⟨Y.1.toPartition Y.2.1,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (widthBounded_iff_parts_le d Y.1 Y.2.1).mp Y.2.2⟩⟩
  invFun P := ⟨YoungDiagram.ofPartition P.1, YoungDiagram.card_ofPartition P.1, by
    apply (widthBounded_iff_parts_le d _ (YoungDiagram.card_ofPartition P.1)).mpr
    simpa using (Finset.mem_filter.mp P.2).2⟩
  left_inv Y := Subtype.ext (YoungDiagram.ofPartition_toPartition Y.2.1)
  right_inv P := Subtype.ext YoungDiagram.toPartition_ofPartition

instance finiteRestrictedDiagram (d n : ℕ) : Finite (RestrictedDiagram d n) :=
  Finite.of_injective _ (restrictedDiagramEquiv d n).injective

private theorem card_restrictedDiagram (d n : ℕ) :
    Nat.card (RestrictedDiagram d n) = (Nat.Partition.restricted n (· ≤ d)).card := by
  rw [Nat.card_congr (restrictedDiagramEquiv d n), Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The two width-bounded pieces can both be conjugated into partitions with at most `d` parts.
This gives the height-bounded convention used in the paper. -/
noncomputable def widthBoundedToAtMostParts (d n : ℕ) :
    RestrictedDiagram d n ≃ {P : Nat.Partition n // P.parts.card ≤ d} where
  toFun Y := ⟨Y.1.transpose.toPartition (by simpa using Y.2.1), by
    change Y.1.transpose.rowLens.length ≤ d
    rw [YoungDiagram.length_rowLens, YoungDiagram.colLen_transpose]
    apply Nat.le_of_not_gt
    intro h
    exact (Nat.lt_irrefl d) (Y.2.2 (0, d) (YoungDiagram.mem_iff_lt_rowLen.mpr h))⟩
  invFun P := ⟨(YoungDiagram.ofPartition P.1).transpose, by simp, by
    rintro ⟨i, j⟩ h
    have hj : j < (YoungDiagram.ofPartition P.1).colLen 0 := by
      apply YoungDiagram.mem_iff_lt_colLen.mp
      exact (YoungDiagram.ofPartition P.1).up_left_mem (Nat.le_refl _) (Nat.zero_le _)
        (YoungDiagram.mem_transpose.mp h)
    have hlen : (YoungDiagram.ofPartition P.1).colLen 0 = P.1.parts.card := by
      rw [← YoungDiagram.length_rowLens, YoungDiagram.rowLens_ofPartition_eq_sort_parts]
      simp
    rw [hlen] at hj
    exact hj.trans_le P.2⟩
  left_inv Y := Subtype.ext (by simp)
  right_inv P := Subtype.ext (by simp)

/-- When the square fits, the tail sizes split the remaining weight without truncation. -/
noncomputable def durfeeDecompositionBySize {n d : ℕ} (h : d * d ≤ n) :
    DiagramFiber n d ≃
      Σ ab : ↥(Finset.antidiagonal (n - d * d)),
        RestrictedDiagram d ab.1.1 × RestrictedDiagram d ab.1.2 :=
  (durfeeDecomposition n d).trans {
    toFun ab := ⟨⟨(ab.1.1.card, ab.1.2.card), Finset.mem_antidiagonal.mpr (by omega)⟩,
      ⟨ab.1.1, rfl, ab.2.1⟩, ⟨ab.1.2, rfl, ab.2.2.1⟩⟩
    invFun ab := ⟨(ab.2.1.1, ab.2.2.1), ab.2.1.2.2, ab.2.2.2.2, by
      have hsum := Finset.mem_antidiagonal.mp ab.1.2
      rw [ab.2.1.2.1, ab.2.2.2.1]
      omega⟩
    left_inv ab := by cases ab; rfl
    right_inv := by
      rintro ⟨⟨⟨a, b⟩, hab⟩, ⟨A, ha, hwA⟩, ⟨B, hb, hwB⟩⟩
      change A.card = a at ha
      change B.card = b at hb
      subst a
      subst b
      rfl }

/-- The partition bijection with the paper's bound on the number of parts. -/
noncomputable def durfeeDecompositionAtMostParts {n d : ℕ} (h : d * d ≤ n) :
    DiagramFiber n d ≃
      Σ ab : ↥(Finset.antidiagonal (n - d * d)),
        {A : Nat.Partition ab.1.1 // A.parts.card ≤ d} ×
        {B : Nat.Partition ab.1.2 // B.parts.card ≤ d} :=
  (durfeeDecompositionBySize h).trans <| Equiv.sigmaCongrRight fun ab =>
    Equiv.prodCongr (widthBoundedToAtMostParts d ab.1.1) (widthBoundedToAtMostParts d ab.1.2)

/-- The coefficient equality in Equation (1), for a square that fits. -/
theorem p_eq_coeff_restrictedPairSeries {n d : ℕ} (h : d * d ≤ n) :
    (p n d : ℤ) = coeff (n - d * d) (restrictedPairSeries d) := by
  classical
  rw [p, Nat.card_congr (durfeeDecompositionBySize h), Nat.card_sigma, coeff_restrictedPairSeries]
  simp only [Nat.cast_sum, Nat.card_prod, Nat.cast_mul, card_restrictedDiagram]
  exact Finset.sum_attach (Finset.antidiagonal (n - d * d)) (fun ab : ℕ × ℕ =>
    ((Nat.Partition.restricted ab.1 (· ≤ d)).card : ℤ) *
      ((Nat.Partition.restricted ab.2 (· ≤ d)).card : ℤ))

/-- The coefficient of `qⁿ` in the shifted series is zero when the square is too large. -/
theorem p_eq_coeff_shifted (n d : ℕ) :
    (p n d : ℤ) = coeff n (PowerSeries.X ^ (d * d) * restrictedPairSeries d) := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · exact p_eq_coeff_restrictedPairSeries h
  · rw [p_eq_zero_of_sq_gt (Nat.lt_of_not_ge h)]
    rfl

/-- The outer series in `q` with the Durfee polynomials as coefficients in the variable `x`. -/
noncomputable def durfeeGeneratingSeries : (Polynomial ℤ)⟦X⟧ :=
  PowerSeries.mk durfeePolynomial

/-- Formal version of the double series in (1), written as a locally finite sum in each
coefficient of `q`. The degree restriction drops only terms divisible by higher powers of `q`. -/
theorem durfeeGeneratingSeries_eq_squares :
    durfeeGeneratingSeries = PowerSeries.mk fun n =>
      ∑ d ∈ Finset.range (n.sqrt + 1), Polynomial.monomial d
        (coeff n (PowerSeries.X ^ (d * d) * restrictedPairSeries d)) := by
  ext n : 1
  simp only [durfeeGeneratingSeries, PowerSeries.coeff_mk, durfeePolynomial]
  exact Finset.sum_congr rfl fun d _ => congrArg (Polynomial.monomial d) (p_eq_coeff_shifted n d)

end DurfeeCCS
