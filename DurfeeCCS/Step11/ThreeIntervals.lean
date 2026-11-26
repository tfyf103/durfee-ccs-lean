module

public import DurfeeCCS.Quotient
public import DurfeeCCS.RootCompletion
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Logic.Equiv.Fin.Basic

/-! Combine the three disjoint open intervals in the proof of Theorem 1.2. -/

public section

namespace DurfeeCCS.Step11

open Polynomial

private theorem exists_separatedEmbedding {k l : ℕ} (t : ℝ) (property : ℝ → Prop)
    (left : Fin k ↪ ℝ) (right : Fin l ↪ ℝ)
    (hleft : ∀ i, left i < t ∧ property (left i))
    (hright : ∀ j, t < right j ∧ property (right j)) :
    ∃ both : Fin (k + l) ↪ ℝ, ∀ i, property (both i) := by
  have hdisjoint : Disjoint (Set.range left) (Set.range right) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, h₁⟩ ⟨j, h₂⟩
    exact ((hleft i).1.trans (hright j).1).ne (h₁.trans h₂.symm)
  let combined : Fin k ⊕ Fin l ↪ ℝ :=
    Equiv.sumEmbeddingEquivProdEmbeddingDisjoint.symm ⟨(left, right), hdisjoint⟩
  let indices : Fin (k + l) ≃ Fin k ⊕ Fin l := finSumFinEquiv.symm
  refine ⟨indices.toEmbedding.trans combined, fun i => ?_⟩
  change property (combined (indices i))
  cases indices i with
  | inl j => exact (hleft j).2
  | inr j => exact (hright j).2

/-- Seven near roots, the middle roots, and the far roots count exactly m−1
distinct negative roots when the two cuts are ordered. -/
theorem negativeRoots_of_threeIntervals (P : Polynomial ℝ) {m d₀ : ℕ}
    (hd : 8 ≤ d₀) (hdm : d₀ ≤ m) {a b : ℝ} (hab : a < b) (hb : b < 0)
    (outer : Fin (m - d₀) ↪ ℝ) (middle : Fin (d₀ - 8) ↪ ℝ) (near : Fin 7 ↪ ℝ)
    (houter : ∀ i, outer i < a ∧ P.IsRoot (outer i))
    (hmiddle : ∀ i, a < middle i ∧ middle i < b ∧ P.IsRoot (middle i))
    (hnear : ∀ i, b < near i ∧ near i < 0 ∧ P.IsRoot (near i)) :
    ∃ r : Fin (m - 1) ↪ ℝ, ∀ i, r i < 0 ∧ P.IsRoot (r i) := by
  obtain ⟨farAndMiddle, hFarAndMiddle⟩ :=
    exists_separatedEmbedding a (fun x => x < b ∧ P.IsRoot x) outer middle
      (fun i => ⟨(houter i).1, (houter i).1.trans hab, (houter i).2⟩) hmiddle
  obtain ⟨all, hall⟩ :=
    exists_separatedEmbedding b (fun x => x < 0 ∧ P.IsRoot x) farAndMiddle near
      (fun i => ⟨(hFarAndMiddle i).1, (hFarAndMiddle i).1.trans hb,
        (hFarAndMiddle i).2⟩) hnear
  let e := finCongr (show m - 1 = (m - d₀) + (d₀ - 8) + 7 by omega)
  exact ⟨e.toEmbedding.trans all, fun i => hall (e i)⟩

/-- The three intervals and the origin exhaust the Durfee degree, over both ℝ and ℂ. -/
theorem durfeeRootCompletion_of_threeIntervals {n d₀ : ℕ}
    (hn : 0 < n) (hd : 8 ≤ d₀) (hdm : d₀ ≤ n.sqrt)
    {a b : ℝ} (hab : a < b) (hb : b < 0)
    (outer : Fin (n.sqrt - d₀) ↪ ℝ) (middle : Fin (d₀ - 8) ↪ ℝ) (near : Fin 7 ↪ ℝ)
    (houter : ∀ i, outer i < a ∧ (durfeePolynomialReal n).IsRoot (outer i))
    (hmiddle : ∀ i, a < middle i ∧ middle i < b ∧ (durfeePolynomialReal n).IsRoot (middle i))
    (hnear : ∀ i, b < near i ∧ near i < 0 ∧ (durfeePolynomialReal n).IsRoot (near i)) :
    ∃ r : Fin (n.sqrt - 1) ↪ ℝ,
      (∀ i, r i < 0 ∧ (durfeePolynomialReal n).IsRoot (r i)) ∧
      RootCompletion (durfeePolynomialReal n) r := by
  obtain ⟨r, hr⟩ := negativeRoots_of_threeIntervals (durfeePolynomialReal n)
    hd hdm hab hb outer middle near houter hmiddle hnear
  refine ⟨r, hr, completeRoots_of_degree ?_ ?_ r hr⟩
  · rw [natDegree_durfeePolynomialReal]
    omega
  · simp [Polynomial.IsRoot, durfeePolynomialReal_eq_X_mul_quotient hn]

end DurfeeCCS.Step11
