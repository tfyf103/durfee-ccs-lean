module

public import DurfeeCCS.Step05.All
public import DurfeeCCS.Step11.Large
public import DurfeeCCS.Step11.Factorization
public import DurfeeCCS.Step11.RootData
public import DurfeeCCS.Samples

/-! Theorem 1.2 and the Canfield–Corteel–Savage conjecture. -/

public section

namespace DurfeeCCS

open Polynomial

/-- Theorem 1.2 for all positive sizes. The degree count exhausts the roots over both ℝ and ℂ. -/
theorem durfee_simple_exact_negative_roots (n : ℕ) (hn : 1 ≤ n) : HasDurfeeRoots n := by
  by_cases hfinite : n ≤ 6400
  · exact Step05.finiteDurfeeRoots n hn hfinite
  · exact Step11.largeDurfeeRoots (by omega)

theorem durfee_negative_root_count (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {x : ℝ // x < 0 ∧ (durfeePolynomialReal n).IsRoot x} = n.sqrt - 1 :=
  Step11.card_negative_roots_of_completed (durfee_simple_exact_negative_roots n hn)

/-- The full simple-root list for the complex Durfee polynomial. -/
theorem durfee_complex_roots_exact (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : Fin (n.sqrt - 1) ↪ ℝ, (∀ i, r i < 0) ∧
      (durfeePolynomialComplex n).roots.card = n.sqrt ∧
      (∀ z : ℂ, (durfeePolynomialComplex n).IsRoot z ↔ z = 0 ∨ ∃ i, z = (r i : ℂ)) ∧
      (∀ z : ℂ, (durfeePolynomialComplex n).IsRoot z →
        (durfeePolynomialComplex n).rootMultiplicity z = 1) := by
  obtain ⟨r, hneg, hroot⟩ := durfee_simple_exact_negative_roots n hn
  rw [durfeePolynomialComplex_eq_map_real]
  refine ⟨r, hneg, ?_, hroot.complex_root_iff, hroot.complex_simple⟩
  rw [hroot.complex_card, Nat.sub_add_cancel (Nat.sqrt_pos.mpr hn)]

/-- Conjecture 1.1. Every complex zero of the ordinary Durfee polynomial is real. -/
theorem ordinaryDurfee_allRootsReal (n : ℕ) (hn : 1 ≤ n) {z : ℂ}
    (hz : (durfeePolynomialComplex n).IsRoot z) : ∃ x : ℝ, z = (x : ℂ) := by
  obtain ⟨r, _, _, hroots, _⟩ := durfee_complex_roots_exact n hn
  rcases (hroots z).1 hz with hzero | ⟨i, hi⟩
  · exact ⟨0, by simpa using hzero⟩
  · exact ⟨r i, hi⟩

/-- Factorization with positive and pairwise distinct radii indexed by the nonzero roots. -/
theorem durfee_factorization (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : Fin (n.sqrt - 1) ↪ ℝ, (∀ i, 0 < r i) ∧
      durfeePolynomialReal n =
        C (p n n.sqrt : ℝ) * X * ∏ i, (X + C (r i)) := by
  obtain ⟨roots, hneg, hroot⟩ := durfee_simple_exact_negative_roots n hn
  let r : Fin (n.sqrt - 1) ↪ ℝ := ⟨fun i => -roots i,
    fun _ _ h => roots.injective (neg_injective h)⟩
  have hdegree : (durfeePolynomialReal n).natDegree = n.sqrt - 1 + 1 := by
    rw [natDegree_durfeePolynomialReal, Nat.sub_add_cancel (Nat.sqrt_pos.mpr hn)]
  have hfactor := Step11.factorization_of_rootCompletion roots hroot hdegree
  rw [Step11.leadingCoeff_durfeePolynomialReal] at hfactor
  refine ⟨r, fun i => neg_pos.mpr (hneg i), ?_⟩
  change durfeePolynomialReal n = C (p n n.sqrt : ℝ) * X * ∏ i, (X + C (-roots i))
  simpa [sub_eq_add_neg] using hfactor

/-- At size one the product of the nonzero-root factors is the empty product. -/
theorem durfee_factorization_one :
    durfeePolynomialReal 1 =
      C (p 1 1 : ℝ) * X * ∏ i : Fin 0, (X + C (Fin.elim0 i : ℝ)) := by
  simp [durfeePolynomialReal, durfeePolynomial_one]

end DurfeeCCS
