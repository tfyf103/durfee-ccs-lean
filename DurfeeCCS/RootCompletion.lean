module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Complex.Basic

/-! Count the distinct roots and transport the complete list from ℝ to ℂ. -/

public section
namespace DurfeeCCS

open Polynomial

/-- The specified roots exhaust the real and complex roots, each with multiplicity one. -/
structure RootCompletion (P : Polynomial ℝ) {k : ℕ} (r : Fin k ↪ ℝ) : Prop where
  real_root_iff : ∀ x : ℝ, P.IsRoot x ↔ x = 0 ∨ ∃ i, x = r i
  real_simple : ∀ x : ℝ, P.IsRoot x → rootMultiplicity x P = 1
  real_card : P.roots.card = k + 1
  complex_root_iff : ∀ z : ℂ, (P.map Complex.ofRealHom).IsRoot z ↔
    z = 0 ∨ ∃ i, z = (r i : ℂ)
  complex_simple : ∀ z : ℂ, (P.map Complex.ofRealHom).IsRoot z →
    rootMultiplicity z (P.map Complex.ofRealHom) = 1
  complex_card : (P.map Complex.ofRealHom).roots.card = k + 1

private theorem completeRoots {R : Type*} [CommRing R] [IsDomain R]
    {P : Polynomial R} {k : ℕ} (hdeg : P.natDegree = k + 1)
    (hzero : P.IsRoot 0) (r : Fin k ↪ R) (hne : ∀ i, r i ≠ 0)
    (hr : ∀ i, P.IsRoot (r i)) :
    (∀ x : R, P.IsRoot x ↔ x = 0 ∨ ∃ i, x = r i) ∧
    (∀ x : R, P.IsRoot x → rootMultiplicity x P = 1) ∧ P.roots.card = k + 1 := by
  classical
  let S : Finset R := insert 0 (Finset.univ.map r)
  have hcard : S.card = k + 1 := by
    have hn : (0 : R) ∉ Finset.univ.map r := by
      simp [hne]
    simp [S, Finset.card_insert_of_notMem hn]
  have hmem (x : R) : x ∈ S ↔ x = 0 ∨ ∃ i, x = r i := by
    simp only [S, Finset.mem_insert, Finset.mem_map, Finset.mem_univ, true_and]
    exact or_congr_right (exists_congr (fun _ => eq_comm))
  have hS : ∀ x ∈ S, P.eval x = 0 := by
    intro x hx
    rcases (hmem x).mp hx with rfl | ⟨i, rfl⟩
    · exact hzero
    · exact hr i
  have hP : P ≠ 0 := by
    intro heq
    simp [heq] at hdeg
  have hroots : P.roots = S.val :=
    roots_eq_of_natDegree_le_card_of_ne_zero hS (hdeg.trans hcard.symm).le hP
  refine ⟨fun x => ?_, fun x hx => ?_, ?_⟩
  · rw [← mem_roots hP, hroots]
    exact hmem x
  · have hxS : x ∈ S.val := hroots ▸ (mem_roots hP).mpr hx
    rw [← count_roots, hroots]
    exact Multiset.count_eq_one_of_mem S.nodup hxS
  · rw [hroots]
    exact hcard

/-- Once all degree slots are represented by distinct real roots, mapping the polynomial to ℂ
preserves that complete list. -/
theorem completeRoots_of_degree {P : Polynomial ℝ} {k : ℕ}
    (hdeg : P.natDegree = k + 1) (hzero : P.IsRoot 0) (r : Fin k ↪ ℝ)
    (hr : ∀ i, r i < 0 ∧ P.IsRoot (r i)) : RootCompletion P r := by
  obtain ⟨hreal, hrealsimple, hrealcard⟩ :=
    completeRoots hdeg hzero r (fun i => (hr i).1.ne) (fun i => (hr i).2)
  let rc : Fin k ↪ ℂ := ⟨fun i => (r i : ℂ), Complex.ofReal_injective.comp r.injective⟩
  have hdegC : (P.map Complex.ofRealHom).natDegree = k + 1 :=
    (natDegree_map_eq_of_injective Complex.ofReal_injective P).trans hdeg
  have hzC : (P.map Complex.ofRealHom).IsRoot 0 := by
    simpa using hzero.map Complex.ofRealHom
  have hneC (i : Fin k) : rc i ≠ 0 := by
    change (r i : ℂ) ≠ 0
    exact_mod_cast (hr i).1.ne
  have hrC (i : Fin k) : (P.map Complex.ofRealHom).IsRoot (rc i) :=
    (hr i).2.map Complex.ofRealHom
  obtain ⟨hcomplex, hcomplexsimple, hcomplexcard⟩ := completeRoots hdegC hzC rc hneC hrC
  exact ⟨hreal, hrealsimple, hrealcard, hcomplex, hcomplexsimple, hcomplexcard⟩

end DurfeeCCS
