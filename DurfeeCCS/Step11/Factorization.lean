module

public import DurfeeCCS.Quotient
public import DurfeeCCS.RootCompletion

/-! Factorization after the real root count has exhausted the degree. -/

public noncomputable section

namespace DurfeeCCS.Step11

open Polynomial

/-- Once zero and the listed simple real roots exhaust the degree, their linear factors
give the polynomial up to its leading coefficient. -/
theorem factorization_of_rootCompletion {P : Polynomial ℝ} {k : ℕ}
    (r : Fin k ↪ ℝ) (hroot : RootCompletion P r) (hdegree : P.natDegree = k + 1) :
    P = C P.leadingCoeff * X * ∏ i, (X - C (r i)) := by
  classical
  have hP : P ≠ 0 := by
    rintro rfl
    simp at hdegree
  let S : Finset ℝ := insert 0 (Finset.univ.map r)
  have hnodup : P.roots.Nodup := by
    apply Multiset.nodup_iff_count_eq_one.mpr
    intro x hx
    exact (count_roots P).trans (hroot.real_simple x ((mem_roots hP).mp hx))
  have hroots : P.roots = S.val := by
    apply (Multiset.Nodup.ext hnodup S.nodup).mpr
    intro x
    rw [mem_roots hP, hroot.real_root_iff x]
    change (_ : Prop) ↔ x ∈ S
    simp [S, eq_comm]
  have hnot : (0 : ℝ) ∉ Finset.univ.map r := by
    intro hmem
    have hcard : S.card = k := by
      change (insert 0 (Finset.univ.map r)).card = k
      rw [Finset.insert_eq_of_mem hmem]
      simp
    have hcount := congrArg Multiset.card hroots
    rw [hroot.real_card] at hcount
    change k + 1 = S.card at hcount
    omega
  have hroots' : P.roots = 0 ::ₘ (Finset.univ.map r).val := by
    rw [hroots]
    exact Finset.insert_val_of_notMem hnot
  have hfactor := C_leadingCoeff_mul_prod_multiset_X_sub_C (hroot.real_card.trans hdegree.symm)
  rw [hroots', Multiset.map_cons, Multiset.prod_cons, map_zero, sub_zero, ← mul_assoc] at hfactor
  change C P.leadingCoeff * X * ∏ x ∈ Finset.univ.map r, (X - C x) = P at hfactor
  rw [Finset.prod_map] at hfactor
  exact hfactor.symm

/-- The leading coefficient is the number of partitions with the largest admissible Durfee side. -/
theorem leadingCoeff_durfeePolynomialReal (n : ℕ) :
    (durfeePolynomialReal n).leadingCoeff = (p n n.sqrt : ℝ) := by
  rw [Polynomial.leadingCoeff, natDegree_durfeePolynomialReal, coeff_durfeePolynomialReal]

end DurfeeCCS.Step11
