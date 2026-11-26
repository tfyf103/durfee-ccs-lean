module

public import DurfeeCCS.Step14.RademacherFareyChain
import all DurfeeCCS.Step14.RademacherFareyChain
import Mathlib.Algebra.BigOperators.Fin

/-! Reindex the truncated Farey contour by its initial vertices. -/

public section

namespace DurfeeCCS.Step14

open Finset

private theorem sum_list_getElem_eq_sum_toFinset {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] {l : List α} (hl : l.Nodup) (f : α → M) :
    (∑ i : Fin l.length, f (l[i.val])) = ∑ r ∈ l.toFinset, f r := by
  let e : Fin l.length ↪ α :=
    ⟨fun i => l[i.val], fun i j he => Fin.ext (hl.getElem_inj_iff.mp he)⟩
  have hmap : (Finset.univ : Finset (Fin l.length)).map e = l.toFinset := by
    ext r
    rw [Finset.mem_map, List.mem_toFinset, List.mem_iff_getElem]
    constructor
    · rintro ⟨i, _, hr⟩
      exact ⟨i.val, i.isLt, hr⟩
    · rintro ⟨i, hi, hr⟩
      exact ⟨⟨i, hi⟩, Finset.mem_univ _, hr⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- The initial Farey vertices are the indexing set of the complete Ford arcs
with the final vertex 1/1 omitted. -/
theorem sum_fareyChain_initial_indices {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℚ → M) :
    (∑ j ∈ range ((fareyChain N).length - 1), f ((fareyChain N)[j]?.getD 0)) =
      ∑ r ∈ (fareyChain N).dropLast.toFinset, f r := by
  have hNodup := (fareyChain_nodup N).sublist (List.dropLast_sublist (fareyChain N))
  rw [← sum_list_getElem_eq_sum_toFinset hNodup]
  conv_lhs => rw [← List.length_dropLast, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  have hlen : (fareyChain N).dropLast.length ≤ (fareyChain N).length := by
    simp
  rw [List.getElem_dropLast, List.getElem?_eq_getElem (i.isLt.trans_le hlen)]
  rfl

/-- Reindex a family on initial Ford arcs by the canonical index of its cusp. -/
theorem sum_fareyChain_initial_idxOf {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    (∑ j ∈ range ((fareyChain N).length - 1), f j) =
      ∑ r ∈ (fareyChain N).dropLast.toFinset, f ((fareyChain N).idxOf r) := by
  rw [← sum_fareyChain_initial_indices N (fun r => f ((fareyChain N).idxOf r))]
  apply sum_congr rfl
  intro i hi
  have hi' : i < (fareyChain N).length := by
    have := mem_range.mp hi
    omega
  rw [List.getElem?_eq_getElem hi', Option.getD_some]
  congr 1
  symm
  exact (fareyChain_nodup N).idxOf_getElem i hi'

/-- The canonical index of an initial Farey cusp is strictly before the final one. -/
theorem fareyChain_idxOf_lt_initial_count {N : ℕ} {r : ℚ}
    (hr : r ∈ (fareyChain N).dropLast.toFinset) :
    (fareyChain N).idxOf r < (fareyChain N).length - 1 := by
  have hr' := List.mem_toFinset.mp hr
  have h := List.succ_idxOf_lt_length_of_mem_dropLast hr'
  omega

theorem fareyChain_getD_idxOf {N : ℕ} {r : ℚ} (hr : r ∈ (fareyChain N).dropLast.toFinset) :
    ((fareyChain N)[(fareyChain N).idxOf r]?.getD 0) = r := by
  rw [List.getElem?_idxOf (List.mem_of_mem_dropLast (List.mem_toFinset.mp hr))]
  rfl

/-- The index of a specified reduced fraction in the truncated Farey chain,
including recovery of its canonical numerator and denominator. -/
theorem fareyChain_initial_residue_index {N h k : ℕ} (hN : 0 < N)
    (hk : k ∈ Icc 1 N) (hh : h ∈ (range k).filter (fun a => a.Coprime k)) :
    let j := (fareyChain N).idxOf ((h : ℚ) / k)
    let v := (fareyChain N).getD j 0
    j < (fareyChain N).length - 1 ∧ v.num = (h : ℤ) ∧ v.den = k := by
  let r : ℚ := (h : ℚ) / k
  have hk' : 0 < k := (mem_Icc.mp hk).1
  have hkR : 0 < (k : ℚ) := by exact_mod_cast hk'
  have hh' := mem_filter.mp hh
  have hhR : (h : ℚ) < k := by exact_mod_cast mem_range.mp hh'.1
  obtain ⟨hnum, hden⟩ :=
    rat_num_den_of_reduced (a := (h : ℤ)) hk' (by simpa using hh'.2)
  rw [Int.cast_natCast] at hnum hden
  have hr : r ∈ (fareyChain N).dropLast.toFinset := by
    rw [List.mem_toFinset, mem_fareyChain_dropLast hN]
    exact ⟨div_nonneg (by positivity) hkR.le, (div_lt_one hkR).mpr hhR,
      hden.trans_le (mem_Icc.mp hk).2⟩
  dsimp only
  rw [List.getD_eq_getElem?_getD, fareyChain_getD_idxOf hr]
  exact ⟨fareyChain_idxOf_lt_initial_count hr, hnum, hden⟩

/-- The Ford arcs can be summed over denominators and reduced numerators;
the addend is allowed to use the adjacent vertices through its original index. -/
theorem sum_fareyChain_initial_by_den {M : Type*} [AddCommMonoid M]
    {N : ℕ} (hN : 0 < N) (g : ℕ → M) :
    (∑ j ∈ range ((fareyChain N).length - 1), g j) =
      ∑ k ∈ Icc 1 N, ∑ h ∈ (range k).filter (fun a => a.Coprime k),
        g ((fareyChain N).idxOf ((h : ℚ) / k)) := by
  rw [sum_fareyChain_initial_idxOf]
  calc
    _ = ∑ r ∈ (fareyChain N).dropLast.toFinset,
        g ((fareyChain N).idxOf ((r.num : ℚ) / r.den)) := by
      apply sum_congr rfl
      intro r _
      rw [Rat.num_div_den]
    _ = _ := by
      simpa only [Int.cast_natCast] using
        sum_fareyChain_dropLast hN (fun a k => g ((fareyChain N).idxOf ((a : ℚ) / k)))

end DurfeeCCS.Step14
