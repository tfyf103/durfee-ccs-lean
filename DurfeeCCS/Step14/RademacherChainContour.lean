module

public import DurfeeCCS.Step14.RademacherFareyChain
public import DurfeeCCS.Step14.RademacherFordPath
import Mathlib.Data.List.GetD

/-! The coefficient integral along the complete Farey chain, with the two
denominator-one halves combined. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step14

open Complex MeasureTheory DurfeeCCS.Step06

/-- The complete Farey chain supplies the forward Ford arcs, their exact
coefficient integral and the endpoint bounds used to complete each inverse line. -/
theorem twoColourPartitionCount_eq_fareyChain_arc_sum (n : ℕ) {N : ℕ} (hN : 0 < N) :
    let L := fareyChain N
    let m := L.length - 1
    let v := fun j => L.getD j 0
    ∃ left right : ℕ → ℝ,
      (∀ j < m, 0 ≤ left j ∧ 0 ≤ right j ∧
        (N : ℝ) ≤ ((v j).den : ℝ) * (left j + 1) ∧
        (N : ℝ) ≤ ((v j).den : ℝ) * (right j + 1)) ∧
      (twoColourPartitionCount n : ℂ) = ∑ j ∈ Finset.range m,
        ∫ t in -(left j)..right j, fordPathIntegrand n (v j).num (v j).den t := by
  let L := fareyChain N
  let m := L.length - 1
  let v := fun j => L.getD j 0
  let a := fun j => (v j).num
  let q := fun j => ((v j).den : ℤ)
  have hL : 0 < L.length := fareyChain_pos hN
  have hV (j : ℕ) (hj : j < L.length) : v j = L[j] :=
    List.getD_eq_getElem L 0 hj
  have hfirst : v 0 = 0 := (hV 0 hL).trans (fareyChain_first hN)
  have hlast : v m = 1 := (hV m (by dsimp [m]; omega)).trans (fareyChain_last hN)
  have hm : 0 < m := by
    by_contra! hb
    have hzero : m = 0 := by omega
    have he : (0 : ℚ) = 1 := hfirst.symm.trans (hzero ▸ hlast)
    exact zero_ne_one he
  have hq (j : ℕ) : 0 < q j := by
    change (0 : ℤ) < ((v j).den : ℤ)
    exact_mod_cast (v j).den_pos
  have hqR (j : ℕ) : (0 : ℝ) < q j := by exact_mod_cast hq j
  have ha₀ : a 0 = 0 := by simp [a, hfirst]
  have hq₀ : q 0 = 1 := by simp [q, hfirst]
  have ha₁ : a m = 1 := by simp [a, hlast]
  have hq₁ : q m = 1 := by simp [q, hlast]
  have hadj (j : ℕ) (hj : j < m) :
      q j * a (j + 1) - a j * q (j + 1) = 1 ∧
        (N : ℝ) < (q j : ℝ) + (q (j + 1) : ℝ) := by
    have ht : j + 1 < L.length := by dsimp [m] at hj; omega
    obtain ⟨hd, hs⟩ := fareyChain_adjacent hN ht
    simp only [a, q, hV j (by omega), hV (j+1) ht]
    exact ⟨hd, by exact_mod_cast hs⟩
  let left : ℕ → ℝ := fun j =>
    if j = 0 then (q (m - 1) : ℝ) else (q (j - 1) : ℝ) / (q j : ℝ)
  let right : ℕ → ℝ := fun j => (q (j + 1) : ℝ) / (q j : ℝ)
  change ∃ left right : ℕ → ℝ,
      (∀ j < m, 0 ≤ left j ∧ 0 ≤ right j ∧
        (N : ℝ) ≤ ((v j).den : ℝ) * (left j + 1) ∧
        (N : ℝ) ≤ ((v j).den : ℝ) * (right j + 1)) ∧
      (twoColourPartitionCount n : ℂ) = ∑ j ∈ Finset.range m,
        ∫ t in -(left j)..right j, fordPathIntegrand n (a j) (q j) t
  refine ⟨left, right, ?_, ?_⟩
  · intro j hj
    have hQR : ((v j).den : ℝ) = (q j : ℝ) := by simp [q]
    rw [hQR]
    have hright : (q j : ℝ) * (right j + 1) = (q j : ℝ) + q (j + 1) := by
      dsimp [right]
      field_simp [(hqR j).ne']
      ring
    refine ⟨?_, div_nonneg (hqR _).le (hqR _).le, ?_, hright ▸ (hadj j hj).2.le⟩
    · unfold left
      split <;> positivity
    · by_cases hj0 : j = 0
      · subst j
        have htail := (hadj (m - 1) (by omega)).2
        rw [show m - 1 + 1 = m by omega, hq₁] at htail
        simpa [left, hq₀] using htail.le
      · have hprev := (hadj (j - 1) (by omega)).2
        rw [show j - 1 + 1 = j by omega] at hprev
        have hleft : (q j : ℝ) * (left j + 1) = (q (j - 1) : ℝ) + q j := by
          simp only [left, ite_eq_right hj0]
          field_simp [(hqR j).ne']
        rw [hleft]
        exact hprev.le
  · have hcurve := twoColourPartitionCount_eq_fordPath_merged_sum n m a q
      (fun j _ => hq j) ha₀ hq₀ ha₁ hq₁ (fun j hj => (hadj j hj).1)
    let F := fun j => ∫ t in -(left j)..right j, fordPathIntegrand n (a j) (q j) t
    change _ = ∑ j ∈ Finset.range m, F j
    have hsplit : ∑ j ∈ Finset.range m, F j =
        (∑ j ∈ Finset.range (m - 1), F (j + 1)) + F 0 := by
      simpa only [Nat.sub_add_cancel hm] using Finset.sum_range_succ' F (m - 1)
    rw [hsplit, add_comm]
    have hF₀ : F 0 = ∫ t in -(q (m - 1) : ℝ)..(q 1 : ℝ), fordPathIntegrand n 0 1 t := by
      simp [F, left, right, ha₀, hq₀]
    have hFS (j : ℕ) : F (j + 1) =
        ∫ t in (-(q j : ℝ) / (q (j + 1) : ℝ))..((q (j + 2) : ℝ) / (q (j + 1) : ℝ)),
          fordPathIntegrand n (a (j + 1)) (q (j + 1)) t := by
      simp [F, left, right, neg_div]
    simp_rw [hF₀, hFS]
    exact hcurve

end DurfeeCCS.Step14
