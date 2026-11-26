module

public import DurfeeCCS.Step14.RademacherAssembly
public import DurfeeCCS.Step14.RademacherChainContour
public import DurfeeCCS.Step14.RademacherIndexing

/-! Equation (14) for the ordinary two-colour partition counts. -/

public noncomputable section

namespace DurfeeCCS.Step14

open MeasureTheory DurfeeCCS.Step06

/-- Reindex the coefficient integral of the complete forward Ford path
by positive denominators and their reduced residues. -/
theorem twoColourPartitionCount_eq_ford_residue_sum (n : ℕ) {N : ℕ} (hN : 0 < N) :
    ∃ left right : ℕ → ℕ → ℝ,
      (∀ k ∈ Finset.Icc 1 N, ∀ h ∈ (Finset.range k).filter (fun h => h.Coprime k),
        0 ≤ left h k ∧ 0 ≤ right h k ∧
        (N : ℝ) ≤ (k : ℝ) * (left h k + 1) ∧
        (N : ℝ) ≤ (k : ℝ) * (right h k + 1)) ∧
      (twoColourPartitionCount n : ℂ) =
        ∑ k ∈ Finset.Icc 1 N, ∑ h ∈ (Finset.range k).filter (fun h => h.Coprime k),
          ∫ v in -(left h k)..right h k, fordCoefficientIntegrand n h k v := by
  obtain ⟨left, right, hends, hsum⟩ := twoColourPartitionCount_eq_fareyChain_arc_sum n hN
  let L := fareyChain N
  let m := L.length - 1
  let vertex := fun j => L.getD j 0
  let i := fun h k : ℕ => L.idxOf ((h : ℚ) / (k : ℚ))
  have hpair (h k : ℕ) (hk : k ∈ Finset.Icc 1 N)
      (hh : h ∈ (Finset.range k).filter (fun a => a.Coprime k)) :
      i h k < m ∧ (vertex (i h k)).num = (h : ℤ) ∧ (vertex (i h k)).den = k :=
    fareyChain_initial_residue_index hN hk hh
  refine ⟨fun h k => left (i h k), fun h k => right (i h k), ?_, ?_⟩
  · intro k hk h hh
    obtain ⟨hi, _, hd⟩ := hpair h k hk hh
    have hends_i := hends (i h k) hi
    change 0 ≤ left (i h k) ∧ 0 ≤ right (i h k) ∧
      (N : ℝ) ≤ ((vertex (i h k)).den : ℝ) * (left (i h k) + 1) ∧
      (N : ℝ) ≤ ((vertex (i h k)).den : ℝ) * (right (i h k) + 1) at hends_i
    simpa only [hd] using hends_i
  · rw [hsum, sum_fareyChain_initial_by_den hN]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro h hh
    obtain ⟨_, ha, hd⟩ := hpair h k hk hh
    change (∫ t in -(left (i h k))..right (i h k),
      fordPathIntegrand n (vertex (i h k)).num (vertex (i h k)).den t) =
      ∫ t in -(left (i h k))..right (i h k), fordCoefficientIntegrand n h k t
    rw [ha, hd]
    simp [fordPathIntegrand, fordPath, fordVelocity, fordCoefficientIntegrand, div_eq_mul_inv]

/-- Exact Rademacher expansion of the two-colour partition numbers. -/
theorem twoColour_partition_rademacher : TwoColourRademacherIdentity :=
  twoColourRademacherIdentity_of_ford_integrals
    (fun n _ _ hN => twoColourPartitionCount_eq_ford_residue_sum n hN)

/-- Equation (14) for each positive coefficient. -/
theorem twoColourPartitionCount_eq_rademacherRHS {n : ℕ} (hn : 0 < n) :
    (twoColourPartitionCount n : ℂ) = twoColourRademacherRHS n :=
  twoColour_partition_rademacher n hn

end DurfeeCCS.Step14
