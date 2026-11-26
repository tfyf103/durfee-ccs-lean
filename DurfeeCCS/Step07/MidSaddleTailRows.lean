module

public import DurfeeCCS.Step07.MidSaddleTail
public import DurfeeCCS.Step07.MidSaddleTableGridSound
public import DurfeeCCS.Step07.SaddleEndpointGrid
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Assembly of the finite midpoint certificates in Lemma 3.9. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open DurfeeCCS.Step06

private def minorArcRightGrid (i : Fin 18) : Fin 21 :=
  ![0, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 19, 20, 20] i

private def minorArcLeftGrid (i : Fin 18) : Fin 21 :=
  ![0, 0, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 19, 20] i

theorem minorArc_row_gap_endpoint (i : Fin 18) :
    (minorArcGapLower i : ℝ) < minorArcSaddleGap (minorArcData i).left := by
  by_cases hi : i = 0
  · subst i
    simpa [minorArcGapLower, minorArcSaddleGap, minorArcData] using saddle_at_one_sq_lower
  · have h₁ : (saddleEndpointData (minorArcLeftGrid i)).logRadius = (minorArcData i).left := by
      fin_cases i <;> first | contradiction | decide +kernel
    have h₂ : (saddleEndpointData (minorArcLeftGrid i)).gapLow = minorArcGapLower i := by
      fin_cases i <;> first | contradiction | rfl
    have h := (saddleEndpointData_bounds (minorArcLeftGrid i)).gap_lower
    rw [h₁, h₂] at h
    exact h

theorem minorArc_row_amplitude_endpoint (i : Fin 18) (hi : i.val < 17) :
    (saddleS (Real.exp (minorArcData i).right)).re ≤ ((minorArcData i).amplitude : ℝ) := by
  have h₁ : (saddleEndpointData (minorArcRightGrid i)).logRadius = (minorArcData i).right := by
    fin_cases i <;> decide +kernel
  have h₂ : (saddleEndpointData (minorArcRightGrid i)).reHigh = (minorArcData i).amplitude := by
    fin_cases i <;> first | rfl | norm_num at hi
  have h := (saddleEndpointData_bounds (minorArcRightGrid i)).re_upper
  rwa [h₁, h₂] at h

def minorArcCandidates (epsₗ epsᵤ yplus : ℝ) : Finset ℝ := by
  classical
  exact insert (minorArcQSmall epsᵤ)
    ((Finset.univ.filter fun k : Fin 1600 => 5 ≤ k.val).image
      fun k => minorArcQFinite epsₗ epsᵤ yplus k.val)

theorem minorArcCandidates_nonempty (epsₗ epsᵤ yplus : ℝ) :
    (minorArcCandidates epsₗ epsᵤ yplus).Nonempty := by
  classical
  exact ⟨minorArcQSmall epsᵤ, Finset.mem_insert_self _ _⟩

/-- The finite maximum in (64) with the prescribed row parameters. -/
def minorArcQstarRow (i : Fin 18) : ℝ :=
  let epsₗ := if i.val < 17 then Real.exp (-((minorArcData i).right : ℝ)) else 0
  let epsᵤ := Real.exp (-((minorArcData i).left : ℝ))
  let yplus := (minorArcYmax (minorArcData i) : ℝ)
  minorArcFixedReal epsₗ yplus +
    (minorArcCandidates epsₗ epsᵤ yplus).sup' (minorArcCandidates_nonempty epsₗ epsᵤ yplus) id

theorem minorArcQstarRow_lt (i : Fin 18) :
    minorArcQstarRow i < ((minorArcData i).target : ℝ) := by
  classical
  let epsₗ := if i.val < 17 then Real.exp (-((minorArcData i).right : ℝ)) else 0
  let epsᵤ := Real.exp (-((minorArcData i).left : ℝ))
  let yplus := (minorArcYmax (minorArcData i) : ℝ)
  have h := minorArc_qstar_upper i
  change (minorArcFixedReal epsₗ yplus + minorArcQSmall epsᵤ < ((minorArcData i).target : ℝ)) ∧
    ∀ k : Fin 1600, 5 ≤ k.val → minorArcFixedReal epsₗ yplus +
      minorArcQFinite epsₗ epsᵤ yplus k.val < ((minorArcData i).target : ℝ) at h
  unfold minorArcQstarRow
  have hs : (minorArcCandidates epsₗ epsᵤ yplus).sup'
      (minorArcCandidates_nonempty epsₗ epsᵤ yplus) id <
        ((minorArcData i).target : ℝ) - minorArcFixedReal epsₗ yplus := by
    rw [Finset.sup'_lt_iff]
    intro z hz
    unfold minorArcCandidates at hz
    change id z < _
    rw [id_eq]
    rcases Finset.mem_insert.mp hz with hsmall | hlarge
    · rw [hsmall]
      linarith only [h.1]
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hlarge
      linarith only [h.2 k (Finset.mem_filter.mp hk).2]
  change minorArcFixedReal epsₗ yplus + (minorArcCandidates epsₗ epsᵤ yplus).sup'
    (minorArcCandidates_nonempty epsₗ epsᵤ yplus) id < _
  linarith only [hs]

theorem minorArc_row_gap (i : Fin 18) (hi : i.val < 17) {t : ℝ}
    (hl : ((minorArcData i).left : ℝ) ≤ t) (hh : t ≤ ((minorArcData i).right : ℝ)) :
    0.17 * (saddleS (Real.exp t)).re < minorArcSaddleGap t - minorArcQstarRow i :=
  minorArc_gap_of_endpoints i hl hh (minorArc_row_gap_endpoint i)
    (minorArc_row_amplitude_endpoint i hi) (minorArcQstarRow_lt i)

theorem minorArc_rows_cover {t : ℝ} (ht0 : 0 ≤ t) (ht6 : t ≤ 6) :
    ∃ i : Fin 18, i.val < 17 ∧ ((minorArcData i).left : ℝ) ≤ t ∧
      t ≤ ((minorArcData i).right : ℝ) := by
  by_cases h0 : t ≤ 0.04
  · refine ⟨0, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h1 : t ≤ 0.08
  · refine ⟨1, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h2 : t ≤ 0.12
  · refine ⟨2, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h3 : t ≤ 0.16
  · refine ⟨3, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h4 : t ≤ 0.20
  · refine ⟨4, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h5 : t ≤ 0.25
  · refine ⟨5, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h6 : t ≤ 0.32
  · refine ⟨6, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h7 : t ≤ 0.40
  · refine ⟨7, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h8 : t ≤ 0.50
  · refine ⟨8, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h9 : t ≤ 0.65
  · refine ⟨9, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h10 : t ≤ 0.85
  · refine ⟨10, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h11 : t ≤ 1
  · refine ⟨11, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h12 : t ≤ 1.5
  · refine ⟨12, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h13 : t ≤ 2.25
  · refine ⟨13, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h14 : t ≤ 4
  · refine ⟨14, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  by_cases h15 : t ≤ 5
  · refine ⟨15, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith
  refine ⟨16, by decide, ?_, ?_⟩ <;> norm_num [minorArcData] <;> linarith

theorem minorArc_tailQstar_gap {t : ℝ} (ht : 6 ≤ t) :
    1.50 < minorArcSaddleGap t - minorArcQstarRow 17 := by
  apply minorArc_tail_gap ht
  simpa [minorArcData] using minorArcQstarRow_lt 17

end DurfeeCCS.Step07
