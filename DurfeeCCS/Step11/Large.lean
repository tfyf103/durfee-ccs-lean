module

public import DurfeeCCS.Step11.NearOrigin
public import DurfeeCCS.Step11.OuterEndpoint
public import DurfeeCCS.Step11.PhaseLadder
public import DurfeeCCS.Step11.ThreeIntervals
public import DurfeeCCS.FiniteRoots

/-! Join the three disjoint ranges of the large-size proof. -/

public section

namespace DurfeeCCS.Step11

open Polynomial Real

/-- At large sizes the three root lists occupy the three open intervals of the manuscript. -/
theorem large_durfee_root_intervals {n : ℕ} (hn : 6401 ≤ n) :
    ∃ d₀ : ℕ, ∃ rPlus : ℝ, 10 ≤ d₀ ∧ d₀ < n.sqrt ∧ nearOriginRadius n < rPlus ∧
      ∃ (outer : Fin (n.sqrt - d₀) ↪ ℝ) (middle : Fin (d₀ - 8) ↪ ℝ) (near : Fin 7 ↪ ℝ),
        (∀ i, outer i < -(rPlus ^ 2) ∧ (durfeePolynomialReal n).IsRoot (outer i)) ∧
        (∀ i, middle i ∈ Set.Ioo (-(rPlus ^ 2)) (-(nearOriginRadius n ^ 2)) ∧
          (durfeePolynomialReal n).IsRoot (middle i)) ∧
        (∀ i, near i ∈ Set.Ioo (-(nearOriginRadius n ^ 2)) 0 ∧
          (durfeePolynomialReal n).IsRoot (near i)) := by
  obtain ⟨d₀, rPlus, hd, hdm, hrPlus, hrMax, hsignPlus, hphasePlus, outer, houter⟩ :=
    outerEndpoint hn
  have hr := (nearOriginRadius_lt_one hn).trans hrPlus
  have hphaseNear := nearOrigin_phase_lt_nine_pi hn
  obtain ⟨middle, hmiddle⟩ :=
    middleRoots_of_endpoint_phase (by omega : 6400 ≤ n) (by omega : 9 ≤ d₀)
      (nearOriginRadius_pos hn) hr hrMax.le (sqrt_mul_nearOriginRadius hn).ge
      hphaseNear hphasePlus (nearOrigin_endpoint_pos hn) hsignPlus
  obtain ⟨near, hnear⟩ := nearOrigin_seven_roots hn
  exact ⟨d₀, rPlus, hd, hdm, hr, outer, middle, near, houter, hmiddle, hnear⟩

/-- The large-size branch of Theorem 1.2. -/
theorem largeDurfeeRoots {n : ℕ} (hn : 6401 ≤ n) : HasDurfeeRoots n := by
  obtain ⟨d₀, rPlus, hd, hdm, hr, outer, middle, near, houter, hmiddle, hnear⟩ :=
    large_durfee_root_intervals hn
  have hpos := nearOriginRadius_pos hn
  have hab : -(rPlus ^ 2) < -(nearOriginRadius n ^ 2) := by
    have h := pow_lt_pow_left₀ hr hpos.le (n := 2) (by decide)
    exact neg_lt_neg h
  have hb : -(nearOriginRadius n ^ 2) < 0 := neg_lt_zero.mpr (pow_pos hpos _)
  obtain ⟨r, hr', hcomplete⟩ :=
    durfeeRootCompletion_of_threeIntervals (by omega : 0 < n) (by omega : 8 ≤ d₀)
      hdm.le hab hb outer middle near houter
      (fun i => ⟨(hmiddle i).1.1, (hmiddle i).1.2, (hmiddle i).2⟩)
      (fun i => ⟨(hnear i).1.1, (hnear i).1.2, (hnear i).2⟩)
  exact ⟨r, fun i => (hr' i).1, hcomplete⟩

end DurfeeCCS.Step11
