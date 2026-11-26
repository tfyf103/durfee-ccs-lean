module

public import DurfeeCCS.Step09.MidErrorAssembly
public import DurfeeCCS.Step09.MidContributionNorm
public import DurfeeCCS.Step09.MidOtherIntegrals

import Mathlib.Tactic.Ring

/-! Turn the absolute masses of Lemma 3.10 into the remaining contour error. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step08

theorem norm_midCentral_other_le {n : ℕ} {r : ℝ}
    (hn : 6400 ≤ n) (hr : 1 ≤ r) (hmax : r ≤ Real.exp 1 * Real.sqrt (n : ℝ))
    (hmass : Summable (fun p : ℤ => midOtherMass n r p (-8) 8)) :
    ‖midCentralContribution n r -
      (midContribution n r 0 0 8 + midContribution n r (-1) (-8) 0)‖ ≤
    midU n r / (4*Real.pi^2) *
      ((∑' p : ℤ, if p = 0 ∨ p = (-1 : ℤ) then 0 else midOtherMass n r p (-8) 8) +
        midOtherMass n r 0 (-8) 0 + midOtherMass n r (-1) 0 8) := by
  let K := midU n r / (4*Real.pi^2)
  let S := midCentralContribution n r
  let f (p : ℤ) := midContribution n r p (-8) 8
  let A := midContribution n r 0 0 8
  let B := midContribution n r (-1) (-8) 0
  let X := midContribution n r 0 (-8) 0
  let Y := midContribution n r (-1) 0 8
  have hn' : 0 < n := by omega
  have hr' : 0 < r := by linarith
  have hf : HasSum f S := hasSum_midContribution_central hn' hr
  have hI := mid_integrable_all hn hr hmax
  have h0 : f 0 = X + A := midContribution_split_at_zero (hI 0)
  have h1 : f (-1) = B + Y := midContribution_split_at_zero (hI (-1))
  have hX : ‖X‖ ≤ K * midOtherMass n r 0 (-8) 0 :=
    norm_midContribution_le hn' hr' le_rfl (by norm_num) (by norm_num) (hI 0)
  have hY : ‖Y‖ ≤ K * midOtherMass n r (-1) 0 8 :=
    norm_midContribution_le hn' hr' (by norm_num) le_rfl (by norm_num) (hI (-1))
  have hpoint (p : ℤ) : ‖f p‖ ≤ K * midOtherMass n r p (-8) 8 :=
    norm_midContribution_le hn' hr' le_rfl le_rfl (by norm_num) (hI p)
  have htail := norm_mid_nonprincipal_le hf (hmass.mul_left K) hpoint
  have he (p : ℤ) :
      (if p = 0 ∨ p = (-1 : ℤ) then 0 else K * midOtherMass n r p (-8) 8) =
      K * (if p = 0 ∨ p = (-1 : ℤ) then 0 else midOtherMass n r p (-8) 8) := by
    split <;> simp
  simp_rw [he, tsum_mul_left] at htail
  have hnorm :
      ‖S - (A+B)‖ ≤ ‖S-f 0-f (-1)‖ + ‖X‖ + ‖Y‖ := by
    have h : S - (A+B) = ((S-f 0-f (-1))+X)+Y := by rw [h0,h1]; ring
    rw [h]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  refine hnorm.trans ((add_le_add (add_le_add htail hX) hY).trans_eq ?_)
  change K * _ + K * _ + K * _ = K * _
  ring

end DurfeeCCS.Step09
