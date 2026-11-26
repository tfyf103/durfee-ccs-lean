module

public import DurfeeCCS.Step10.OuterFarDominance
public import DurfeeCCS.Step10.OuterCoeff
public import DurfeeCCS.Step10.OuterCoeffElementary

/-! Unconditional single-monomial domination and signs in the far outer range. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Step06 Finset

theorem outerFar_coefficientBounds : FarCoefficientBounds := by
  refine ⟨fun t ht => lemma42.1 ht, fun t ht => lemma42.2.1 ht, fun t ht => lemma42.2.2 ht, ?_⟩
  intro t ht
  have ht' : (t : ℝ) ≤ 25 := by exact_mod_cast ht.le
  have hsq : sqrt ((t : ℝ) / 3) ≤ 5 / sqrt 3 := by
    calc
      _ ≤ sqrt (25 / 3) := sqrt_le_sqrt (by linarith)
      _ = _ := by rw [sqrt_div (by norm_num), show (25 : ℝ) = (5 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
  apply (twoColour_exp_bound t).trans
  apply exp_le_exp.mpr
  calc
    _ ≤ 2 * π * (5 / sqrt 3) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

/-- Lemma 4.3 in the manuscript. -/
theorem lemma43 {n d : ℕ} (hn : 6401 ≤ n) (hd : 1 ≤ d) (hdm : d < n.sqrt)
    (hfar : farThreshold n ≤ farSample n d) :
    (∑ l ∈ (Finset.Icc 1 n.sqrt).erase d, farWeighted n l (farSample n d)) <
      farWeighted n d (farSample n d) :=
  singleMonomialDominates outerFar_coefficientBounds hn hd hdm hfar

/-- Far-range sign used in the construction of the alternating radii. -/
theorem farSample_sign {n d : ℕ} (hn : 6401 ≤ n) (hd : 1 ≤ d) (hdm : d < n.sqrt)
    (hfar : farThreshold n ≤ farSample n d) :
    0 < (-1 : ℝ) ^ d * Step08.durfeeNegativeValue n (exp (farSample n d / 2)) :=
  farSample_sign_of_coefficientBounds outerFar_coefficientBounds hn hd hdm hfar

end DurfeeCCS.Step10
