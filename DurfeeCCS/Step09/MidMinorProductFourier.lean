module

public import DurfeeCCS.Step09.MidMinorProductClipping

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Absolute Fourier regrouping for the clipped angular product in (62). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex

private def clippedLogKernel (u t v θ : ℝ) (m j : ℕ) : ℂ :=
  - (-(midClippedTerm u t v θ m)) ^ (j + 1) / ((j + 1 : ℕ) : ℂ)

private theorem hasSum_clippedLogKernel (u t v θ : ℝ) (m : ℕ) :
    HasSum (fun j => clippedLogKernel u t v θ m j) (log (1 + midClippedTerm u t v θ m)) := by
  have hm : ‖-(midClippedTerm u t v θ m)‖ < 1 := by
    rw [norm_neg]
    exact (norm_midClippedTerm_le u t v θ m).trans_lt (by norm_num [midMinorAlpha])
  simpa only [clippedLogKernel, neg_div, neg_neg, sub_neg_eq_add, Nat.cast_add, Nat.cast_one] using
    (Complex.hasSum_taylorSeries_neg_log' hm).neg

private theorem midMinorWeight_pow (u t : ℝ) (m : ℤ) (j : ℕ) :
    (midMinorWeight 1 u t m)^j = midMinorWeight j u t m := by
  simp only [midMinorWeight, ← Real.exp_nat_mul, Nat.cast_one]
  congr 1
  ring

private theorem midMinorWeight_one_nonneg (u t : ℝ) (m : ℤ) :
    0 ≤ midMinorWeight 1 u t m := Real.exp_nonneg _

private theorem midMinorWeight_one_le_one (u t : ℝ) (m : ℤ) :
    midMinorWeight 1 u t m ≤ 1 := by
  unfold midMinorWeight
  push_cast
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (abs_nonneg _))

private theorem midMinorAlpha_nonneg : 0 ≤ midMinorAlpha := by norm_num [midMinorAlpha]

private theorem midMinorAlpha_lt_one : midMinorAlpha < 1 := by norm_num [midMinorAlpha]

private theorem norm_clippedLogKernel_le (u t v θ : ℝ) (m j : ℕ) :
    ‖clippedLogKernel u t v θ m j‖ ≤ midMinorWeight 1 u t m * midMinorAlpha ^ j := by
  let w := midMinorWeight 1 u t m
  have hw₀ : 0 ≤ w := midMinorWeight_one_nonneg u t m
  have hw₁ : w ≤ 1 := midMinorWeight_one_le_one u t m
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos j
  have hα : midMinorAlpha ^ (j+1) ≤ midMinorAlpha ^ j :=
    pow_le_pow_of_le_one midMinorAlpha_nonneg midMinorAlpha_lt_one.le (by omega)
  have hp : w ^ (j+1) ≤ w := by
    simpa only [pow_one] using pow_le_pow_of_le_one hw₀ hw₁ (show 1 ≤ j+1 by omega)
  rw [clippedLogKernel, norm_div, norm_neg, norm_pow, norm_neg, norm_midClippedTerm,
    Complex.norm_natCast]
  change (midMinorAlpha * w)^(j+1) / ((j+1 : ℕ) : ℝ) ≤ _
  calc
    _ ≤ (midMinorAlpha * w)^(j+1) := div_le_self (pow_nonneg (mul_nonneg midMinorAlpha_nonneg hw₀) _) hj
    _ = midMinorAlpha^(j+1) * w^(j+1) := mul_pow _ _ _
    _ ≤ midMinorAlpha^j * w := mul_le_mul hα hp (pow_nonneg hw₀ _) (pow_nonneg midMinorAlpha_nonneg _)
    _ = _ := mul_comm _ _

private theorem clippedLogKernel_summable_norm {u : ℝ} (hu : 0 < u) (t v θ : ℝ) :
    Summable (fun mj : ℕ × ℕ => ‖clippedLogKernel u t v θ mj.1 mj.2‖) := by
  have hm := summable_midMinorWeight (by decide : 0 < (1 : ℕ)) hu t
  have hj := summable_geometric_of_lt_one midMinorAlpha_nonneg midMinorAlpha_lt_one
  exact (hm.mul_of_nonneg hj (fun m => midMinorWeight_one_nonneg u t m)
    (fun j => pow_nonneg midMinorAlpha_nonneg j)).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun mj => norm_clippedLogKernel_le u t v θ mj.1 mj.2)

private def clippedFourierCoeff (u t v θ : ℝ) (j : ℕ) : ℂ :=
  ∑' m : ℕ, clippedLogKernel u t v θ m j

private theorem tsum_clippedLogKernel_eq_tsum_fourier {u : ℝ} (hu : 0 < u) (t v θ : ℝ) :
    (∑' m : ℕ, log (1 + midClippedTerm u t v θ m)) = ∑' j : ℕ, clippedFourierCoeff u t v θ j := by
  have h := (clippedLogKernel_summable_norm hu t v θ).of_norm
  calc
    _ = ∑' m : ℕ, ∑' j : ℕ, clippedLogKernel u t v θ m j :=
      tsum_congr (fun m => (hasSum_clippedLogKernel u t v θ m).tsum_eq.symm)
    _ = _ := (Summable.tsum_comm (f := clippedLogKernel u t v θ) h).symm

private theorem summable_clippedFourierCoeff {u : ℝ} (hu : 0 < u) (t v θ : ℝ) :
    Summable (clippedFourierCoeff u t v θ) :=
  (clippedLogKernel_summable_norm hu t v θ).of_norm.prod_symm.prod

private theorem midClippedTerm_pow_eq_mode {u t v θ : ℝ} (m j : ℕ) :
    (midClippedTerm u t v θ m)^j = (midMinorAlpha : ℂ)^j *
      midMinorPhase ((j : ℝ)*(Real.pi/2 - v/2 + θ)) * midMinorTerm j u t (-v) m := by
  have hangle : (j : ℝ)*midFactorAngle v θ m =
      (j : ℝ)*(Real.pi/2 - v/2 + θ) + (j : ℝ)*(m : ℤ)*(-v) := by
    unfold midFactorAngle
    push_cast
    ring
  rw [midClippedTerm, mul_pow, ← Complex.ofReal_pow, mul_pow, midMinorWeight_pow,
    ← midMinorPhase_nat_mul, hangle, midMinorPhase_add, midMinorTerm]
  push_cast
  ring

private theorem clippedFourierCoeff_eq_mode (u t v θ : ℝ) (j : ℕ) :
    clippedFourierCoeff u t v θ j =
      (((-1 : ℂ)^j * (midMinorAlpha : ℂ)^(j+1)) / ((j + 1 : ℕ) : ℂ)) *
        midMinorPhase ((((j + 1 : ℕ) : ℝ))*(Real.pi/2 - v/2 + θ)) *
          midMinorMode (j+1) u t (-v) := by
  have h (m : ℕ) : clippedLogKernel u t v θ m j =
      (((-1 : ℂ)^j * (midMinorAlpha : ℂ)^(j+1)) / ((j + 1 : ℕ) : ℂ)) *
        midMinorPhase ((((j + 1 : ℕ) : ℝ))*(Real.pi/2 - v/2 + θ)) *
          midMinorTerm (j+1) u t (-v) m := by
    rw [clippedLogKernel, neg_eq_neg_one_mul (midClippedTerm u t v θ m), mul_pow,
      midClippedTerm_pow_eq_mode, pow_succ (-1 : ℂ)]
    ring
  simp_rw [clippedFourierCoeff, h, tsum_mul_left, midMinorMode]

private theorem norm_clippedFourierCoeff (u t v θ : ℝ) (j : ℕ) :
    ‖clippedFourierCoeff u t v θ j‖ =
      (midMinorAlpha^(j+1) / ((j + 1 : ℕ) : ℝ)) * ‖midMinorMode (j+1) u t v‖ := by
  rw [clippedFourierCoeff_eq_mode, norm_mul, norm_mul, norm_div, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg midMinorAlpha_nonneg, Complex.norm_natCast, norm_midMinorPhase,
    mul_one, midMinorMode_neg, Complex.norm_conj]

theorem norm_midMinorMode_succ_le_weight_one {u : ℝ} (hu : 0 < u) (t v : ℝ) (j : ℕ) :
    ‖midMinorMode (j+1) u t v‖ ≤ ∑' m : ℕ, midMinorWeight 1 u t m := by
  refine (norm_midMinorMode_le_zero (Nat.succ_pos j) hu t v).trans ?_
  refine (summable_midMinorWeight (Nat.succ_pos j) hu t).tsum_le_tsum ?_
    (summable_midMinorWeight (by decide : 0 < (1:ℕ)) hu t)
  intro m
  rw [← midMinorWeight_pow]
  simpa only [pow_one] using pow_le_pow_of_le_one (midMinorWeight_one_nonneg u t m)
    (midMinorWeight_one_le_one u t m) (show 1 ≤ j+1 by omega)

theorem summable_norm_weighted_midMinorMode {u : ℝ} (hu : 0 < u) (t v : ℝ) :
    Summable (fun j : ℕ => (2 * midMinorAlpha^(j+1) / ((j+1:ℕ):ℝ)) *
      ‖midMinorMode (j+1) u t v‖) := by
  let C := ∑' m : ℕ, midMinorWeight 1 u t m
  have hC : 0 ≤ C := tsum_nonneg (fun m => midMinorWeight_one_nonneg u t m)
  have hs := (summable_geometric_of_lt_one midMinorAlpha_nonneg midMinorAlpha_lt_one).mul_left (2*C)
  refine hs.of_nonneg_of_le (fun j => by
    have : 0 ≤ midMinorAlpha := midMinorAlpha_nonneg
    positivity) (fun j => ?_)
  have hnum : 2*midMinorAlpha^(j+1) ≤ 2*midMinorAlpha^j :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one midMinorAlpha_nonneg midMinorAlpha_lt_one.le (by omega)) (by norm_num)
  have hdiv : 2*midMinorAlpha^(j+1)/((j+1:ℕ):ℝ) ≤ 2*midMinorAlpha^j := by
    have hj : (1:ℝ) ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos j
    exact (div_le_self (by have := midMinorAlpha_nonneg; positivity) hj).trans hnum
  refine (mul_le_mul hdiv (norm_midMinorMode_succ_le_weight_one hu t v j) (norm_nonneg _)
    (by have := midMinorAlpha_nonneg; positivity)).trans_eq ?_
  ring

/-- The Fourier terms of the two clipped factors are bounded by the
corresponding absolute angular modes, after the absolutely convergent exchange. -/
theorem midClipped_log_fourier_le {u : ℝ} (hu : 0 < u) (t v θ : ℝ) :
    ((∑' m : ℕ, (log (1 + midClippedTerm u t v θ m) +
       log (1 + midClippedTerm u t v (-θ) m))) : ℂ).re ≤
      ∑' i : ℕ, (2 * midMinorAlpha^(i+1) / ((i+1:ℕ):ℝ)) *
        ‖midMinorMode (i+1) u t v‖ := by
  have hS (φ : ℝ) := (summable_norm_log_midClippedTerm hu t v φ).of_norm
  have hLog := ((hS θ).hasSum.add (hS (-θ)).hasSum).tsum_eq
  have hFourier := ((summable_clippedFourierCoeff hu t v θ).hasSum.add
    (summable_clippedFourierCoeff hu t v (-θ)).hasSum).tsum_eq
  rw [hLog, tsum_clippedLogKernel_eq_tsum_fourier hu t v θ,
    tsum_clippedLogKernel_eq_tsum_fourier hu t v (-θ), ← hFourier]
  change Complex.reCLM (∑' j, (clippedFourierCoeff u t v θ j + clippedFourierCoeff u t v (-θ) j)) ≤ _
  rw [Complex.reCLM.map_tsum ((summable_clippedFourierCoeff hu t v θ).add
    (summable_clippedFourierCoeff hu t v (-θ)))]
  refine (Complex.reCLM.summable ((summable_clippedFourierCoeff hu t v θ).add
    (summable_clippedFourierCoeff hu t v (-θ)))).tsum_le_tsum ?_
    (summable_norm_weighted_midMinorMode hu t v)
  intro j
  change (clippedFourierCoeff u t v θ j + clippedFourierCoeff u t v (-θ) j).re ≤ _
  refine ((Complex.re_le_norm _).trans (norm_add_le _ _)).trans_eq ?_
  rw [norm_clippedFourierCoeff, norm_clippedFourierCoeff]
  ring

end DurfeeCCS.Step09
