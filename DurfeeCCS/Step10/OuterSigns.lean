module

public import DurfeeCCS.Step10.OuterSamples
public import DurfeeCCS.Step10.OuterPhase
public import DurfeeCCS.Step10.OuterRoots
public import DurfeeCCS.Step10.OuterFarCoefficients
public import DurfeeCCS.Step10.OuterErrorNormalize
public import Mathlib.Basic.Sign.Defs
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Polynomial

/-- The predicted value of Dₙ at −exp h in the first outer range. -/
def outerPrediction (y h : ℝ) : ℝ :=
  (outerRho h π * Complex.exp ((y : ℂ) * outerRho h π)).re / (4 * π * y ^ 2)

/-- The exact target of Proposition 4.1, in the variable h = 2 log r. -/
def OuterBesselApproximation : Prop :=
  ∀ n : ℕ, 6401 ≤ n → ∀ h : ℝ, outerStart n ≤ h → h ≤ farThreshold n →
    |Step08.durfeeNegativeValue n (exp (h / 2)) - outerPrediction (outerY n) h| <
      0.99 * outerTransformAmplitude (outerY n) h

/-- The exact target of Lemma 4.3, including the threshold equality. -/
def OuterMonomialDominance : Prop :=
  ∀ n : ℕ, 6401 ≤ n → ∀ d : ℕ, 1 ≤ d → d < n.sqrt →
    farThreshold n ≤ farSample n d →
    (∑ l ∈ (Finset.Icc 1 n.sqrt).erase d, farWeighted n l (farSample n d)) <
      farWeighted n d (farSample n d)

theorem durfeeNegativeValue_exp_half (n : ℕ) (h : ℝ) :
    Step08.durfeeNegativeValue n (exp (h / 2)) = (durfeePolynomialReal n).eval (-exp h) := by
  unfold Step08.durfeeNegativeValue durfeePolynomialReal
  rw [eval₂_eq_eval_map, ← Real.exp_nat_mul, Nat.cast_ofNat, show 2 * (h / 2) = h by ring]

theorem outerPrediction_phase (y h : ℝ) :
    outerPrediction y h =
      (‖outerRho h π‖ * exp (y * (outerRho h π).re) / (4 * π * y ^ 2)) *
        cos (outerPhi y h) := by
  let w := outerRho h π
  have hre : ((y : ℂ) * w).re = y * w.re := by simp [Complex.mul_re]
  have him : ((y : ℂ) * w).im = y * w.im := by simp [Complex.mul_im]
  change (w * Complex.exp ((y : ℂ) * w)).re / (4 * π * y ^ 2) =
    (‖w‖ * exp (y * w.re) / (4 * π * y ^ 2)) * cos (y * w.im + w.arg)
  rw [Complex.mul_re, Complex.exp_re, Complex.exp_im, hre, him, Real.cos_add,
    ← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  ring

/-- At every integer phase crossing, the proposition's error margin preserves the sign. -/
theorem outer_sign_at_phase {n d : ℕ} {h : ℝ} (hn : 1 ≤ n) (hh : 0 < h)
    (hphase : outerPhi (outerY n) h = π * d)
    (herr : |Step08.durfeeNegativeValue n (exp (h / 2)) - outerPrediction (outerY n) h| <
      0.99 * outerTransformAmplitude (outerY n) h) :
    0 < (-1 : ℝ) ^ d * Step08.durfeeNegativeValue n (exp (h / 2)) := by
  let y := outerY n
  let w := outerRho h π
  let M := ‖w‖ * exp (y * w.re) / (4 * π * y ^ 2)
  have hy' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 0 < y := sqrt_pos.2 (by linarith)
  have hA : 0 < outerTransformAmplitude y h := by unfold outerTransformAmplitude; positivity
  have hlt : outerTransformAmplitude y h < M := by
    unfold outerTransformAmplitude M
    have hr := (outerRho_re_gt (t := π) hh).trans_le (Complex.re_le_norm w)
    gcongr
  have hc : cos (outerPhi y h) = (-1 : ℝ) ^ d := by
    rw [hphase, mul_comm π, cos_nat_mul_pi]
  rw [outerPrediction_phase, hc] at herr
  change |Step08.durfeeNegativeValue n (exp (h / 2)) - M * (-1 : ℝ) ^ d| <
    0.99 * outerTransformAmplitude y h at herr
  have hh' := abs_lt.mp herr
  rcases neg_one_pow_eq_or ℝ d with hp | hp <;> rw [hp] at hh' ⊢ <;> linarith only [hh'.1, hh'.2, hA, hlt]

theorem outerFirst_phase_mismatch {n : ℕ} (hn : 6401 ≤ n) :
    |Step06.saddlePhase n (sqrt (outerSample n (outerFirst n))) - π * outerFirst n| < 0.48 := by
  let h := outerLogSample n (outerFirst n)
  have hs : sqrt (outerSample n (outerFirst n)) = exp (h / 2) := by
    unfold outerSample
    rw [sqrt_eq_rpow, rpow_def_of_pos (exp_pos _), log_exp]
    simp [h, div_eq_mul_inv]
  have hData := outerFirst_sample hn
  simp only [outerSample, log_exp] at hData
  have hBound : 2 * log (sqrt ((n : ℝ) - 1 / 12)) ≤ h := by
    change 2 * log (outerY n) ≤ h
    rw [← outerStart_eq (by omega : 1 ≤ n)]
    exact hData.1
  have hm := saddlePhase_outerPhase_lt hn hBound
  rw [hs, ← hData.2.2]
  exact hm.trans (by norm_num)

/-- The signs and root intervals in Corollary 4.4 follow from the two outer estimates. -/
theorem outerAlternating_of_estimates (hApprox : OuterBesselApproximation)
    (hDominates : OuterMonomialDominance) {n : ℕ} (hn : 6401 ≤ n) :
    ∃ d₀ : ℕ, ∃ x : ℕ → ℝ,
      (0.92 * outerY n < d₀ ∧ d₀ ≤ n.sqrt - 1) ∧
      (∀ d, d₀ ≤ d → d < n.sqrt → 0 < x d ∧
        (SignType.sign ((durfeePolynomialReal n).eval (-x d)) : ℝ) = (-1 : ℝ) ^ d) ∧
      StrictMonoOn x (Set.Ico d₀ n.sqrt) ∧
      (outerStart n ≤ log (x d₀) ∧ log (x d₀) ≤ outerStart n + 2) ∧
      |Step06.saddlePhase n (sqrt (x d₀)) - π * d₀| < 0.48 ∧
      ∃ r : Fin (n.sqrt - d₀) ↪ ℝ, ∀ i,
        r i < -x d₀ ∧ (durfeePolynomialReal n).IsRoot (r i) := by
  have hStart := outerFirst_bounds hn
  have hh₀ : 0 < n := by omega
  have hd₀ : 0 < outerFirst n := by
    have h : (0 : ℝ) < outerFirst n := lt_of_le_of_lt
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hStart.1
    exact_mod_cast h
  have hr := outerFirst_sample hn
  have hs (d : ℕ) (hd : outerFirst n ≤ d) (hm : d < n.sqrt) :
      0 < (-1 : ℝ) ^ d * (durfeePolynomialReal n).eval (-outerSample n d) := by
    rw [outerSample, ← durfeeNegativeValue_exp_half]
    by_cases hc : farSample n d ≤ farThreshold n
    · have hs := outerLogSample_near hn hd hm hc
      apply outer_sign_at_phase (by omega) ((outerStart_gt hn).trans_le hs.1.1 |>.trans' (by norm_num))
        hs.2 (hApprox n hn _ hs.1.1 (hs.1.2.trans hc))
    · have hh := lt_of_not_ge hc
      rw [outerLogSample_far hh]
      exact farSign_of_dominance hh₀ (Finset.mem_Icc.mpr ⟨by omega, hm.le⟩)
        (hDominates n hn d (by omega) hm hh.le)
  refine ⟨outerFirst n, outerSample n, ⟨hStart.1, by omega⟩, ?_,
    strictMonoOn_outerSample hn, ⟨hr.1, hr.2.1.le⟩, outerFirst_phase_mismatch hn,
    outerRoots_of_alternating hh₀ hStart.2.1 _ (fun _ _ _ => outerSample_pos _ _)
      (strictMonoOn_outerSample hn) hs⟩
  intro d hd hm
  have hp := hs d hd hm
  refine ⟨outerSample_pos _ _, ?_⟩
  rcases neg_one_pow_eq_or ℝ d with hs | hs
  · rw [hs] at hp ⊢
    rw [sign_pos (by simpa only [one_mul] using hp)]
    rfl
  · rw [hs] at hp ⊢
    rw [sign_neg (by linarith only [hp])]
    rfl

end DurfeeCCS.Step10
