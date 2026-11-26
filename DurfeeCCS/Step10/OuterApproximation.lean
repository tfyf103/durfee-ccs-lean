module

public import DurfeeCCS.Step10.OuterFiniteExpansionData
public import DurfeeCCS.Step10.OuterErrorTransfer
public import DurfeeCCS.Step10.OuterFar
public import DurfeeCCS.Step10.OuterEulerWeightFiniteProduct
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset

/-- The final preprocessing estimate before the Poisson bounds are applied. -/
def OuterPreprocessingError : Prop :=
  ∀ n : ℕ, 6401 ≤ n → ∀ h : ℝ, outerStart n ≤ h → h ≤ farThreshold n →
    |Step08.durfeeNegativeValue n (exp (h / 2)) -
      ∑ abj ∈ outerGoodTriples n, outerTripleKernel n h abj| <
        0.022 * outerTransformAmplitude (outerY n) h

def outerTripleMass (Y h : ℝ) (abj : ℕ × ℕ × ℕ) : ℝ :=
  (outerMixedCoeff abj.1 abj.2.1 abj.2.2 : ℝ) *
    exp (-h / 2) ^ (abj.1 + abj.2.1) *
      exp (-(outerWeightSigma Y h) * outerGamma abj.1 abj.2.1 abj.2.2)

/-- The Euler product bounds the mass of every nonzero triple used by the outer proof. -/
def OuterTripleMassBound : Prop :=
  ∀ n : ℕ, 6401 ≤ n → ∀ h : ℝ, outerStart n ≤ h →
    (∑ abj ∈ (outerGoodTriples n).erase (0, 0, 0), outerTripleMass (outerY n) h abj) ≤
      exp 0.461 - 1


theorem outerTripleMass_bound : OuterTripleMassBound := by
  intro n hn h hh
  let Y := outerY n
  let w := exp (-h / 2)
  let σ := outerWeightSigma Y h
  have hY : 80 ≤ Y := (eighty_lt_outerY hn).le
  have hStart : 2 * log Y ≤ h := by
    rw [← outerStart_eq (by omega : 1 ≤ n)]
    exact hh
  have hw₀ : 0 ≤ w := (exp_pos _).le
  have hw : w < 1 := exp_lt_one_iff.mpr (by linarith [(outerStart_gt hn).trans_le hh])
  have hσ : 0 < σ := outerWeightSigma_pos hY hStart
  have hA := finite_nonzero_gamma_weight_le (w := w) (σ := σ) hw₀ hw hσ
    ((outerGoodTriples n).erase (0, 0, 0)) (by simp)
  have hCap : outerWeightProduct w σ < exp 0.461 := outerWeightProduct_cap hY hStart
  exact (show _ ≤ outerWeightProduct w σ - 1 from hA).trans (sub_le_sub_right hCap.le _)

theorem outerTripleKernel_le_mass {n : ℕ} (hn : 6401 ≤ n) {h : ℝ}
    (hh : outerStart n ≤ h) (hcap : h ≤ farThreshold n)
    {abj : ℕ × ℕ × ℕ} (habj : abj ∈ outerGoodTriples n) :
    |outerTripleKernel n h abj| ≤
      (1.42 * outerTransformAmplitude (outerY n) h) * outerTripleMass (outerY n) h abj := by
  rcases abj with ⟨a, b, j⟩
  let Y := outerY n
  let y := outerTripleRadius n a b j
  let x : ℝ := ((a : ℝ) + b) / 2
  let P : ℝ := outerMixedCoeff a b j
  let m (k : ℤ) := kernelTransform y ((h : ℂ) + (outerFrequency k : ℂ) * Complex.I)
  have hh' := (outerStart_gt hn).trans_le hh
  have hY : 80 < Y := eighty_lt_outerY hn
  have hY₀ : 0 < Y := by linarith
  have hy : 0.9 * Y ≤ y := (mem_filter.mp habj).2
  have hy₀ : 0 < y := by linarith
  have hyY := outerTripleRadius_le n a b j
  have hdiff : 0 ≤ Y ^ 2 - outerGamma a b j := (sqrt_pos.mp hy₀).le
  have hγ : Y ^ 2 - y ^ 2 = outerGamma a b j := by
    change Y ^ 2 - sqrt (Y ^ 2 - outerGamma a b j) ^ 2 = _
    rw [sq_sqrt hdiff]
    ring
  have hP : 0 ≤ P := by
    change (0 : ℝ) ≤ (outerMixedCoeff a b j : ℝ)
    exact_mod_cast outerMixedCoeff_nonneg a b j
  have hAn := outerTransformAmplitude_pos hY₀ (show 0 < h by linarith [hh'])
  have hratio := outerAmplitude_ratio hY.le (by linarith only [hy, hY]) hyY hh' hγ
  have hAratio : outerTransformAmplitude y h ≤
      outerTransformAmplitude Y h * exp (-(outerWeightSigma Y h) * outerGamma a b j) := by
    convert (div_le_iff₀ hAn).mp hratio using 1
    unfold outerWeightSigma
    ring
  have hModes : Summable (fun k : ℤ => ‖m k‖) ∧
      (∑' k : ℤ, ‖m k‖) < 1.42 * outerTransformAmplitude y h := by
    simpa only [m, outerZeta, mul_comm Complex.I] using outerTransformAbsSum hY (show (9 / 10 : ℝ) * Y ≤ y by linarith only [hy]) hh' hcap
  let E (k : ℤ) := Complex.exp (-((outerFrequency k * x : ℝ) : ℂ) * Complex.I) * m k
  have hE (k : ℤ) : ‖E k‖ = ‖m k‖ := by
    dsimp only [E]
    rw [norm_mul, Complex.norm_exp, Complex.mul_re]
    simp
  have hsum : ‖∑' k, E k‖ ≤ 1.42 * outerTransformAmplitude y h := by
    have hS : Summable fun k => ‖E k‖ := by simpa only [hE] using hModes.1
    have hN := norm_tsum_le_tsum_norm hS
    simp only [hE] at hN
    exact hN.trans hModes.2.le
  have hPoisson := shifted_outerBessel_poisson hy₀.le h x
  change |(-1 : ℝ) ^ (a + b) * P * (∑' d : ℤ, (-(exp h : ℂ)) ^ d *
      (outerBesselKernel y ((d : ℝ) + x) : ℂ)).re| ≤ _
  rw [hPoisson, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hP, Complex.re_ofReal_mul, abs_mul, abs_of_pos (exp_pos _)]
  change P * (exp (-h * x) * |(∑' k, E k).re|) ≤ _
  calc
    _ ≤ P * (exp (-h * x) * (1.42 * outerTransformAmplitude y h)) := by
      gcongr
      exact (Complex.abs_re_le_norm _).trans hsum
    _ ≤ P * (exp (-h * x) *
        (1.42 * (outerTransformAmplitude Y h * exp (-(outerWeightSigma Y h) * outerGamma a b j)))) := by
      gcongr
    _ = _ := by
      have hx : exp (-h * x) = exp (-h / 2) ^ (a + b) := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [x]
        push_cast
        ring
      rw [hx]
      simp only [outerTripleMass]
      dsimp [Y, P]
      ring

private theorem outerTriple_zero_mem {n : ℕ} (hn : 6401 ≤ n) :
    (0, 0, 0) ∈ outerGoodTriples n := by
  have hy : 0 ≤ outerY n := (eighty_lt_outerY hn).le.trans' (by norm_num)
  simp only [outerGoodTriples, mem_filter, outerTripleBox, mem_product, mem_range, Nat.zero_lt_succ,
    and_self, true_and]
  have hr : outerTripleRadius n 0 0 0 = outerY n := by simp [outerTripleRadius, outerGamma, sqrt_sq hy]
  rw [hr]
  linarith

theorem outerTripleKernel_zero_error {n : ℕ} (hn : 6401 ≤ n) {h : ℝ}
    (hh : outerStart n ≤ h) (hcap : h ≤ farThreshold n) :
    |outerTripleKernel n h (0, 0, 0) - outerPrediction (outerY n) h| <
      0.130 * outerTransformAmplitude (outerY n) h := by
  let Y := outerY n
  have hy : 80 < Y := eighty_lt_outerY hn
  have hr : outerTripleRadius n 0 0 0 = Y := by
    simp [outerTripleRadius, outerGamma, sqrt_sq (by linarith : 0 ≤ Y), Y]
  have hP := shifted_outerBessel_poisson (by linarith : 0 ≤ Y) h 0
  have hP' : (∑' d : ℤ, (-(exp h : ℂ)) ^ d * (outerBesselKernel Y (d : ℝ) : ℂ)) =
      ∑' p : ℤ, kernelTransform Y (outerZeta h (outerFrequency p)) := by
    simpa [outerZeta, mul_comm Complex.I] using hP
  have hb := outerTransformLeadingPair hy ((outerStart_gt hn).trans_le hh) hcap
  have hmain : outerPrediction Y h = 2 * (outerMainMode Y h π).re := by
    unfold outerPrediction outerMainMode outerEndpointMain
    rw [show (8 : ℂ) * (π : ℂ) * (Y : ℂ) ^ 2 = ((8 * π * Y ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.div_ofReal_re]
    ring
  simp only [outerTripleKernel, hr, outerMixedCoeff_zero_zero, Nat.cast_zero,
    zero_div, add_zero, pow_zero, ite_true, Int.cast_one, one_mul, hP']
  change |(∑' p : ℤ, kernelTransform Y (outerZeta h (outerFrequency p))).re - outerPrediction Y h| <
    0.130 * outerTransformAmplitude Y h
  rw [hmain]
  have hR := Complex.abs_re_le_norm ((∑' p : ℤ, kernelTransform Y (outerZeta h (outerFrequency p))) -
    ((2 * (outerMainMode Y h π).re : ℝ) : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hR
  exact hR.trans_lt hb

/-- The strict numerical budget for Proposition 4.1, on the full n and h intervals. -/
theorem outerBesselApproximation_of_errors (hpre : OuterPreprocessingError)
    (hmass : OuterTripleMassBound) : OuterBesselApproximation := by
  intro n hn h hh hcap
  let A := outerTransformAmplitude (outerY n) h
  let S := (outerGoodTriples n).erase ((0, 0, 0) : ℕ × ℕ × ℕ)
  let V := Step08.durfeeNegativeValue n (exp (h / 2))
  let Q := ∑ abj ∈ outerGoodTriples n, outerTripleKernel n h abj
  let M := outerPrediction (outerY n) h
  have hA : 0 < A := outerTransformAmplitude_pos (by linarith [eighty_lt_outerY hn])
    (by linarith [(outerStart_gt hn).trans_le hh])
  have hQ : Q = outerTripleKernel n h (0, 0, 0) + ∑ abj ∈ S, outerTripleKernel n h abj :=
    (add_sum_erase _ _ (outerTriple_zero_mem hn)).symm
  have hRest :
      |∑ abj ∈ S, outerTripleKernel n h abj| ≤ 1.42 * (exp 0.461 - 1) * A := by
    calc
      _ ≤ ∑ abj ∈ S, |outerTripleKernel n h abj| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ abj ∈ S, (1.42 * A) * outerTripleMass (outerY n) h abj :=
        Finset.sum_le_sum (fun _ hp => outerTripleKernel_le_mass hn hh hcap (mem_of_mem_erase hp))
      _ = (1.42 * A) * ∑ abj ∈ S, outerTripleMass (outerY n) h abj := by rw [mul_sum]
      _ ≤ (1.42 * A) * (exp 0.461 - 1) :=
        mul_le_mul_of_nonneg_left (hmass n hn h hh) (by positivity)
      _ = _ := by ring
  have hC : (0.022 + 0.130 + 1.42 * (exp 0.461 - 1) : ℝ) < 0.984 := by
    dyadic_interval +kernel [prec := 34]
  have h₁ : |V - Q| < 0.022 * A := hpre n hn h hh hcap
  have h₂ : |outerTripleKernel n h (0, 0, 0) - M| < 0.130 * A :=
    outerTripleKernel_zero_error hn hh hcap
  change |V - M| < 0.99 * A
  rw [show V - M = (V - Q) + (outerTripleKernel n h (0, 0, 0) - M) +
    ∑ abj ∈ S, outerTripleKernel n h abj by rw [hQ]; ring]
  have hd := (abs_add_le (V - Q + (outerTripleKernel n h (0, 0, 0) - M)) _).trans
    (add_le_add (abs_add_le _ _) hRest)
  have he := mul_lt_mul_of_pos_right (hC.trans (by norm_num : (0.984 : ℝ) < 0.99)) hA
  linarith only [h₁, h₂, hd, he]

end DurfeeCCS.Step10
