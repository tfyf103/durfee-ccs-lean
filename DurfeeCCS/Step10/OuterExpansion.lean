module

public import DurfeeCCS.Step10.OuterEulerTail
public import DurfeeCCS.Step10.OuterFiniteExpansionData
public import DurfeeCCS.Step09.MidPoissonEuler
public import DurfeeCCS.Step09.MidPoissonProduct
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Finset PowerSeries MeasureTheory Step06 Step09

private def twoColourFormal : ℤ⟦X⟧ := PowerSeries.mk twoColourPartitionCount

private def shiftedPairSeries (d a b : ℕ) : ℤ⟦X⟧ :=
  (C ((-1 : ℤ) ^ a * (-1 : ℤ) ^ b) * X ^ (outerTailPower d a + outerTailPower d b)) *
    ((restrictedPartitionSeries a * restrictedPartitionSeries b) * twoColourFormal)

/-- One summand of the finite expansion for the d-th Durfee coefficient. -/
def outerShiftedCoeff (d a b N : ℕ) : ℤ :=
  if outerTailPower d a + outerTailPower d b ≤ N then
    (-1 : ℤ) ^ (a + b) *
      ∑ j ∈ range (N - (outerTailPower d a + outerTailPower d b) + 1),
        outerMixedCoeff a b j *
          twoColourPartitionCount (N - (outerTailPower d a + outerTailPower d b) - j)
  else 0

private theorem coeff_shiftedPairSeries (d a b N : ℕ) :
    coeff N (shiftedPairSeries d a b) = outerShiftedCoeff d a b N := by
  let v := outerTailPower d a + outerTailPower d b
  unfold shiftedPairSeries outerShiftedCoeff
  rw [mul_assoc, coeff_C_mul, mul_comm (X ^ v), coeff_mul_X_pow', ← pow_add]
  split_ifs
  · congr 1
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j k =>
      coeff j (restrictedPartitionSeries a * restrictedPartitionSeries b) * coeff k twoColourFormal)]
    simp [outerMixedCoeff, twoColourFormal, v]
  · simp

private theorem hasSum_shiftedPairSeries {q : ℂ} (hq : ‖q‖ < 1) (d a b : ℕ) :
    HasSum (fun N => ((outerShiftedCoeff d a b N : ℤ) : ℂ) * q ^ N)
      (twoColourGenerating q * outerTailTerm q d a * outerTailTerm q d b) ∧
    Summable (fun N => ‖((outerShiftedCoeff d a b N : ℤ) : ℂ) * q ^ N‖) := by
  let v := outerTailPower d a + outerTailPower d b
  let s : ℤ := (-1) ^ a * (-1) ^ b
  let M : ℤ⟦X⟧ := C s * X ^ v
  have hC (N : ℕ) : ((coeff N M : ℤ) : ℂ) * q ^ N =
      if N = v then (s : ℂ) * q ^ v else 0 := by
    rw [show coeff N M = _ from coeff_C_mul_X_pow s v N]
    split_ifs <;> simp_all
  have hM : HasSum (fun N => ((coeff N M : ℤ) : ℂ) * q ^ N) ((s : ℂ) * q ^ v) := by
    simp_rw [hC]
    exact hasSum_ite_eq v _
  have hMN : Summable (fun N => ‖((coeff N M : ℤ) : ℂ) * q ^ N‖) := by
    simp_rw [hC, apply_ite norm, norm_zero]
    exact (hasSum_ite_eq v _).summable
  obtain ⟨hS, hSN⟩ := hasSum_coeff_restrictedMixedSeries hq a b
  have hF : HasSum (fun N => ((coeff N twoColourFormal : ℤ) : ℂ) * q ^ N)
      (twoColourGenerating q) := by
    simpa only [twoColourFormal, coeff_mk, twoColourGenerating_eq_tsum hq] using
      (summable_norm_twoColourGenerating hq).of_norm.hasSum
  have hFN : Summable (fun N => ‖((coeff N twoColourFormal : ℤ) : ℂ) * q ^ N‖) := by
    simpa only [twoColourFormal, coeff_mk] using summable_norm_twoColourGenerating hq
  obtain ⟨hP, hPN⟩ := hasSum_coeff_mul_of_summable_norm hS hSN hF hFN
  obtain ⟨hV, hVN⟩ := hasSum_coeff_mul_of_summable_norm hM hMN hP hPN
  have hV' : HasSum (fun N => ((coeff N (shiftedPairSeries d a b) : ℤ) : ℂ) * q ^ N) _ := hV
  have hVN' : Summable
      (fun N => ‖((coeff N (shiftedPairSeries d a b) : ℤ) : ℂ) * q ^ N‖) := hVN
  simp_rw [coeff_shiftedPairSeries] at hV' hVN'
  refine ⟨?_, hVN'⟩
  convert hV' using 1
  simp only [outerTailTerm, s, v, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    pow_add, div_eq_mul_inv]
  ring

private theorem power_factor_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (j : ℕ) :
    1 - q ^ (j + 1) ≠ 0 := by
  have h := pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero j)
  rw [← norm_pow] at h
  intro he
  have hq' : q ^ (j + 1) = 1 := (sub_eq_zero.mp he).symm
  simp [hq'] at h

private theorem tailTerm_norm_le {q : ℂ} {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1)
    (hqr : ‖q‖ = r) (d a : ℕ) :
    ‖outerTailTerm q d a‖ ≤ ‖outerTailTerm (r : ℂ) d a‖ := by
  have hq : ‖q‖ < 1 := hqr ▸ hr
  have hrq : ‖(r : ℂ)‖ = r := by simp [abs_of_nonneg hr₀]
  have h1 (j : ℕ) : ‖1 - (r : ℂ) ^ (j + 1)‖ ≤ ‖1 - q ^ (j + 1)‖ := by
    have h := pow_le_one₀ hr₀ hr.le (n := j + 1)
    rw [← Complex.ofReal_one, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr h)]
    have H := norm_sub_norm_le (1 : ℂ) (q ^ (j + 1))
    simpa only [Complex.ofReal_one, norm_one, norm_pow, hqr] using H
  have h2 : ‖qPochhammer (r : ℂ) r a‖ ≤ ‖qPochhammer q q a‖ := by
    simp_rw [qPochhammer_self_eq_prod, norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => h1 j)
  have h3 : 0 < ‖qPochhammer (r : ℂ) r a‖ := by
    rw [norm_pos_iff, qPochhammer_self_eq_prod]
    apply Finset.prod_ne_zero_iff.2
    intro j _
    exact power_factor_ne_zero (hrq.trans_lt hr) j
  simp only [outerTailTerm, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, hqr, hrq]
  exact div_le_div_of_nonneg_left (pow_nonneg hr₀ _) h3 h2

private theorem generating_norm_le {q : ℂ} {r : ℝ} (hr : ‖q‖ = r) (hr₀ : 0 ≤ r)
    (hr₁ : r < 1) : ‖twoColourGenerating q‖ ≤
      ∑' m, ‖(twoColourPartitionCount m : ℂ) * (r : ℂ) ^ m‖ := by
  have hq : ‖q‖ < 1 := hr ▸ hr₁
  have hn (m : ℕ) : ‖(twoColourPartitionCount m : ℂ) * q ^ m‖ =
      ‖(twoColourPartitionCount m : ℂ) * (r : ℂ) ^ m‖ := by
    simp only [norm_mul, norm_pow, hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr₀]
  rw [twoColourGenerating_eq_tsum hq]
  simpa only [hn] using norm_tsum_le_tsum_norm (summable_norm_twoColourGenerating hq)

set_option maxHeartbeats 800000 in
theorem restrictedPair_coefficient_eq_outerExpansion (d N : ℕ) :
    coeff N (restrictedPairSeries d) =
      ∑ ab ∈ (range (N + 1)) ×ˢ (range (N + 1)), outerShiftedCoeff d ab.1 ab.2 N := by
  let ζ (v : ℝ) : ℂ := 1 + (v : ℂ) * Complex.I
  let q (v : ℝ) : ℂ := Complex.exp (-ζ v)
  let r : ℝ := Real.exp (-1)
  have hr₀ : 0 < r := Real.exp_pos _
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hnq (v : ℝ) : ‖q v‖ = r := by simp [q, ζ, r, Complex.norm_exp, Complex.mul_re]
  have hq (v : ℝ) : ‖q v‖ < 1 := (hnq v).trans_lt hr
  have hqr : ‖(r : ℂ)‖ < 1 := by simpa [abs_of_pos hr₀] using hr
  let K := ∑' m, ‖(twoColourPartitionCount m : ℂ) * (r : ℂ) ^ m‖
  have hK : 0 ≤ K := tsum_nonneg (fun _ => norm_nonneg _)
  let F (ab : ℕ × ℕ) (v : ℝ) : ℂ :=
    Complex.exp ((N : ℂ) * ζ v) *
      (twoColourGenerating (q v) * outerTailTerm (q v) d ab.1 * outerTailTerm (q v) d ab.2)
  let bnd (ab : ℕ × ℕ) : ℝ :=
    (Real.exp N * K) * (‖outerTailTerm (r : ℂ) d ab.1‖ * ‖outerTailTerm (r : ℂ) d ab.2‖)
  have htail := summable_norm_outerTailTerm hqr d
  have hbnd : Summable bnd :=
    (htail.mul_of_nonneg htail (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left _
  have hbound (ab : ℕ × ℕ) (v : ℝ) : ‖F ab v‖ ≤ bnd ab := by
    simp only [F, bnd, norm_mul, Complex.norm_exp]
    rw [show ((N : ℂ) * ζ v).re = N by simp [ζ, Complex.mul_re]]
    have hm₁ := tailTerm_norm_le hr₀.le hr (hnq v) d ab.1
    have hm₂ := tailTerm_norm_le hr₀.le hr (hnq v) d ab.2
    have hm₃ := generating_norm_le (hnq v) hr₀.le hr
    rw [mul_assoc (‖twoColourGenerating (q v)‖), ← mul_assoc (Real.exp N)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hm₃ (Real.exp_nonneg _))
      (mul_le_mul hm₁ hm₂ (norm_nonneg _) (norm_nonneg _)) (by positivity) (by positivity)
  have hcont_q : Continuous q := by unfold q ζ; fun_prop
  have hconT (a : ℕ) : Continuous (fun v => outerTailTerm (q v) d a) := by
    have hc₁ : Continuous (fun v => qPochhammer (q v) (q v) a) := by
      simp_rw [qPochhammer_self_eq_prod]
      exact continuous_finsetProd _ (fun j _ => continuous_const.sub (hcont_q.pow _))
    have hc₀ : ∀ v, qPochhammer (q v) (q v) a ≠ 0 := by
      intro v
      rw [qPochhammer_self_eq_prod]
      exact Finset.prod_ne_zero_iff.2 (fun j _ => power_factor_ne_zero (hq v) j)
    exact ((continuous_const.mul (hcont_q.pow _)).mul (hc₁.inv₀ hc₀))
  have hconG : Continuous (fun v => twoColourGenerating (q v)) := by
    change Continuous (fun v => twoColourGenerating (Complex.exp (-ζ v)))
    simp_rw [twoColourGenerating_exp_neg]
    exact (((continuous_eulerProduct_vertical (by norm_num : 0 < (1 : ℝ))).inv₀
      (fun v => eulerProduct_ne_zero_right (by simp))).pow 2)
  have hcont (ab : ℕ × ℕ) : Continuous (F ab) := by
    unfold F ζ
    exact (by fun_prop : Continuous (fun v : ℝ => Complex.exp ((N : ℂ) *
      (1 + (v : ℂ) * Complex.I)))).mul ((hconG.mul (hconT _)).mul (hconT _))
  have hsumv (v : ℝ) : Summable (fun ab => ‖F ab v‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ab => hbound ab v) hbnd
  have hInt := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -Real.pi) (b := Real.pi) (μ := volume) (F := F)
    (f := fun v => ∑' ab, F ab v) (fun ab _ => bnd ab)
    (fun ab => (hcont ab).aestronglyMeasurable)
    (fun ab => ae_of_all _ fun v _ => hbound ab v)
    (ae_of_all _ fun _ _ => hbnd) intervalIntegrable_const
    (ae_of_all _ fun v _ => (hsumv v).of_norm.hasSum)
  have H (v : ℝ) : (∑' ab, F ab v) =
      Complex.exp ((N : ℂ) * ζ v) * ((qPochhammer (q v) (q v) d)⁻¹ ^ 2) := by
    unfold F
    simp_rw [mul_assoc (twoColourGenerating (q v))]
    rw [tsum_mul_left, tsum_mul_left, ← eulerTail_sq_eq_doubleSum (hq v)]
    change Complex.exp ((N : ℂ) * ζ v) *
      (twoColourGenerating (q v) * outerEulerTail (q v) d ^ 2) = _
    rw [twoColourGenerating_mul_eulerTail_sq (hq v)]
  have hq0 : ‖Complex.exp (-(1 : ℂ))‖ < 1 := by
    have he : q 0 = Complex.exp (-(1 : ℂ)) := by simp [q, ζ]
    exact he ▸ hq 0
  have hcoef : ((coeff N (restrictedPairSeries d) : ℤ) : ℂ) =
      (2 * Real.pi : ℂ)⁻¹ * ∫ v in -Real.pi..Real.pi, ∑' ab, F ab v := by
    have hc := angular_coefficient_of_summable
      (fun m => ((coeff m (restrictedPairSeries d) : ℤ) : ℂ))
      N (1 : ℝ) (by simpa only [Complex.ofReal_one] using
        summable_norm_coeff_restrictedPairSeries hq0 d)
    refine hc.trans ?_
    congr 1
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    change Complex.exp ((N : ℂ) * ζ v) *
      (∑' m : ℕ, ((coeff m (restrictedPairSeries d) : ℤ) : ℂ) * q v ^ m) =
        ∑' ab, F ab v
    rw [H, (hasSum_coeff_restrictedPairSeries (hq v) d).tsum_eq]
  have hcoefAB (ab : ℕ × ℕ) : ((outerShiftedCoeff d ab.1 ab.2 N : ℤ) : ℂ) =
      (2 * Real.pi : ℂ)⁻¹ * ∫ v in -Real.pi..Real.pi, F ab v := by
    have hc := angular_coefficient_of_summable
      (fun m => ((outerShiftedCoeff d ab.1 ab.2 m : ℤ) : ℂ))
      N (1 : ℝ) (by simpa only [Complex.ofReal_one] using
        (hasSum_shiftedPairSeries hq0 d ab.1 ab.2).2)
    refine hc.trans ?_
    congr 1
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    change Complex.exp ((N : ℂ) * ζ v) *
      (∑' m : ℕ, ((outerShiftedCoeff d ab.1 ab.2 m : ℤ) : ℂ) * q v ^ m) =
        F ab v
    rw [(hasSum_shiftedPairSeries (hq v) d ab.1 ab.2).1.tsum_eq]
  have htotal := hInt.tsum_eq
  apply (Int.cast_injective (α := ℂ))
  rw [Int.cast_sum, hcoef, ← htotal, ← tsum_mul_left]
  simp_rw [← hcoefAB]
  rw [tsum_eq_sum (s := (range (N + 1)) ×ˢ (range (N + 1)))]
  intro ab hab
  have hsmall (a : ℕ) (ha : N < a) : N < outerTailPower d a := by
    unfold outerTailPower
    rw [show (a + 1).choose 2 = a.choose 1 + a.choose 2 from Nat.choose_succ_succ a 1,
      Nat.choose_one_right]
    omega
  have hshift : ¬ outerTailPower d ab.1 + outerTailPower d ab.2 ≤ N := by
    by_contra hs
    apply hab
    rw [mem_product, mem_range, mem_range]
    constructor <;> by_contra! hbad
    · have hp := hsmall ab.1 (by omega)
      omega
    · have hp := hsmall ab.2 (by omega)
      omega
  simp [outerShiftedCoeff, hshift]

end DurfeeCCS.Step10
