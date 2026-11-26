module

public import DurfeeCCS.Step10.OuterErrorHigh
import Mathlib.Tactic

/-! Summation of the explicit transform estimates in Proposition 4.1. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Complex DurfeeCCS.Step07

/-- The finite low-mode approximation to the explicit transform. -/
def outerMainMode (y h v : ℝ) : ℂ := outerEndpointMain y (outerRho h v)

private theorem low_transform_endpoints {y h v : ℝ} (hy : 0 < y) (hh : 0 < h) :
    kernelTransformIntegralFormula y (outerZeta h v) =
      outerEndpointUpper y (outerRho h v) - outerEndpointLower y (outerZeta h v) := by
  let ζ := outerZeta h v
  let ρ := outerRho h v
  let A : ℝ := 4 * π ^ 2 / 3
  have hζ : 0 < ζ.re := by simpa [ζ]
  have hq : ρ ^ 2 = ζ ^ 2 + (A : ℂ) := outerRhoAt_sq h v A
  have he := kernelTransformIntegral_endpoints hy.ne' hζ
  change kernelTransformIntegralFormula y ζ + (π : ℂ) ^ 3 * Complex.sinh ((y : ℂ) * ζ) /
      (18 * ζ) = (1 / (8 * (π : ℂ))) *
        (kernelEndpoint y (ζ ^ 2 + (A : ℂ)) ρ - kernelEndpoint y (ζ ^ 2 + (A : ℂ)) ζ) at he
  unfold kernelEndpoint at he
  rw [← hq, sub_self, zero_mul, zero_div, zero_add, hq] at he
  have hπc : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hζc : ζ ≠ 0 := by
    intro hz
    simp [hz] at hζ
  change kernelTransformIntegralFormula y ζ =
    outerEndpointUpper y ρ - outerEndpointLower y ζ
  unfold outerEndpointUpper outerEndpointLower
  dsimp [A] at he
  push_cast at he
  field_simp [hπc, hyc, hζc] at he ⊢
  linear_combination he

/-- The pointwise low-frequency estimate on page 41 for the explicit integral formula. -/
theorem outerLow_transform_error {y h v : ℝ} (hy : 72 < y) (hh : 8.76 < h)
    (hscale : h / y ≤ 0.240) (hyh : 1 ≤ y * h) (hv : |v| ≤ h) :
    ‖kernelTransformIntegralFormula y (outerZeta h v) - outerMainMode y h v‖ ≤
      ‖outerMainMode y h v‖ * (1 / (y * h) + 2 * Real.exp (-2 * (y * h))) +
        2 / h * Real.exp (y * h) := by
  have hh₀ : 0 < h := by linarith
  have hy₀ : 0 < y := by linarith
  have hv₂ : v ^ 2 ≤ h ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hv 2
  have hζlo : h ≤ ‖outerZeta h v‖ := by
    simpa only [outerZeta_re] using Complex.re_le_norm (outerZeta h v)
  have hζhi : ‖outerZeta h v‖ ≤ Real.sqrt 2 * h := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    rw [normSq_outerZeta, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  exact outerEndpoint_error hy hh₀ hscale (outerZeta_re h v) (outerRho_re_gt hh₀).le
    hyh hζlo hζhi (low_transform_endpoints hy₀ hh₀)

/-- The high-frequency tail bound on page 42 for the explicit integral formula. -/
theorem outerHigh_relative_sum {y h : ℝ} (hy : 72 ≤ y) (hh : 8.76 < h) :
    let T (p : ℤ) := if h < |outerFrequency p| then
      ‖kernelTransformIntegralFormula y (outerZeta h (outerFrequency p))‖ /
        outerTransformAmplitude y h else 0
    Summable T ∧ (∑' p, T p) <
      29 * y ^ 3 / h ^ 2 *
        Real.exp (-(4 * π ^ 2 * y / (3 * h)) * max 0.152 (1 / 4 - 8.4 / h ^ 2)) := by
  dsimp only
  let T (p : ℤ) := if h < |outerFrequency p| then
      ‖kernelTransformIntegralFormula y (outerZeta h (outerFrequency p))‖ /
        outerTransformAmplitude y h else 0
  let Q (p : ℤ) := if h < |outerFrequency p| then
    1 / (h ^ 2 + outerFrequency p ^ 2) else 0
  let A : ℝ := 4 * π ^ 2 / 3
  let ε := Real.exp (-(4 * π ^ 2 * y / (3 * h)) * max 0.152 (1 / 4 - 8.4 / h ^ 2))
  let K := (0.55 * π ^ 2 * A ^ 2 / 18) * y ^ 3 / h * ε
  have hy₀ : 0 < y := by linarith
  have hh₀ : 0 < h := by linarith
  have hApos := outerTransformAmplitude_pos hy₀ hh₀
  have hK₀ : 0 < K := by dsimp [K,A,ε]; positivity
  have hQ := outerHighReciprocal_sum hh₀
  change Summable Q ∧ ∑' p, Q p ≤ _ at hQ
  have hT₀ (p : ℤ) : 0 ≤ T p := by dsimp only [T]; split_ifs <;> positivity
  have hpoint (p : ℤ) : T p ≤ K * Q p := by
    by_cases hp : h < |outerFrequency p|
    · rw [show T p = _ from ite_eq_left hp, show Q p = _ from ite_eq_left hp]
      apply (div_le_iff₀ hApos).2
      apply (outerHigh_transform_point hy hh hp).trans_eq
      unfold outerTransformAmplitude outerHighGap
      dsimp [K, ε, A, outerBesselScale]
      rw [mul_sub, Real.exp_sub,
        show y * (4 * π ^ 2 / 3 / h * max (0.152 : ℝ) (1 / 4 - 8.4 / h ^ 2)) =
          4 * π ^ 2 * y / (3 * h) * max (0.152 : ℝ) (1 / 4 - 8.4 / h ^ 2) by ring]
      rw [neg_mul, Real.exp_neg]
      field_simp
      ring
    · simp [T,Q,hp]
  have hQ' := hQ.1.mul_left K
  have hT := hQ'.of_nonneg_of_le hT₀ hpoint
  refine ⟨hT, ?_⟩
  calc
    _ ≤ ∑' p, K * Q p := hT.tsum_le_tsum hpoint hQ'
    _ ≤ K * (2 / h ^ 2 + 1 / (π * h)) := by
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left hQ.2 hK₀.le
    _ = (0.55 * π * A ^ 2 / 18 * (1 + 2 * π / h)) * (y ^ 3 / h ^ 2 * ε) := by
      dsimp [K]
      field_simp
      ring
    _ < _ := by
      have hπ : π ≤ 3.141593 := pi_lt_d6.le
      have hA : A ≤ 13.16 := by
        calc
          _ ≤ 4 * (3.141593 : ℝ) ^ 2 / 3 := by dsimp [A]; gcongr
          _ ≤ _ := by norm_num
      have hB : 0.55 * π * A ^ 2 / 18 * (1 + 2 * π / h) < 29 := by
        calc
          _ ≤ (0.55 * 3.141593 * (13.16 : ℝ) ^ 2 / 18) * (1 + 2 * 3.141593 / 8.76) := by
            dsimp [A] at ⊢ hA
            gcongr
          _ < _ := by norm_num
      change _ < 29 * y ^ 3 / h ^ 2 * ε
      rw [show 29 * y ^ 3 / h ^ 2 * ε = 29 * (y ^ 3 / h ^ 2 * ε) by ring]
      exact mul_lt_mul_of_pos_right hB (by positivity)

private theorem outerLow_nonleading_sum {y₀ y h c : ℝ} (hc : 9/10 ≤ c) (hy₀ : 80 ≤ y₀)
    (hy : c * y₀ ≤ y) (hh : 8.76 < h) (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    let V (p : ℤ) := if |outerFrequency p| ≤ h then
      if p = 0 ∨ p = -1 then 0 else ‖outerMainMode y h (outerFrequency p)‖ /
        outerTransformAmplitude y h
      else 0
    Summable V ∧ (∑' p, V p) ≤ outerSmallModeBound c := by
  dsimp only
  let A := outerTransformAmplitude y h
  let j := outerFrequencyCutoff h
  let M (p : ℤ) := ‖outerMainMode y h (outerFrequency p)‖ / A
  let W (p : ℤ) := if p = 0 ∨ p = -1 then 0 else M p
  let Q (m : ℕ) := if outerPositiveFrequency (m + 1) ≤ h then
    M (m + 1 : ℤ) + M (-(m + 2 : ℤ)) else 0
  have hy₀₀ : 0 < y₀ := by linarith
  have hy' : 0 < y := (mul_pos (by linarith) hy₀₀).trans_le hy
  have hh₀ : 0 < h := by linarith
  have hA : 0 < A := outerTransformAmplitude_pos hy' hh₀
  have hQ₀ (m : ℕ) : 0 ≤ Q m := by dsimp only [Q,M]; split_ifs <;> positivity
  have hpoint (m : ℕ) : Q m ≤
      1.47 * Real.exp (-(26 * π ^ 4 * y / (25 * h ^ 3)) * ((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
    dsimp only [Q]
    split_ifs with H
    · have h₁ : outerFrequency (m + 1 : ℤ) = outerPositiveFrequency (m + 1) := by
        rw [outerPositiveFrequency, Nat.cast_add, Nat.cast_one]
      have h₂ : outerFrequency (-(m + 2 : ℤ)) = -outerPositiveFrequency (m + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using outerFrequency_neg_nat (m + 1)
      dsimp [M]
      rw [h₁, h₂, ← add_div]
      exact outerLow_nonleading_pair hy' m H
    · positivity
  obtain ⟨hs, hSum⟩ := outerSmallModeSeries_le (show 0 < c by linarith)
    (outerSmallModeExponent_le hc hy₀ hy hh₀ hcap) hQ₀ hpoint
  have hLow := outerLow_frequency_sum h W
  refine ⟨hLow.1, hLow.2.le.trans ?_⟩
  have hj : 0 < j := (outerPositiveFrequency_le_iff h 0).1 (by
    rw [outerPositiveFrequency_zero]
    linarith [pi_lt_d6])
  change (∑ m ∈ Finset.range j, (W m + W (-(m + 1 : ℤ)))) ≤ _
  cases hindex : j with
  | zero => omega
  | succ N =>
    rw [Finset.sum_range_succ']
    have hident : (∑ m ∈ Finset.range N, (W ((m + 1 : ℕ) : ℤ) +
        W (-(((m+1 : ℕ) : ℤ) + 1)))) = ∑ m ∈ Finset.range N, Q m := by
      apply Finset.sum_congr rfl
      intro m hm
      have hv : outerPositiveFrequency (m + 1) ≤ h :=
        (outerPositiveFrequency_le_iff h _).2 (by
          have := Finset.mem_range.mp hm
          change j = N + 1 at hindex
          omega)
      have hmc : (0 : ℤ) ≤ m := Nat.cast_nonneg _
      have w₁ : ¬((m : ℤ) + 1 = 0 ∨ (m : ℤ) + 1 = -1) := by omega
      have w₂ : ¬(-((m : ℤ) + 2) = 0 ∨ -((m : ℤ) + 2) = -1) := by omega
      rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by simp, show -((m : ℤ) + 1 + 1) = -((m : ℤ) + 2) by ring]
      simp only [W, ite_eq_right w₁, ite_eq_right w₂, Q, ite_eq_left hv]
    have hzero : W 0 + W (-1) = 0 := by simp [W]
    change (∑ m ∈ Finset.range N, (W ((m + 1 : ℕ) : ℤ) +
      W (-(((m + 1 : ℕ) : ℤ) + 1)))) + (W 0 + W (-1)) ≤ _
    rw [hident,hzero,add_zero]
    exact (hs.sum_le_tsum _ (fun m _ => hQ₀ m)).trans hSum

private theorem outerLow_lower_relative {y h : ℝ} (hy : 0 < y) (hh : 8.76 < h) :
    2 * (outerFrequencyCutoff h : ℝ) *
        ((2 / h * Real.exp (y * h)) / outerTransformAmplitude y h) ≤
      14 * y ^ 2 / h * Real.exp (-17 * π ^ 2 * y / (30 * h)) := by
  have hh₀ : 0 < h := by linarith
  have hcount := outerFrequencyCutoff_count hh₀.le
  have hA := outerTransformAmplitude_pos hy hh₀
  have hE := Real.exp_le_exp.mpr
    (show y * h - y * (outerRho h π).re ≤ -17 * π ^ 2 * y / (30 * h) by
      have H := mul_le_mul_of_nonneg_left (outerRho_re_pi_gap hh).le hy.le
      linear_combination H)
  have hπ : π ≤ 3.142 := pi_lt_d6.le.trans (by norm_num)
  have hfact : 8 * (1 + π / h) ≤ 14 := by
    have hdiv : π / h ≤ (3.142 : ℝ) / 8.76 := by
      exact div_le_div₀ (by norm_num) hπ (by norm_num) hh.le
    linarith
  calc
    _ ≤ (h / π + 1) * ((2 / h * Real.exp (y * h)) / outerTransformAmplitude y h) := by gcongr
    _ = (8 * (1 + π / h)) * (y ^ 2 / h) *
          Real.exp (y * h - y * (outerRho h π).re) := by
      unfold outerTransformAmplitude
      rw [Real.exp_sub]
      field_simp
      ring
    _ ≤ 14 * (y ^ 2 / h) * Real.exp (-17 * π ^ 2 * y / (30 * h)) := by gcongr
    _ = _ := by ring

/-- The pointwise low-mode errors and the three numerical majorants on page 43. -/
theorem outerLow_error_sums {y₀ y h c : ℝ} (hc : 9/10 ≤ c) (hy₀ : 80 < y₀)
    (hy : c * y₀ ≤ y) (hh : 8.76 < h) (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    let V (p : ℤ) := if |outerFrequency p| ≤ h then
      ‖kernelTransformIntegralFormula y (outerZeta h (outerFrequency p)) -
        outerMainMode y h (outerFrequency p)‖ / outerTransformAmplitude y h else 0
    Summable V ∧ (∑' p, V p) ≤ outerLowerBound c y₀ + outerUpperBound c := by
  dsimp only
  let A := outerTransformAmplitude y h
  let C := 2 / h * Real.exp (y * h) / A
  let f := 1 / (y * h) + 2 * Real.exp (-2 * (y * h))
  let M (p : ℤ) := ‖outerMainMode y h (outerFrequency p)‖ / A
  let R (p : ℤ) := ‖kernelTransformIntegralFormula y (outerZeta h (outerFrequency p)) -
      outerMainMode y h (outerFrequency p)‖ / A
  let lowM (p : ℤ) := if |outerFrequency p| ≤ h then M p else 0
  let extra (p : ℤ) := if |outerFrequency p| ≤ h then C else 0
  let lowR (p : ℤ) := if |outerFrequency p| ≤ h then R p else 0
  let W (p : ℤ) := if p = 0 ∨ p = -1 then M p else 0
  let non (p : ℤ) := if |outerFrequency p| ≤ h then
    if p = 0 ∨ p = -1 then 0 else M p else 0
  have hh₀ : 0 < h := by linarith
  have hy₀₀ : 0 < y₀ := by linarith
  have hy' : 72 < y := by nlinarith [mul_nonneg (show 0 ≤ c - 9/10 by linarith) hy₀₀.le]
  have hypos : 0 < y := by linarith
  have hA : 0 < A := outerTransformAmplitude_pos hypos hh₀
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : 0 ≤ f := by dsimp [f]; positivity
  have h₉ : (9 / 10 : ℝ) * y₀ ≤ y := (mul_le_mul_of_nonneg_right hc hy₀₀.le).trans hy
  have ⟨_, hscale, hyh⟩ := outerError_scale hy₀.le h₉ hh hcap
  have hM := outerLow_frequency_sum h M
  have hCsum := outerLow_frequency_sum h (fun _ : ℤ => C)
  have hR := outerLow_frequency_sum h R
  have hL12 : |outerFrequency (0 : ℤ)| ≤ h ∧ |outerFrequency (-1)| ≤ h := by
    have H : π ≤ h := by linarith [pi_lt_d6]
    constructor
    · simpa [outerFrequency, abs_of_pos pi_pos] using H
    · have he : outerFrequency (-1) = -π := by norm_num [outerFrequency]
      rwa [he, abs_neg, abs_of_pos pi_pos]
  have hW : Summable W := by
    apply summable_of_ne_finset_zero (s := ({0, -1} : Finset ℤ))
    intro p hp
    have hp' : ¬(p = 0 ∨ p = -1) := by simpa using hp
    exact ite_eq_right hp'
  have hWsum : (∑' p, W p) = M 0 + M (-1) := by
    rw [tsum_eq_sum (s := ({0, -1} : Finset ℤ)) (fun p hp => by
      have hp' : ¬(p = 0 ∨ p = -1) := by simpa using hp
      exact ite_eq_right hp')]
    norm_num [W, Finset.sum_insert]
  have hWb : (∑' p, W p) ≤ 1.142 := by
    rw [hWsum]
    dsimp only [M]
    rw [← add_div]
    have hz : outerFrequency 0 = π := by simp [outerFrequency]
    have ho : outerFrequency (-1) = -π := by norm_num [outerFrequency]
    rw [hz, ho]
    exact (outerLow_leading_pair hypos hh).le
  have hn := outerLow_nonleading_sum hc hy₀.le hy hh hcap
  have hsplit (p : ℤ) : lowM p = W p + non p := by
    by_cases hP : p = 0 ∨ p = -1
    · have hl : |outerFrequency p| ≤ h := hP.elim (fun e => e ▸ hL12.1) (fun e => e ▸ hL12.2)
      simp [lowM, W, non, hl, hP]
    · simp [lowM, W, non, hP]
  have hMbound : (∑' p, lowM p) ≤ 1.142 + outerSmallModeBound c := by
    simp_rw [hsplit]
    rw [hW.tsum_add hn.1]
    exact add_le_add hWb hn.2
  have hM₀ : 0 ≤ ∑' p, lowM p := tsum_nonneg (fun p => by dsimp [lowM, M]; split_ifs <;> positivity)
  have hlow (p : ℤ) : lowR p ≤ f * lowM p + extra p := by
    by_cases hL : |outerFrequency p| ≤ h
    · simp only [lowR, lowM, extra, ite_eq_left hL, R, M, C]
      have H := div_le_div_of_nonneg_right
        (outerLow_transform_error hy' hh hscale.le hyh hL) hA.le
      rw [add_div] at H
      exact H.trans_eq (by ring)
    · simp [lowR, lowM, extra, hL]
  refine ⟨hR.1, ?_⟩
  calc
    _ ≤ (∑' p, (f * lowM p + extra p)) :=
      hR.1.tsum_le_tsum hlow ((hM.1.mul_left f).add hCsum.1)
    _ = f * (∑' p, lowM p) + (∑' p, extra p) := by
      rw [(hM.1.mul_left f).tsum_add hCsum.1, tsum_mul_left]
    _ ≤ outerLowerBound c y₀ + outerUpperBound c := by
      have hCeq : (∑' p, extra p) = 2 * (outerFrequencyCutoff h : ℝ) * C := by
        rw [hCsum.2]
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      rw [hCeq, add_comm]
      exact add_le_add
        ((outerLow_lower_relative hypos hh).trans (outerLowerMajorant_le hc hy₀.le hy hh₀ hcap))
        (by rw [mul_comm]; exact outerUpperMajorant_le hc hy₀.le hy hh.le hM₀ hMbound)

/-- The explicit integral in (69), indexed by the manuscript's odd frequency lattice. -/
def outerIntegralMode (y h : ℝ) (p : ℤ) : ℂ :=
  kernelTransformIntegralFormula y (outerZeta h (outerFrequency p))

/-- The leading pair, supported exactly at π and −π. -/
def outerIntegralLead (y h : ℝ) (p : ℤ) : ℂ :=
  if p = 0 ∨ p = -1 then outerMainMode y h (outerFrequency p) else 0

private theorem outerIntegralLead_summable (y h : ℝ) :
    Summable (outerIntegralLead y h) := by
  apply summable_of_ne_finset_zero (s := ({0, -1} : Finset ℤ))
  intro p hp
  have hp' : ¬(p = 0 ∨ p = -1) := by simpa using hp
  exact ite_eq_right hp'

private theorem outerIntegralLead_norm (y h : ℝ) :
    Summable (fun p => ‖outerIntegralLead y h p‖ / outerTransformAmplitude y h) ∧
    (∑' p, ‖outerIntegralLead y h p‖ / outerTransformAmplitude y h) =
      (‖outerMainMode y h π‖ + ‖outerMainMode y h (-π)‖) / outerTransformAmplitude y h := by
  let M (p : ℤ) := ‖outerIntegralLead y h p‖ / outerTransformAmplitude y h
  let F : Finset ℤ := {0, -1}
  have hz (p : ℤ) (hp : p ∉ F) : M p = 0 := by
    have hp' : ¬(p = 0 ∨ p = -1) := by simpa [F] using hp
    simp only [M, outerIntegralLead, ite_eq_right hp', norm_zero, zero_div]
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  norm_num [M, F, outerIntegralLead, outerFrequency, add_div, Finset.sum_insert]

private theorem outerIntegralLead_sum {y h : ℝ} (hh : 0 < h) :
    (∑' p, outerIntegralLead y h p) = ((2 * (outerMainMode y h π).re : ℝ) : ℂ) := by
  rw [tsum_eq_sum (s := ({0, -1} : Finset ℤ)) (fun p hp => by
    have hp' : ¬(p = 0 ∨ p = -1) := by simpa using hp
    exact ite_eq_right hp')]
  have hz : outerFrequency 0 = π := by simp [outerFrequency]
  have ho : outerFrequency (-1) = -π := by norm_num [outerFrequency]
  norm_num [outerIntegralLead, Finset.sum_insert, hz, ho]
  unfold outerMainMode
  rw [outerRho_conj hh, outerEndpointMain_conj]
  apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, two_mul]

private theorem outerIntegral_residual {y₀ y h c : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 < y₀)
    (hy : c * y₀ ≤ y) (hh : 8.76 < h) (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    let R (p : ℤ) := ‖outerIntegralMode y h p - outerIntegralLead y h p‖ / outerTransformAmplitude y h
    Summable R ∧ (∑' p, R p) ≤
      (outerSmallModeBound c + max (outerHighLowBound c y₀) (outerHighLargeBound c y₀)) +
      (outerLowerBound c y₀ + outerUpperBound c) := by
  dsimp only
  let A := outerTransformAmplitude y h
  let T (p : ℤ) := outerIntegralMode y h p
  let P (p : ℤ) := outerIntegralLead y h p
  let M (p : ℤ) := outerMainMode y h (outerFrequency p)
  let Q (p : ℤ) := if h < |outerFrequency p| then ‖T p‖ / A else 0
  let W (p : ℤ) := if |outerFrequency p| ≤ h then ‖T p - M p‖ / A else 0
  let S (p : ℤ) := if |outerFrequency p| ≤ h then
    if p = 0 ∨ p = -1 then 0 else ‖M p‖ / A else 0
  let R (p : ℤ) := ‖T p - P p‖ / A
  have hy₀₀ : 0 < y₀ := by linarith
  have hy' : 72 ≤ y := by nlinarith [mul_nonneg (show 0 ≤ c - 9/10 by linarith) hy₀₀.le]
  have hypos : 0 < y := by linarith
  have hh₀ : 0 < h := by linarith
  have hA := outerTransformAmplitude_pos hypos hh₀
  have hW := outerLow_error_sums hc hy₀ hy hh hcap
  have hS := outerLow_nonleading_sum hc hy₀.le hy hh hcap
  have hQ := outerHigh_relative_sum hy' hh
  have hQb : (∑' p, Q p) ≤ max (outerHighLowBound c y₀) (outerHighLargeBound c y₀) := by
    by_cases h11 : h ≤ 11
    · apply hQ.2.le.trans
      apply le_trans _ ((outerHighLowMajorant_le hc hy₀.le hy hh₀ h11).trans (le_max_left _ _))
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
      have H := mul_le_mul_of_nonpos_left
        (le_max_left (0.152 : ℝ) (1 / 4 - 8.4 / h ^ 2))
        (neg_nonpos.mpr (show 0 ≤ 4 * π ^ 2 * y / (3 * h) by positivity))
      simpa only [show -(4 * π ^ 2 * y / (3 * h)) * (0.152 : ℝ) =
        -0.152 * 4 * π ^ 2 * y / (3 * h) by ring] using H
    · apply hQ.2.le.trans
      apply le_trans _ ((outerHighLargeMajorant_le hc hy₀.le hy (le_of_not_ge h11) hcap).trans
        (le_max_right _ _))
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
      exact mul_le_mul_of_nonpos_left (le_max_right _ _) (neg_nonpos.mpr (by positivity))
  have hR₀ (p : ℤ) : 0 ≤ R p := div_nonneg (norm_nonneg _) hA.le
  have hdom (p : ℤ) : R p ≤ S p + Q p + W p := by
    have hprincipal : p = 0 ∨ p = -1 → |outerFrequency p| ≤ h := by
      rintro (rfl | rfl)
      · simpa [outerFrequency, abs_of_pos pi_pos] using (show π ≤ h by linarith [pi_lt_d6])
      · have he : outerFrequency (-1) = -π := by norm_num [outerFrequency]
        rw [he, abs_neg, abs_of_pos pi_pos]
        linarith [pi_lt_d6]
    by_cases hp : p = 0 ∨ p = -1
    · have hl := hprincipal hp
      simp [R, P, outerIntegralLead, hp, S, Q, W, hl, not_lt.mpr hl, M]
    · by_cases hl : |outerFrequency p| ≤ h
      · simp only [R,P,outerIntegralLead,ite_eq_right hp,sub_zero,S,ite_eq_left hl,Q,
          ite_eq_right (not_lt.mpr hl),add_zero,W]
        rw [← add_div, add_comm ‖M p‖]
        apply div_le_div_of_nonneg_right _ hA.le
        calc
          ‖T p‖ = ‖(T p - M p) + M p‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      · have hH : h < |outerFrequency p| := lt_of_not_ge hl
        simp [R, P, outerIntegralLead, hp, S, Q, W, hl, hH]
  have hs : Summable (fun p => S p + Q p + W p) := (hS.1.add hQ.1).add hW.1
  have hR := hs.of_nonneg_of_le hR₀ hdom
  refine ⟨hR, ?_⟩
  calc
    _ ≤ (∑' p, (S p + Q p + W p)) := hR.tsum_le_tsum hdom hs
    _ ≤ _ := by
      have hSs : Summable S := hS.1
      have hQs : Summable Q := hQ.1
      have hWs : Summable W := hW.1
      rw [(hSs.add hQs).tsum_add hWs, hSs.tsum_add hQs]
      exact add_le_add (add_le_add hS.2 hQb) hW.2

private theorem outerIntegral_abs_le {y₀ y h c : ℝ} (hc : 9 / 10 ≤ c) (hy₀ : 80 < y₀)
    (hy : c * y₀ ≤ y) (hh : 8.76 < h) (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    let A := outerTransformAmplitude y h
    let T := outerIntegralMode y h
    let P := outerIntegralLead y h
    let b := outerSmallModeBound c + max (outerHighLowBound c y₀) (outerHighLargeBound c y₀) +
      (outerLowerBound c y₀ + outerUpperBound c)
    Summable (fun p => ‖T p‖) ∧
      (∑' p, ‖T p‖) ≤ (b + 1.142) * A ∧
      ‖(∑' p, T p) - (∑' p, P p)‖ ≤ b * A := by
  dsimp only
  let A := outerTransformAmplitude y h
  let T := outerIntegralMode y h
  let P := outerIntegralLead y h
  let b := outerSmallModeBound c + max (outerHighLowBound c y₀) (outerHighLargeBound c y₀) +
      (outerLowerBound c y₀ + outerUpperBound c)
  let R (p : ℤ) := ‖T p - P p‖ / A
  let L (p : ℤ) := ‖P p‖ / A
  let N (p : ℤ) := ‖T p‖ / A
  have hy₀₀ : 0 < y₀ := by linarith
  have hypos : 0 < y := (mul_pos (by linarith) hy₀₀).trans_le hy
  have hh₀ : 0 < h := by linarith
  have hA : 0 < A := outerTransformAmplitude_pos hypos hh₀
  have hR := outerIntegral_residual hc hy₀ hy hh hcap
  have hL := outerIntegralLead_norm y h
  have hLb : (∑' p, L p) ≤ 1.142 := hL.2.le.trans (outerLow_leading_pair hypos hh).le
  have hdom (p : ℤ) : N p ≤ R p + L p := by
    dsimp [N, R, L]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hA.le
    calc
      ‖T p‖ = ‖(T p - P p) + P p‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hN : Summable N := (hR.1.add hL.1).of_nonneg_of_le (fun p => div_nonneg (norm_nonneg _) hA.le) hdom
  have hNs : (∑' p, N p) ≤ b + 1.142 :=
    (hN.tsum_le_tsum hdom (hR.1.add hL.1)).trans (by
      rw [hR.1.tsum_add hL.1]; exact add_le_add hR.2 hLb)
  have hTN : Summable (fun p => ‖T p‖) := (hN.mul_right A).congr (fun p => div_mul_cancel₀ _ hA.ne')
  have hRN : Summable (fun p => ‖T p - P p‖) :=
    (hR.1.mul_right A).congr (fun p => div_mul_cancel₀ _ hA.ne')
  have hex₁ (p : ℤ) : ‖T p‖ = N p * A := (div_mul_cancel₀ _ hA.ne').symm
  have hex₂ (p : ℤ) : ‖T p - P p‖ = R p * A := (div_mul_cancel₀ _ hA.ne').symm
  refine ⟨hTN, ?_, ?_⟩
  · change (∑' p, ‖T p‖) ≤ (b + 1.142) * A
    simp_rw [hex₁, tsum_mul_right]
    exact mul_le_mul_of_nonneg_right hNs hA.le
  · change ‖(∑' p, T p) - (∑' p, P p)‖ ≤ b * A
    rw [← hTN.of_norm.tsum_sub (outerIntegralLead_summable y h)]
    apply (norm_tsum_le_tsum_norm hRN).trans
    simp_rw [hex₂, tsum_mul_right]
    exact mul_le_mul_of_nonneg_right hR.2 hA.le

/-- Equation (74) for the explicit integral in (69). -/
theorem outerTransformIntegralAbsSum {y₀ y h : ℝ} (hy₀ : 80 < y₀)
    (hy : (9 / 10 : ℝ) * y₀ ≤ y) (hh : 8.76 < h) (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    Summable (fun p => ‖outerIntegralMode y h p‖) ∧
      (∑' p, ‖outerIntegralMode y h p‖) < 1.42 * outerTransformAmplitude y h := by
  have H := outerIntegral_abs_le (c := 9/10) le_rfl hy₀ hy hh hcap
  refine ⟨H.1, H.2.1.trans_lt ?_⟩
  apply mul_lt_mul_of_pos_right _ (outerTransformAmplitude_pos (by linarith) (by linarith))
  apply lt_of_le_of_lt _ outerTableLeftTotal
  have h₁ := outerSmallModeBound_left.le
  have h₂ := max_le_max (outerHighLowBound_uniform_left hy₀.le).le
    (outerHighLargeBound_uniform_left hy₀.le).le
  have h₃ := (outerLowerBound_uniform_left hy₀.le).le
  have h₄ := outerUpperBound_left.le
  nlinarith

/-- Equation (75) for the explicit integral in (69). -/
theorem outerTransformIntegralLeadingPair {y₀ h : ℝ} (hy₀ : 80 < y₀) (hh : 8.76 < h)
    (hcap : h ≤ 4 * y₀ ^ (1 / 3 : ℝ)) :
    ‖(∑' p, outerIntegralMode y₀ h p) - ((2 * (outerMainMode y₀ h π).re : ℝ) : ℂ)‖ <
      0.130 * outerTransformAmplitude y₀ h := by
  have H := outerIntegral_abs_le (y := y₀) (c := 1) (by norm_num) hy₀ (by simp) hh hcap
  rw [← outerIntegralLead_sum (by linarith : 0 < h)]
  apply H.2.2.trans_lt
  apply mul_lt_mul_of_pos_right _ (outerTransformAmplitude_pos (by linarith) (by linarith))
  apply lt_of_le_of_lt _ outerTableRightTotal
  have h₁ := outerSmallModeBound_right.le
  have h₂ := max_le_max (outerHighLowBound_uniform_right hy₀.le).le
    (outerHighLargeBound_uniform_right hy₀.le).le
  have h₃ := (outerLowerBound_uniform_right hy₀.le).le
  have h₄ := outerUpperBound_right.le
  nlinarith

end DurfeeCCS.Step10
