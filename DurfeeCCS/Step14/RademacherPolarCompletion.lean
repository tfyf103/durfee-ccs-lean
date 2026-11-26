module

public import DurfeeCCS.Step06.RademacherExactPolar
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The completed polar contribution on a Ford circle and its endpoint errors. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step14

open Complex Filter MeasureTheory Set
open scoped Topology
open DurfeeCCS.Step06 DurfeeCCS.Step08

/-- The parameter for the positive Fourier index in the inverse Ford coordinate. -/
def fordPolarB (n k : ℕ) : ℝ := 2 * Real.pi * ((n : ℝ) - 1 / 12) / (k : ℝ) ^ 2

/-- The polar integrand after substituting the inverse Ford coordinate. -/
def fordPolarIntegrand (n k : ℕ) (v : ℝ) : ℂ :=
  rademacherPolarKernel (Real.pi / 6) (fordPolarB n k) (verticalPoint 1 v) / (k : ℂ) ^ 3

theorem fordPolarB_pos {n k : ℕ} (hn : 0 < n) (hk : 0 < k) : 0 < fordPolarB n k := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold fordPolarB
  exact div_pos (mul_pos (by positivity) (by linarith)) (by positivity)

theorem fordPolarB_le {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    fordPolarB n k ≤ 2 * Real.pi * n := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold fordPolarB
  exact (div_le_self (mul_nonneg (by positivity) (by linarith))
    (one_le_pow₀ hk')).trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

theorem integrable_fordPolarIntegrand {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    Integrable (fordPolarIntegrand n k) := by
  exact (integral_rademacherPolarKernel zero_lt_one (by positivity) (fordPolarB_pos hn hk)).1.div_const _

/-- The complete inverse Ford line gives the exact Bessel and denominator
normalization appearing in (14), before the arithmetic phase. -/
theorem integral_fordPolarIntegrand {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (∫ v : ℝ, fordPolarIntegrand n k v) =
      ((2 * Real.pi / (12 * (n : ℝ) - 1) : ℝ) : ℂ) / (k : ℂ) *
        besselI 2 ((twoColourBesselScale n / (k : ℝ) : ℝ) : ℂ) := by
  let A : ℝ := Real.pi / 6
  let B : ℝ := fordPolarB n k
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := fordPolarB_pos hn hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hkR.ne'
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hshift : (0 : ℝ) < 12 * (n : ℝ) - 1 := by linarith
  have hratio : A / B = (k : ℝ) ^ 2 / (12 * (n : ℝ) - 1) := by
    dsimp [A, B, fordPolarB]
    field_simp [Real.pi_ne_zero, hkR.ne', hshift.ne', (show (n : ℝ) - 1 / 12 ≠ 0 by linarith)]
    ring
  have harg : 2 * Real.sqrt (A * B) = twoColourBesselScale n / (k : ℝ) := by
    apply (sq_eq_sq₀ (by positivity) (by unfold twoColourBesselScale; positivity)).mp
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hA.le hB.le), twoColourBesselScale, div_pow, div_pow,
      mul_pow, Real.sq_sqrt hshift.le]
    dsimp [A, B, fordPolarB]
    field_simp [hkR.ne']
    ring
  have h := (integral_rademacherPolarKernel zero_lt_one hA hB).2
  rw [inv_mul_eq_div, div_eq_iff (Complex.ofReal_ne_zero.mpr
    (show 2 * Real.pi ≠ 0 by positivity))] at h
  change (∫ v : ℝ, rademacherPolarKernel A B (verticalPoint 1 v) / (k : ℂ) ^ 3) = _
  rw [integral_div, h, hratio, harg]
  push_cast
  field_simp [hkC]

/-- A uniform majorant that controls both inverse-Ford tails even when the
neighbor has small denominator. -/
theorem norm_fordPolarIntegrand_le {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (v : ℝ) :
    ‖fordPolarIntegrand n k v‖ ≤
      8 * Real.exp (Real.pi / 6 + 2 * Real.pi * n) / (k : ℝ) ^ 3 / (1 + |v|) ^ 3 := by
  let w := verticalPoint 1 v
  have hwr : w.re = 1 := by simp [w, verticalPoint, Complex.mul_re]
  have hwi : w.im = v := by simp [w, verticalPoint, Complex.mul_im]
  have h1 : (1 : ℝ) ≤ ‖w‖ := by
    simpa only [hwr, abs_one] using Complex.abs_re_le_norm w
  have hv : |v| ≤ ‖w‖ := by simpa only [hwi] using Complex.abs_im_le_norm w
  have htotal : (1 + |v|) / 2 ≤ ‖w‖ := by linarith only [h1, hv]
  have hInv : w⁻¹.re ≤ 1 := by
    rw [Complex.inv_re, Complex.normSq_apply, hwr, hwi]
    have hd : 1 ≤ (1 : ℝ) * 1 + v * v := by nlinarith only [sq_nonneg v]
    exact (div_le_one (zero_lt_one.trans_le hd)).mpr hd
  have hB := fordPolarB_pos hn hk
  have hdiv : ((fordPolarB n k : ℂ) / w).re = fordPolarB n k * w⁻¹.re := by
    rw [div_eq_mul_inv, Complex.re_ofReal_mul]
  have hExp : ((Real.pi / 6 : ℝ) * w + (fordPolarB n k : ℂ) / w).re ≤
      Real.pi / 6 + 2 * Real.pi * n := by
    rw [Complex.add_re, Complex.re_ofReal_mul, hdiv, hwr, mul_one]
    linarith only [mul_le_mul_of_nonneg_left hInv hB.le, fordPolarB_le hn hk]
  change ‖rademacherPolarKernel (Real.pi / 6) (fordPolarB n k) w / (k : ℂ) ^ 3‖ ≤ _
  rw [rademacherPolarKernel, norm_div, norm_div, norm_pow, norm_pow, Complex.norm_exp,
    Complex.norm_natCast]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hab : 0 ≤ |v| := abs_nonneg v
  calc
    _ ≤ Real.exp (Real.pi / 6 + 2 * Real.pi * n) / ((1 + |v|) / 2) ^ 3 / (k : ℝ) ^ 3 :=
      div_le_div_of_nonneg_right
        (div_le_div₀ (by positivity) (Real.exp_le_exp.mpr hExp) (by positivity)
          (pow_le_pow_left₀ (by positivity) htotal 3)) (by positivity)
    _ = _ := by
      field_simp [hkR.ne', (show 1 + |v| ≠ 0 by positivity)]
      ring

private theorem shiftedCubicIntegral {H : ℝ} (hH : 0 ≤ H) :
    IntegrableOn (fun v : ℝ => (v + 1) ^ (-3 : ℝ)) (Ioi H) ∧
      (∫ v in Ioi H, (v + 1) ^ (-3 : ℝ)) = 1 / (2 * (H + 1) ^ 2) := by
  let f : ℝ → ℝ := fun v => v + 1
  let g : ℝ → ℝ := fun v => v ^ (-3 : ℝ)
  have hf : MeasurableEmbedding f :=
    (Homeomorph.addRight (1 : ℝ)).measurableEmbedding
  have hμ : MeasurePreserving f volume volume :=
    measurePreserving_add_right (volume : Measure ℝ) (1 : ℝ)
  have hpre : f ⁻¹' Ioi (H + 1) = Ioi H := by
    ext v
    simp [f]
  have hh : 0 < H + 1 := by positivity
  have hi : IntegrableOn g (Ioi (H + 1)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hh
  refine ⟨?_, ?_⟩
  · simpa only [hpre, Function.comp_def, f, g] using
      (hμ.integrableOn_comp_preimage hf).mpr hi
  calc
    _ = ∫ v in Ioi (H + 1), v ^ (-3 : ℝ) := by
      simpa only [hpre, f, g] using hμ.setIntegral_preimage_emb hf g (Ioi (H + 1))
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hh,
        show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hh.le, Real.rpow_two]
      field_simp [hh.ne']

private theorem norm_fordPolar_halfTail {n k : ℕ} (hk : 0 < k)
    {H : ℝ} (hH : 0 ≤ H) {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi H))
    (hgNorm : ∀ v ∈ Ioi H, ‖g v‖ ≤
      8 * Real.exp (Real.pi / 6 + 2 * Real.pi * n) / (k : ℝ) ^ 3 / (v + 1) ^ 3) :
    ‖∫ v in Ioi H, g v‖ ≤
      4 * Real.exp (Real.pi / 6 + 2 * Real.pi * n) / (k : ℝ) ^ 3 / (H + 1) ^ 2 := by
  let C : ℝ := 8 * Real.exp (Real.pi / 6 + 2 * Real.pi * n) / (k : ℝ) ^ 3
  have hDom := (shiftedCubicIntegral hH).1.const_mul C
  have hpoint (v : ℝ) (hv : v ∈ Ioi H) :
      ‖g v‖ ≤ C * (v + 1) ^ (-3 : ℝ) := by
    rw [Real.rpow_neg (by have : H < v := hv; linarith),
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← div_eq_mul_inv]
    exact hgNorm v hv
  calc
    _ ≤ ∫ v in Ioi H, ‖g v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioi H, C * (v + 1) ^ (-3 : ℝ) :=
      setIntegral_mono_on hg.norm hDom measurableSet_Ioi hpoint
    _ = _ := by
      rw [integral_const_mul, (shiftedCubicIntegral hH).2]
      dsimp [C]
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp [hk'.ne', (show H + 1 ≠ 0 by positivity)]
      norm_num

/-- Truncating the inverse line at both Farey endpoints produces a uniform
polar error of order 1/(k N²), with k the denominator of the central cusp. -/
theorem norm_fordPolar_truncation_le {n k N : ℕ} (hn : 0 < n) (hk : 0 < k) (hN : 0 < N)
    {left right : ℝ} (hl : 0 ≤ left) (hr : 0 ≤ right)
    (hlN : (N : ℝ) ≤ (k : ℝ) * (left + 1)) (hrN : (N : ℝ) ≤ (k : ℝ) * (right + 1)) :
    ‖(∫ v in -left..right, fordPolarIntegrand n k v) -
      (∫ v : ℝ, fordPolarIntegrand n k v)‖ ≤
      8 * Real.exp (Real.pi / 6 + 2 * Real.pi * n) / ((k : ℝ) * (N : ℝ) ^ 2) := by
  let f := fordPolarIntegrand n k
  let E := Real.exp (Real.pi / 6 + 2 * Real.pi * n)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : Integrable f := integrable_fordPolarIntegrand hn hk
  have hfneg : Integrable (fun v => f (-v)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hf
  have hscale (H : ℝ) (hH : 0 ≤ H) (hHN : (N : ℝ) ≤ (k : ℝ) * (H + 1)) :
      4 * E / (k : ℝ) ^ 3 / (H + 1) ^ 2 ≤ 4 * E / ((k : ℝ) * (N : ℝ) ^ 2) := by
    calc
      _ = 4 * E / ((k : ℝ) * ((k : ℝ) * (H + 1)) ^ 2) := by
        simp only [div_div, mul_pow]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN'.le hHN 2) hk'.le)
  have hright : ‖∫ v in Ioi right, f v‖ ≤ 4 * E / ((k : ℝ) * (N : ℝ) ^ 2) := by
    apply (norm_fordPolar_halfTail hk hr hf.integrableOn fun v hv => ?_).trans (hscale right hr hrN)
    have hv' : 0 ≤ v := hr.trans (mem_Ioi.mp hv).le
    simpa only [f, abs_of_nonneg hv', add_comm 1 v] using norm_fordPolarIntegrand_le hn hk v
  have hleft : ‖∫ v in Iic (-left), f v‖ ≤ 4 * E / ((k : ℝ) * (N : ℝ) ^ 2) := by
    rw [← integral_comp_neg_Ioi]
    apply (norm_fordPolar_halfTail hk hl hfneg.integrableOn fun v hv => ?_).trans (hscale left hl hlN)
    have hv' : 0 ≤ v := hl.trans (mem_Ioi.mp hv).le
    simpa only [f, abs_neg, abs_of_nonneg hv', add_comm 1 v] using norm_fordPolarIntegrand_le hn hk (-v)
  have hsplit₁ := intervalIntegral.integral_interval_add_Ioi
    (a := -left) (b := right) hf.integrableOn hf.integrableOn
  have hsplit₂ := intervalIntegral.integral_Iic_add_Ioi (b := -left) hf.integrableOn hf.integrableOn
  have hsplit : (∫ v in -left..right, f v) - (∫ v, f v) =
      -((∫ v in Iic (-left), f v) + (∫ v in Ioi right, f v)) := by
    rw [← hsplit₂, ← hsplit₁]
    abel
  change ‖(∫ v in -left..right, f v) - (∫ v, f v)‖ ≤ _
  rw [hsplit, norm_neg]
  exact (norm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))

/-- Summing errors scaled by 1/(k N²) across the reduced numerators gives
a total error of order 1/N. -/
theorem norm_ford_sum_error_le {N : ℕ} (hN : 0 < N) {C : ℝ} (hC : 0 ≤ C)
    (numerators : ℕ → Finset ℕ) (hcard : ∀ k, (numerators k).card ≤ k)
    (err : ℕ → ℕ → ℂ)
    (hbound : ∀ k ∈ Finset.Icc 1 N, ∀ h ∈ numerators k, ‖err h k‖ ≤
      C / ((k : ℝ) * (N : ℝ) ^ 2)) :
    ‖∑ k ∈ Finset.Icc 1 N, ∑ h ∈ numerators k, err h k‖ ≤ C / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 N, ‖∑ h ∈ numerators k, err h k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 N, C / (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hc' : ((numerators k).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard k
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hbound k hk)).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      refine (mul_le_mul_of_nonneg_right hc' (by positivity)).trans_eq ?_
      field_simp [hk'.ne', hN'.ne']
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      simp only [Nat.add_sub_cancel]
      field_simp [hN'.ne']

/-- Exact normalization of the completed polar integrals summed over the
reduced cusp numerators and denominators at most N. -/
theorem fordPolar_sum_eq_truncated (n N : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc 1 N, ∑ h ∈ (Finset.range k).filter (fun h => h.Coprime k),
      twoColourPhase n h k * (∫ v : ℝ, fordPolarIntegrand n k v)) =
    ((2 * Real.pi / (12 * (n : ℝ) - 1) : ℝ) : ℂ) *
      ∑ k ∈ Finset.range N, twoColourRademacherTerm n (k + 1) := by
  let A : ℂ := ((2 * Real.pi / (12 * (n : ℝ) - 1) : ℝ) : ℂ)
  have hshift :
      (∑ k ∈ Finset.Icc 1 N, A * twoColourRademacherTerm n k) =
        ∑ k ∈ Finset.range N, A * twoColourRademacherTerm n (k + 1) := by
    apply Finset.sum_bij (fun k _ => k - 1)
    · intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨hl, hu⟩
      exact Finset.mem_range.mpr (by omega)
    · intro a ha b hb h
      have ha' := (Finset.mem_Icc.mp ha).1
      have hb' := (Finset.mem_Icc.mp hb).1
      omega
    · intro k hk
      refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, by omega⟩
      exact Finset.mem_range.mp hk
    · intro k hk
      rw [Nat.sub_add_cancel (Finset.mem_Icc.mp hk).1]
  change _ = A * _
  rw [Finset.mul_sum, ← hshift]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_fordPolarIntegrand hn (Finset.mem_Icc.mp hk).1]
  rw [twoColourRademacherTerm, twoColourKloosterman, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  change twoColourPhase n h k * (A / (k : ℂ) * _) =
    A * (twoColourPhase n h k / (k : ℂ) * _)
  ring

/-- With the finite Ford dissection and its local nonpolar estimates, the
truncated coefficient sum has an explicit error tending to zero. -/
theorem norm_twoColour_truncated_error {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {C : ℝ} (hC : 0 ≤ C) (left right : ℕ → ℕ → ℝ) (err : ℕ → ℕ → ℂ)
    (hsize : ∀ k ∈ Finset.Icc 1 N, ∀ h ∈ (Finset.range k).filter (fun h => h.Coprime k),
      0 ≤ left h k ∧ 0 ≤ right h k ∧
      (N : ℝ) ≤ (k : ℝ) * (left h k + 1) ∧ (N : ℝ) ≤ (k : ℝ) * (right h k + 1))
    (herr : ∀ k ∈ Finset.Icc 1 N, ∀ h ∈ (Finset.range k).filter (fun h => h.Coprime k),
      ‖err h k‖ ≤ C / ((k : ℝ) * (N : ℝ) ^ 2))
    (hsplit : (twoColourPartitionCount n : ℂ) =
      ∑ k ∈ Finset.Icc 1 N, ∑ h ∈ (Finset.range k).filter (fun h => h.Coprime k),
        (twoColourPhase n h k * (∫ v in -(left h k)..right h k, fordPolarIntegrand n k v) +
          err h k)) :
    ‖(twoColourPartitionCount n : ℂ) -
        ((2 * Real.pi / (12 * (n : ℝ) - 1) : ℝ) : ℂ) *
        ∑ k ∈ Finset.range N, twoColourRademacherTerm n (k + 1)‖ ≤
      (8 * Real.exp (Real.pi / 6 + 2 * Real.pi * n) + C) / (N : ℝ) := by
  rw [hsplit, ← fordPolar_sum_eq_truncated n N hn, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, add_sub_right_comm _ (err _ _), ← mul_sub]
  apply norm_ford_sum_error_le hN (by positivity)
  · intro k
    simpa using Finset.card_filter_le (Finset.range k) (fun h => h.Coprime k)
  · intro k hk h hh
    rcases hsize k hk h hh with ⟨hl, hr, hlN, hrN⟩
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_twoColourPhase, one_mul, add_div]
    exact add_le_add (norm_fordPolar_truncation_le hn (Finset.mem_Icc.mp hk).1 hN hl hr hlN hrN)
      (herr k hk h hh)

/-- An error estimate on finite denominator sums suffices for the infinite coefficient
identity, with absolute summability supplied by the existing bound in (14). -/
theorem twoColourRademacherIdentity_of_truncated_error
    (h : ∀ n : ℕ, 0 < n → ∃ C : ℝ, ∀ N : ℕ, 0 < N →
      ‖(twoColourPartitionCount n : ℂ) -
        ((2 * Real.pi / (12 * (n : ℝ) - 1) : ℝ) : ℂ) *
        ∑ k ∈ Finset.range N, twoColourRademacherTerm n (k + 1)‖ ≤ C / (N : ℝ)) :
    TwoColourRademacherIdentity := by
  intro n hn
  let A : ℂ := ((2 * Real.pi / (12 * (n : ℝ) - 1) : ℝ) : ℂ)
  let q : ℕ → ℂ := fun N => A * ∑ k ∈ Finset.range N, twoColourRademacherTerm n (k + 1)
  have hq : Tendsto q atTop (𝓝 (twoColourRademacherRHS n)) := by
    exact ((summable_twoColourRademacherTerm n).hasSum.tendsto_sum_nat).const_mul A
  obtain ⟨C, hC⟩ := h n hn
  have hN : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  have hlimit : Tendsto (fun N => (twoColourPartitionCount n : ℂ) - q N) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) (hN.mono fun N hN' => hC N hN') ?_
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
  exact sub_eq_zero.mp (tendsto_nhds_unique (hq.const_sub _) hlimit)

end DurfeeCCS.Step14
