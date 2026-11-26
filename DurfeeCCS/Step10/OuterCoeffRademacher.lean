module

public import DurfeeCCS.Step10.OuterCoeffBessel
public import DurfeeCCS.Step10.OuterCoeffData
public import DurfeeCCS.Step06.Rademacher
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-! The leading Bessel term and the coefficient error in manuscript (68). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Step06 Set MeasureTheory intervalIntegral

theorem rademacher_argument {t : ℕ} (ht : 0 < t) :
    twoColourBesselScale t = 2 * Real.pi * twoColourShift t / Real.sqrt 3 := by
  have hy := twoColourShift_pos ht
  have hY := twoColourShift_sq ht
  have h₃ : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hex : 12 * (t : ℝ) - 1 = (2 * Real.sqrt 3 * twoColourShift t) ^ 2 := by
    rw [mul_pow, mul_pow, h₃, hY]
    ring
  unfold twoColourBesselScale
  rw [hex, Real.sqrt_sq (by positivity)]
  field_simp
  nlinarith

theorem rademacher_prefactor {t : ℕ} (ht : 0 < t) :
    2 * Real.pi / (12 * (t : ℝ) - 1) = Real.pi / (6 * twoColourShift t ^ 2) := by
  rw [twoColourShift_sq ht]
  have h : (12 * (t : ℝ) - 1) ≠ 0 := by
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  field_simp [h]
  <;> ring

private theorem zeta_two_tail_le_one :
    (∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) ≤ 1 := by
  have hsum := hasSum_zeta_two
  have h := hsum.summable.sum_add_tsum_nat_add 2
  rw [hsum.tsum_eq] at h
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have he : (∑' i : ℕ, (((i : ℝ) + 2) ^ 2)⁻¹) =
      (∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) := by
    apply tsum_congr
    intro k
    push_cast
    rw [one_div]
  rw [he] at h
  have hp := Real.pi_lt_d2
  have hp₀ := Real.pi_pos
  nlinarith [mul_nonneg (sub_nonneg.mpr hp.le) (by linarith : 0 ≤ (3.15 : ℝ) + Real.pi)]

/-- The Rademacher right-hand side has a first-term error bounded by (68). -/
theorem twoColour_rademacher_bessel_error {t : ℕ} (ht : 0 < t) :
    |(twoColourRademacherRHS t).re - outerBesselMain (twoColourShift t)| ≤
      Real.pi ^ 3 / 36 * Real.exp (Real.pi * Real.sqrt ((t : ℝ) / 3)) := by
  let y := twoColourShift t
  let c := Real.pi / (6 * y ^ 2)
  let e := Real.exp (Real.pi * Real.sqrt ((t : ℝ) / 3))
  have hy := twoColourShift_pos ht
  have hc : 0 < c := by dsimp [c]; positivity
  have hscale : twoColourBesselScale t = 2 * Real.pi * y / Real.sqrt 3 :=
    rademacher_argument ht
  have hbound (k : ℕ) : ‖twoColourRademacherTerm t (k + 2)‖ ≤
      (Real.pi ^ 2 * y ^ 2 / 6 * e) * (1 / ((k + 2 : ℕ) : ℝ) ^ 2) := by
    let ell : ℝ := (k + 2 : ℕ)
    have hell : 2 ≤ ell := by dsimp [ell]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hell₀ : 0 < ell := by linarith
    let x := twoColourBesselScale t / ell
    have hx₀ : 0 ≤ x := by dsimp [x]; rw [hscale]; positivity
    have hy' : y / Real.sqrt 3 ≤ Real.sqrt ((t : ℝ) / 3) := by
      rw [Real.sqrt_div (by positivity)]
      exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (by positivity)
    have hx : x ≤ Real.pi * Real.sqrt ((t : ℝ) / 3) := by
      dsimp [x]
      rw [hscale]
      have haux : 2 * Real.pi * y / Real.sqrt 3 / ell ≤ Real.pi * (y / Real.sqrt 3) := by
        apply (div_le_iff₀ hell₀).mpr
        calc
          _ = Real.pi * (y / Real.sqrt 3) * 2 := by ring
          _ ≤ _ := by gcongr
      exact haux.trans (mul_le_mul_of_nonneg_left hy' Real.pi_pos.le)
    have hg : Real.exp x ≤ e := Real.exp_le_exp.mpr hx
    change ‖twoColourKloosterman t (k + 2) / (↑(k + 2 : ℕ) : ℂ) * besselI 2 (x : ℂ)‖ ≤ _
    rw [norm_mul, norm_div, Complex.norm_natCast]
    calc
      _ ≤ 1 * ‖besselI 2 (x : ℂ)‖ :=
        mul_le_mul_of_nonneg_right
          ((div_le_one hell₀).mpr (norm_twoColourKloosterman_le t (k + 2))) (norm_nonneg _)
      _ ≤ x ^ 2 / 8 * Real.exp x := by simpa using norm_besselI_two_real_le hx₀
      _ ≤ x ^ 2 / 8 * e := by gcongr
      _ = _ := by
        dsimp only [x]
        rw [hscale]
        change (2 * Real.pi * y / Real.sqrt 3 / ell) ^ 2 / 8 * e =
          Real.pi ^ 2 * y ^ 2 / 6 * e * (1 / ell ^ 2)
        rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        ring
  have hs := (summable_twoColourRademacherTerm t).comp_injective Nat.succ_injective
  have hs' := (summable_norm_twoColourRademacherTerm t).comp_injective Nat.succ_injective
  have hs2 := hasSum_zeta_two.summable.comp_injective (show Function.Injective (· + 2 : ℕ → ℕ)
    from fun _ _ he => Nat.add_right_cancel he)
  have hsum : ‖∑' k : ℕ, twoColourRademacherTerm t (k + 2)‖ ≤ Real.pi ^ 2 * y ^ 2 / 6 * e := by
    calc
      _ ≤ ∑' k : ℕ, ‖twoColourRademacherTerm t (k + 2)‖ := norm_tsum_le_tsum_norm hs'
      _ ≤ ∑' k : ℕ, (Real.pi ^ 2 * y ^ 2 / 6 * e) * (1 / ((k + 2 : ℕ) : ℝ) ^ 2) :=
        hs'.tsum_le_tsum hbound (hs2.mul_left _)
      _ ≤ _ := by
        rw [tsum_mul_left]
        have hnon : 0 ≤ Real.pi ^ 2 * y ^ 2 / 6 * e := by positivity
        simpa using mul_le_mul_of_nonneg_left zeta_two_tail_le_one hnon
  have heq : (twoColourRademacherRHS t).re - outerBesselMain y =
      c * (∑' k : ℕ, twoColourRademacherTerm t (k + 2)).re := by
    rw [twoColourRademacherRHS, rademacher_prefactor ht,
      (summable_twoColourRademacherTerm t).tsum_eq_zero_add]
    simp only [Complex.re_ofReal_mul, Complex.add_re, Nat.zero_add]
    have hfirst : twoColourRademacherTerm t 1 = besselI 2 ((2 * Real.pi * y / Real.sqrt 3 : ℝ) : ℂ) := by
      simp [twoColourRademacherTerm, hscale]
    rw [hfirst]
    unfold outerBesselMain
    change c * (_ + _) - _ = _
    dsimp [c]
    have hY : 6 * y ^ 2 ≠ 0 := by positivity
    ring
  change |(twoColourRademacherRHS t).re - outerBesselMain y| ≤ Real.pi ^ 3 / 36 * e
  rw [heq, abs_mul, abs_of_pos hc]
  calc
    _ ≤ c * ‖∑' k : ℕ, twoColourRademacherTerm t (k + 2)‖ := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ ≤ c * (Real.pi ^ 2 * y ^ 2 / 6 * e) := by gcongr
    _ = _ := by
      have hy' : y ≠ 0 := hy.ne'
      dsimp [c]
      field_simp [hy']
      ring

/-- Manuscript (68) from the exact coefficient identity (14). -/
theorem twoColour_bessel_error (h14 : TwoColourRademacherIdentity) {t : ℕ} (ht : 0 < t) :
    |(twoColourPartitionCount t : ℝ) - outerBesselMain (twoColourShift t)| ≤
      Real.pi ^ 3 / 36 * Real.exp (Real.pi * Real.sqrt ((t : ℝ) / 3)) := by
  simpa [← h14 t ht] using twoColour_rademacher_bessel_error ht

end DurfeeCCS.Step10
