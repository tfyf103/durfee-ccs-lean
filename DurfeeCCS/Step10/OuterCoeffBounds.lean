module

public import DurfeeCCS.Step10.OuterCoeffData
public import DurfeeCCS.Step10.OuterCoeffGamma
public import DurfeeCCS.Step06.TwoColour
public import DurfeeCCS.Step07.ElementaryBounds
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic

/-! The comparison scale and explicit remainder constants in Lemma 4.2. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Step06 Step07

private theorem rpow_five_halves {y : ℝ} (hy : 0 < y) :
    y ^ (5 / 2 : ℝ) = y ^ (2 : ℕ) * Real.sqrt y := by
  rw [show (5 / 2 : ℝ) = (2 : ℕ) + 1 / 2 by norm_num, Real.rpow_add hy,
    Real.rpow_natCast, ← Real.sqrt_eq_rpow]

private theorem rpow_quarter {y : ℝ} (hy : 0 ≤ y) :
    y ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt y) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
  congr 1
  norm_num

private theorem comparison_normalization {y : ℝ} (hy : 0 < y) :
    Real.pi / (6 * y ^ 2) * outerBesselEnvelope (2 * Real.pi * y / Real.sqrt 3) =
      outerComparisonB y := by
  have h₃ : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hr : 0 < Real.sqrt (Real.sqrt (3 : ℝ)) := by positivity
  have hs : 0 < Real.sqrt y := by positivity
  have h3q : (3 : ℝ) ^ (3 / 4 : ℝ) = Real.sqrt 3 * Real.sqrt (Real.sqrt 3) := by
    rw [show (3 / 4 : ℝ) = 1 / 2 + 1 / 4 by norm_num, Real.rpow_add (by norm_num : (0:ℝ)<3),
      rpow_quarter (by norm_num), ← Real.sqrt_eq_rpow]
  have he : Real.sqrt (2 * Real.pi * (2 * Real.pi * y / Real.sqrt 3)) =
      2 * Real.pi * Real.sqrt y / Real.sqrt (Real.sqrt 3) := by
    rw [show 2 * Real.pi * (2 * Real.pi * y / Real.sqrt 3) =
        (2 * Real.pi) ^ 2 * (y / Real.sqrt 3) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_div hy.le]
    ring
  rw [outerBesselEnvelope, outerComparisonB, he, h3q, rpow_five_halves hy]
  field_simp [Real.pi_ne_zero, hy.ne', h₃.ne', hr.ne', hs.ne']
  rw [Real.sq_sqrt h₃.le]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- The normalization of the two-sided Bessel bounds to the comparison function B. -/
theorem outerBesselMain_bounds {y : ℝ} (hy : 0 < y) :
    outerComparisonB y * (1 - 15 * Real.sqrt 3 / (16 * Real.pi * y)) ≤ outerBesselMain y ∧
      outerBesselMain y ≤ outerComparisonB y := by
  let x := 2 * Real.pi * y / Real.sqrt 3
  have hx : 0 < x := by dsimp [x]; positivity
  have h := besselI_two_asymptotic_bounds hx
  have h1 : 15 / (8 * x) = 15 * Real.sqrt 3 / (16 * Real.pi * y) := by
    dsimp [x]
    field_simp [Real.pi_ne_zero, hy.ne', show Real.sqrt (3 : ℝ) ≠ 0 by positivity]
    norm_num
  have hg : 0 ≤ Real.pi / (6 * y ^ 2) := by positivity
  have hlow := mul_le_mul_of_nonneg_left h.1 hg
  rw [← mul_assoc, comparison_normalization hy, h1] at hlow
  have hupp := mul_le_mul_of_nonneg_left h.2 hg
  rw [comparison_normalization hy] at hupp
  constructor
  · simpa [outerBesselMain, x, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlow
  · simpa [outerBesselMain, x, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hupp

/-- The pointwise relative remainder function used in the proof of Lemma 4.2. -/
def outerCoeffRemainder (y : ℝ) : ℝ :=
  Real.pi ^ 3 / (3 : ℝ) ^ (5 / 4 : ℝ) * y ^ (5 / 2 : ℝ) *
    Real.exp ((Real.pi / Real.sqrt 3) * (Real.sqrt (y ^ 2 + 1 / 12) - 2 * y))

theorem outerComparisonB_mul_remainder {t : ℕ} (ht : 0 < t) :
    outerComparisonB (twoColourShift t) * outerCoeffRemainder (twoColourShift t) =
      Real.pi ^ 3 / 36 * Real.exp (Real.pi * Real.sqrt ((t : ℝ) / 3)) := by
  let y := twoColourShift t
  have hy := twoColourShift_pos ht
  have hy₂ := twoColourShift_sq ht
  have hy3 : y ^ 2 + 1 / 12 = (t : ℝ) := by dsimp [y]; linarith
  have H : (3 : ℝ) ^ (3 / 4 : ℝ) * 3 ^ (5 / 4 : ℝ) = 9 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show (3 / 4 + 5 / 4 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  change outerComparisonB y * outerCoeffRemainder y = _
  rw [outerComparisonB, outerCoeffRemainder, hy3, Real.sqrt_div (by positivity)]
  have he : 2 * Real.pi * y / Real.sqrt 3 +
      Real.pi / Real.sqrt 3 * (Real.sqrt (t : ℝ) - 2 * y) =
        Real.pi * (Real.sqrt (t : ℝ) / Real.sqrt 3) := by ring
  rw [show Real.exp (Real.pi * (Real.sqrt (t : ℝ) / Real.sqrt 3)) =
    Real.exp (2 * Real.pi * y / Real.sqrt 3) *
      Real.exp (Real.pi / Real.sqrt 3 * (Real.sqrt (t : ℝ) - 2 * y)) by rw [← Real.exp_add, he]]
  calc
    _ = Real.pi ^ 3 *
        (Real.exp (2 * Real.pi * y / Real.sqrt 3) *
          Real.exp (Real.pi / Real.sqrt 3 * (Real.sqrt (t : ℝ) - 2 * y))) /
        (4 * ((3 : ℝ) ^ (3 / 4 : ℝ) * 3 ^ (5 / 4 : ℝ))) := by
      field_simp [show y ^ (5 / 2 : ℝ) ≠ 0 by positivity,
        show (3 : ℝ) ^ (3 / 4 : ℝ) ≠ 0 by positivity,
        show (3 : ℝ) ^ (5 / 4 : ℝ) ≠ 0 by positivity]
    _ = _ := by rw [H]; ring

private theorem sqrt_three_interval :
    (1.73205080756887 : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 1.73205080756888 :=
  sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)

private theorem coeffRate_bounds :
    (1.8137993 : ℝ) ≤ Real.pi / Real.sqrt 3 ∧ Real.pi / Real.sqrt 3 ≤ 1.8137994 := by
  have hs : 0 < Real.sqrt (3 : ℝ) := by positivity
  exact ⟨(le_div_iff₀ hs).mpr (by linarith [sqrt_three_interval.2, pi_enclosure.1]),
    (div_le_iff₀ hs).mpr (by linarith [sqrt_three_interval.1, pi_enclosure.2])⟩

private theorem coeffPrefactor_le : Real.pi ^ 3 / (3 : ℝ) ^ (5 / 4 : ℝ) ≤ 7.85323 := by
  rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    Real.rpow_one, rpow_quarter (by norm_num)]
  apply (div_le_iff₀ (by positivity)).mpr
  have hl : (1.31607401295248 : ℝ) ≤ Real.sqrt (Real.sqrt 3) :=
    Real.le_sqrt_of_sq_le ((by norm_num : (1.31607401295248 : ℝ)^2 ≤ 1.73205080756887).trans sqrt_three_interval.1)
  obtain ⟨hπ₀,hπ₁⟩ := pi_enclosure
  calc
    _ ≤ (3.14159265358980 : ℝ)^3 := by
      apply pow_le_pow_left₀ Real.pi_pos.le _ 3
      convert hπ₁.le using 1 <;> norm_num
    _ ≤ 7.85323 * (3 * 1.31607401295248) := by norm_num
    _ ≤ _ := by gcongr

private theorem outerCoeffRemainder_bound {y m : ℝ} (hm : 0 < m) (hym : m ≤ y) :
    outerCoeffRemainder y ≤ 7.85323 * Real.exp (1.8137994 / (24 * m)) *
      (y ^ (5 / 2 : ℝ) * Real.exp (-(Real.pi / Real.sqrt 3) * y)) := by
  have hy := hm.trans_le hym
  let s := Real.sqrt (y ^ 2 + 1 / 12)
  have hs : s ^ 2 = y ^ 2 + 1 / 12 := Real.sq_sqrt (by positivity)
  have hu : y ≤ s := by rw [← Real.sqrt_sq hy.le]; exact Real.sqrt_le_sqrt (by linarith)
  have hx : s - y ≤ 1 / (24 * m) := by
    apply (le_div_iff₀ (show 0 < 24*m by positivity)).mpr
    have hm' : 2 * m ≤ s + y := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hm' (sub_nonneg.mpr hu)]
  have hRate := coeffRate_bounds
  have hE : Real.pi / Real.sqrt 3 * (s - y) ≤ 1.8137994 / (24 * m) := by
    calc
      _ ≤ 1.8137994 * (1 / (24 * m)) :=
        mul_le_mul hRate.2 hx (sub_nonneg.mpr hu) (by norm_num)
      _ = _ := by ring
  unfold outerCoeffRemainder
  change Real.pi ^ 3 / 3 ^ (5 / 4 : ℝ) * y ^ (5 / 2 : ℝ) *
      Real.exp (Real.pi / Real.sqrt 3 * (s - 2 * y)) ≤ _
  rw [show Real.pi / Real.sqrt 3 * (s - 2 * y) =
    Real.pi / Real.sqrt 3 * (s - y) + (-(Real.pi / Real.sqrt 3) * y) by ring, Real.exp_add]
  calc
    _ = (Real.pi ^ 3 / 3 ^ (5 / 4 : ℝ) * Real.exp (Real.pi / Real.sqrt 3 * (s - y))) *
          (y ^ (5 / 2 : ℝ) * Real.exp (-(Real.pi / Real.sqrt 3) * y)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul coeffPrefactor_le (Real.exp_le_exp.mpr hE) (Real.exp_pos _).le (by norm_num)

private theorem gammaPower_at_max {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    y ^ (5 / 2 : ℝ) * Real.exp (-a * y) ≤
      ((5 / 2 : ℝ) / a) ^ (5 / 2 : ℝ) * Real.exp (-(5 / 2)) := by
  let w : ℝ := (5 / 2 : ℝ) / a
  have hw : 0 < w := by positivity
  have hwa : a * w = 5 / 2 := by dsimp [w]; field_simp
  have hv := Real.log_le_sub_one_of_pos (div_pos hy hw)
  rw [Real.log_div hy.ne' hw.ne'] at hv
  have hv' : (5 / 2 : ℝ) * (Real.log y - Real.log w) ≤ a * y - a * w := by
    have h := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 5 / 2)
    have he : (5 / 2 : ℝ) * (y / w - 1) = a * y - a * w := by
      rw [← hwa]
      field_simp
    exact h.trans_eq he
  change _ ≤ w ^ (5 / 2 : ℝ) * _
  rw [Real.rpow_def_of_pos hw, Real.rpow_def_of_pos hy, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  linarith

private theorem outerCoeffRemainder_lt_general {y : ℝ} (hy : (0.957427 : ℝ) ≤ y) :
    outerCoeffRemainder y < 1.556 := by
  have h₀ : 0 < y := (by norm_num : 0 < (0.957427 : ℝ)).trans_le hy
  let a := Real.pi / Real.sqrt 3
  have ha : 0 < a := by dsimp [a]; positivity
  have hv : (5 / 2 : ℝ) / a ≤ 1.378323 := by
    apply (div_le_iff₀ ha).mpr
    have h := coeffRate_bounds.1
    change (1.8137993 : ℝ) ≤ a at h
    linarith
  have hga := gammaPower_at_max ha h₀
  have hwb : ((5 / 2 : ℝ) / a) ^ (5 / 2 : ℝ) ≤ (1.378323 : ℝ)^2 * 1.174021 := by
    calc
      _ ≤ (1.378323 : ℝ) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hv (by norm_num)
      _ = (1.378323 : ℝ)^2 * Real.sqrt 1.378323 := rpow_five_halves (by norm_num)
      _ ≤ _ := by
        gcongr
        exact (sqrt_enclosure (lo := 0) (by norm_num) (by norm_num) (by norm_num)).2
  refine (outerCoeffRemainder_bound (by norm_num) hy).trans_lt ?_
  calc
    _ ≤ 7.85323 * Real.exp ((1.8137994 : ℝ) / (24 * 0.957427)) *
          ((1.378323 : ℝ)^2 * 1.174021 * Real.exp (-(5 / 2))) := by
      exact mul_le_mul_of_nonneg_left
        (hga.trans (mul_le_mul_of_nonneg_right hwb (Real.exp_pos _).le)) (by positivity)
    _ = 7.85323 * ((1.378323 : ℝ)^2 * 1.174021) *
        Real.exp ((1.8137994 : ℝ) / (24 * 0.957427) - 5 / 2) := by
      rw [Real.exp_sub, Real.exp_neg]
      ring
    _ ≤ 7.85323 * ((1.378323 : ℝ)^2 * 1.174021) * Real.exp (-2.421064) := by gcongr; norm_num
    _ < _ := by dyadic_interval +kernel [prec := 50]

private theorem outerCoeffRemainder_lt_cutoff {y m M e : ℝ}
    (hm : 0 < m) (hym : m ≤ y) (hm' : (5 / 2 : ℝ) ≤ 1.8137993 * m)
    (hM : Real.sqrt m ≤ M) (he : (1.8137994 : ℝ) / (24 * m) - 1.8137993 * m ≤ e) :
    outerCoeffRemainder y ≤ 7.85323 * (m ^ 2 * M) * Real.exp e := by
  have ha := coeffRate_bounds
  let a := Real.pi / Real.sqrt 3
  have h₀ : 0 < a := by dsimp [a]; positivity
  have hM₀ : 0 ≤ M := (Real.sqrt_nonneg m).trans hM
  have hcut : (5 / 2 : ℝ) ≤ a * m := hm'.trans (mul_le_mul_of_nonneg_right ha.1 hm.le)
  have hd := antitoneOn_rpow_mul_exp_neg (by norm_num) h₀.le hm hcut (Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr hym) hym
  refine (outerCoeffRemainder_bound hm hym).trans ?_
  calc
    _ ≤ 7.85323 * Real.exp (1.8137994 / (24 * m)) * (m ^ (5 / 2 : ℝ) * Real.exp (-a * m)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = 7.85323 * (m ^ 2 * Real.sqrt m) * Real.exp (1.8137994 / (24 * m) - a * m) := by
      rw [rpow_five_halves hm, Real.exp_sub, show -a*m = -(a*m) by ring, Real.exp_neg]
      ring
    _ ≤ _ := by
      gcongr
      show (1.8137994 : ℝ) / (24 * m) - a * m ≤ e
      linarith [mul_le_mul_of_nonneg_right ha.1 hm.le]

theorem outerCoeffRemainder_lt1556 {t : ℕ} (ht : 0 < t) :
    outerCoeffRemainder (twoColourShift t) < 1.556 := by
  have h : (1 : ℝ) ≤ t := by exact_mod_cast ht
  apply outerCoeffRemainder_lt_general
  apply Real.le_sqrt_of_sq_le
  linarith

theorem outerCoeffRemainder_lt0052 {t : ℕ} (ht : 25 ≤ t) :
    outerCoeffRemainder (twoColourShift t) < 0.052 := by
  have h : (25 : ℝ) ≤ t := by exact_mod_cast ht
  have hy : (4.99165 : ℝ) ≤ twoColourShift t := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hM : Real.sqrt (4.99165 : ℝ) ≤ 2.234201 :=
    (sqrt_enclosure (lo := 0) (by norm_num) (by norm_num) (by norm_num)).2
  refine (outerCoeffRemainder_lt_cutoff (by norm_num) hy (by norm_num) hM (e := -9.038710)
    (by norm_num)).trans_lt ?_
  dyadic_interval +kernel [prec := 50]

theorem outerCoeffRemainder_lt000004 {t : ℕ} (ht : 100 ≤ t) :
    outerCoeffRemainder (twoColourShift t) < 0.00004 := by
  have h : (100 : ℝ) ≤ t := by exact_mod_cast ht
  have hy : (9.99583 : ℝ) ≤ twoColourShift t := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hM : Real.sqrt (9.99583 : ℝ) ≤ 3.161619 :=
    (sqrt_enclosure (lo := 0) (by norm_num) (by norm_num) (by norm_num)).2
  refine (outerCoeffRemainder_lt_cutoff (by norm_num) hy (by norm_num) hM (e := -18.122868)
    (by norm_num)).trans_lt ?_
  dyadic_interval +kernel [prec := 50]

/-- Exact coefficient constants of Lemma 4.2, from the coefficient error (68). -/
theorem lemma42_of_bessel_error
    (h68 : ∀ {t : ℕ}, 0 < t → |(twoColourPartitionCount t : ℝ) - outerBesselMain (twoColourShift t)| ≤
      Real.pi ^ 3 / 36 * Real.exp (Real.pi * Real.sqrt ((t : ℝ) / 3))) :
    (∀ {t : ℕ}, 0 < t → (twoColourPartitionCount t : ℝ) ≤ 2.6 * outerComparisonB (twoColourShift t)) ∧
    (∀ {t : ℕ}, 25 ≤ t → (twoColourPartitionCount t : ℝ) ≤ 1.1 * outerComparisonB (twoColourShift t)) ∧
    (∀ {t : ℕ}, 100 ≤ t → 0.9 * outerComparisonB (twoColourShift t) ≤ (twoColourPartitionCount t : ℝ)) := by
  have hup {t : ℕ} (ht : 0 < t) :
      (twoColourPartitionCount t : ℝ) ≤
        (1 + outerCoeffRemainder (twoColourShift t)) * outerComparisonB (twoColourShift t) := by
    obtain ⟨_, h⟩ := outerBesselMain_bounds (twoColourShift_pos ht)
    have herr := abs_le.mp (h68 ht)
    rw [← outerComparisonB_mul_remainder ht] at herr
    linarith
  refine ⟨fun {t} ht => (hup ht).trans ?_, fun {t} ht => (hup (show 0 < t by omega)).trans ?_, fun {t} ht => ?_⟩
  · have h := outerCoeffRemainder_lt1556 ht
    apply mul_le_mul_of_nonneg_right _ (outerComparisonB_pos (twoColourShift_pos ht)).le
    linarith
  · have h := outerCoeffRemainder_lt0052 ht
    apply mul_le_mul_of_nonneg_right _ (outerComparisonB_pos (twoColourShift_pos (show 0 < t by omega))).le
    linarith
  · have ht' : 0 < t := by omega
    have hR := outerCoeffRemainder_lt000004 ht
    obtain ⟨hB, _⟩ := outerBesselMain_bounds (twoColourShift_pos ht')
    have h := (abs_le.mp (h68 ht')).1
    rw [← outerComparisonB_mul_remainder ht'] at h
    have hd : 15 * Real.sqrt 3 / (16 * Real.pi * twoColourShift t) < 0.052 := by
      have hT : (100 : ℝ) ≤ t := by exact_mod_cast ht
      have hy : (9.99583 : ℝ) ≤ twoColourShift t := by
        apply Real.le_sqrt_of_sq_le
        linarith
      have hπ : (3.14159265358979 : ℝ) ≤ Real.pi := by convert pi_enclosure.1.le using 1 <;> norm_num
      apply (div_lt_iff₀ (by positivity)).mpr
      calc
        _ ≤ (15 : ℝ) * 1.73205080756888 := mul_le_mul_of_nonneg_left sqrt_three_interval.2 (by norm_num)
        _ < (0.052 : ℝ) * (16 * 3.14159265358979 * 9.99583) := by norm_num
        _ ≤ _ := by gcongr
    have hBp := outerComparisonB_pos (twoColourShift_pos ht')
    nlinarith [mul_nonneg hBp.le (sub_nonneg.mpr hR.le), mul_nonneg hBp.le (sub_nonneg.mpr hd.le)]

end DurfeeCCS.Step10
