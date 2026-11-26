module

public import DurfeeCCS.Step10.OuterCoeffBounds
public import DurfeeCCS.Step10.OuterCoeffRademacher
public import DurfeeCCS.Step10.OuterCoeffSmall
public import DurfeeCCS.Step06.RademacherExactEstimate

/-! The unconditional coefficient error (68) and Lemma 4.2. -/

@[expose] public section

namespace DurfeeCCS.Step10

open Step06

/-- The exact coefficient error (68) for all positive indices. -/
theorem twoColour_bessel_error_unconditional {t : ℕ} (ht : 0 < t) :
    |(twoColourPartitionCount t : ℝ) - outerBesselMain (twoColourShift t)| ≤
      Real.pi ^ 3 / 36 * Real.exp (Real.pi * Real.sqrt ((t : ℝ) / 3)) := by
  by_cases ht' : t ≤ 15
  · exact twoColour_bessel_error_small ht ht'
  have herr := norm_twoColourPartitionCount_sub_RademacherMain_large (n := t) (by omega)
  have hab := (Complex.abs_re_le_norm ((twoColourPartitionCount t : ℂ) - twoColourRademacherMain t)).trans herr
  rw [Complex.sub_re, Complex.intCast_re, twoColourRademacherMain, Complex.re_ofReal_mul,
    rademacher_prefactor ht, rademacher_argument ht] at hab
  simpa only [outerBesselMain, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hab

/-- The coefficient error measured in units of the positive comparison function. -/
theorem twoColour_bessel_error_relative {t : ℕ} (ht : 0 < t) :
    |(twoColourPartitionCount t : ℝ) - outerBesselMain (twoColourShift t)| ≤
      outerComparisonB (twoColourShift t) * outerCoeffRemainder (twoColourShift t) := by
  rw [outerComparisonB_mul_remainder ht]
  exact twoColour_bessel_error_unconditional ht

/-- Manuscript Lemma 4.2, with all three endpoints included. -/
theorem lemma42 :
    (∀ {t : ℕ}, 0 < t → (twoColourPartitionCount t : ℝ) ≤ 2.6 * outerComparisonB (twoColourShift t)) ∧
    (∀ {t : ℕ}, 25 ≤ t → (twoColourPartitionCount t : ℝ) ≤ 1.1 * outerComparisonB (twoColourShift t)) ∧
    (∀ {t : ℕ}, 100 ≤ t → 0.9 * outerComparisonB (twoColourShift t) ≤ (twoColourPartitionCount t : ℝ)) :=
  lemma42_of_bessel_error twoColour_bessel_error_unconditional

end DurfeeCCS.Step10
