module

public import DurfeeCCS.EquationOne
public import DurfeeCCS.Step06.TwoColour

/-! Integer coefficient indices in the manuscript, including its zero convention. -/

@[expose] public section

open PowerSeries

namespace DurfeeCCS.Step13

/-- The coefficient at an integer index, extended by zero below degree zero. -/
noncomputable def intCoeff (H : ℤ⟦X⟧) (j : ℤ) : ℤ :=
  if 0 ≤ j then coeff j.toNat H else 0

theorem intCoeff_of_neg (H : ℤ⟦X⟧) {j : ℤ} (h : j < 0) : intCoeff H j = 0 := by
  simp [intCoeff, h.not_ge]

@[simp] theorem intCoeff_natCast (H : ℤ⟦X⟧) (j : ℕ) : intCoeff H j = coeff j H := by
  simp [intCoeff]

/-- The shift in the restricted two-colour partition coefficient is an integer difference. -/
theorem p_eq_intCoeff_restrictedPair (n d : ℕ) :
    (p n d : ℤ) = intCoeff (restrictedPairSeries d) ((n : ℤ) - (d : ℤ) ^ 2) := by
  by_cases h : d * d ≤ n
  · rw [p_eq_coeff_restrictedPairSeries h]
    have h' : ((d : ℤ) ^ 2) ≤ (n : ℤ) := by exact_mod_cast (by simpa [pow_two] using h)
    rw [intCoeff, ite_eq_left (sub_nonneg.mpr h')]
    have hdiff : ((n - d * d : ℕ) : ℤ) = (n : ℤ) - (d : ℤ) ^ 2 := by
      rw [Int.ofNat_sub h, pow_two]
      simp
    rw [← hdiff, Int.toNat_natCast]
  · have h' : (n : ℤ) - (d : ℤ) ^ 2 < 0 := by
      apply sub_neg.mpr
      exact_mod_cast (by simpa [pow_two] using Nat.lt_of_not_ge h)
    rw [p_eq_zero_of_sq_gt (Nat.lt_of_not_ge h), Nat.cast_zero, intCoeff_of_neg _ h']

end DurfeeCCS.Step13
