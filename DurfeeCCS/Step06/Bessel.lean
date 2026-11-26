module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import DurfeeCCS.Step06.BesselSeries

/-! Compatibility of (9) with the Bessel function in the locked Mathlib revision. -/

public noncomputable section

namespace DurfeeCCS.Step06

private theorem hgCoeff_eq (ν k : ℕ) :
    Complex.regularizedHGFunCoeff 0 {((ν : ℂ) + 1)} k = besselAuxCoeff ν k := by
  have h : (ν : ℂ) + 1 + k = (↑(k + ν) : ℂ) + 1 := by push_cast; ring
  simp only [Complex.regularizedHGFunCoeff, besselAuxCoeff, Multiset.map_zero,
    Multiset.prod_zero, Multiset.map_singleton, Multiset.prod_singleton, h,
    Complex.Gamma_nat_eq_factorial]

/-- The manuscript's ordinary Bessel function agrees with Mathlib's at every natural order. -/
theorem besselJ_eq_mathlib (ν : ℕ) (z : ℂ) : besselJ ν z = Complex.besselJ (ν : ℂ) z := by
  rw [besselJ_eq_aux, Complex.besselJ_def]
  dsimp only
  rw [Complex.cpow_natCast, Complex.regularizedHGFun]
  have hseries : Complex.regularizedHGFunSeries 0 {((ν : ℂ) + 1)} = besselAuxSeries ν := by
    rw [Complex.regularizedHGFunSeries, besselAuxSeries]
    congr 1
    exact funext (hgCoeff_eq ν)
  rw [hseries]

/-- At a real argument the ordinary Bessel series has real value. -/
theorem besselJ_ofReal_eq (ν : ℕ) (x : ℝ) : besselJ ν (x : ℂ) = ↑(besselJ ν (x : ℂ)).re := by
  let a (k : ℕ) : ℝ :=
    (-1) ^ k * (x / 2) ^ (2 * k + ν) / ((k.factorial : ℝ) * ((k + ν).factorial : ℝ))
  have h : besselJ ν (x : ℂ) = (↑(∑' k, a k) : ℂ) := by
    rw [besselJ, Complex.ofReal_tsum]
    apply tsum_congr
    intro k
    simp only [a, besselJTerm, besselITerm]
    push_cast
    rw [mul_div_assoc]
  rw [h, Complex.ofReal_re]

end DurfeeCCS.Step06
