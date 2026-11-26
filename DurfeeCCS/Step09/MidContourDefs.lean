module

public import DurfeeCCS.Step09.MidPhase
public import DurfeeCCS.Step08.DurfeeContour

/-! Parts of the contour used for Proposition 3.11. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex MeasureTheory Set DurfeeCCS.Step06 DurfeeCCS.Step08

def midDurfeeLine (n : ℕ) (r v : ℝ) : ℂ :=
  let ζ := verticalPoint (midU n r) v
  exp ((n : ℂ) * ζ) * durfeeAnalyticF (-(r : ℂ)^2) (exp (-ζ))

def midOuterContribution (n : ℕ) (r : ℝ) : ℂ :=
  (2*Real.pi : ℂ)⁻¹ * ∫ v in Icc (-Real.pi) Real.pi \ Ioo (-(8*midU n r)) (8*midU n r),
    midDurfeeLine n r v

def midCentralContribution (n : ℕ) (r : ℝ) : ℂ :=
  (2*Real.pi : ℂ)⁻¹ * ∫ v in (-(8*midU n r))..(8*midU n r), midDurfeeLine n r v

theorem ofReal_durfeeNegativeValue_eq_line {n : ℕ} {r : ℝ}
    (hu : 0 < midU n r) :
    (durfeeNegativeValue n r : ℂ) =
      (2*Real.pi : ℂ)⁻¹ * ∫ v in -Real.pi..Real.pi, midDurfeeLine n r v := by
  rw [ofReal_durfeeNegativeValue, durfeePolynomials_angular_coefficient n r _ hu]
  rfl

end DurfeeCCS.Step09
