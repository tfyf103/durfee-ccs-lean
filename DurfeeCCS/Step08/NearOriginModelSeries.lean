module

public import DurfeeCCS.Step08.NearOriginDefs
public import DurfeeCCS.Step08.BesselConvolution

/-! Matching the integrated Laurent series to the Bessel model in (17). -/

@[expose] public section

namespace DurfeeCCS.Step08

open DurfeeCCS.Step06

theorem nearOriginModel_eq_series (σ : ℝ) (n : ℕ) :
    nearOriginModel σ n =
      (n : ℂ)⁻¹ * (∑' k : ℕ, (-1 : ℂ)^(k+1) * (σ : ℂ)^(4*(k+1)) /
        (((k+1).factorial : ℂ)^2 * ((2*k+1).factorial : ℂ))) -
      (σ : ℂ)^4 / (2 * (n : ℂ)^2) * (∑' k : ℕ, (-1 : ℂ)^k * (σ : ℂ)^(4*k+4) /
        ((k.factorial : ℂ) * ((k+2).factorial : ℂ) * ((2*k+2).factorial : ℂ))) := by
  unfold nearOriginModel
  rw [besselJ_zero_mul_besselI_one_sub_eq_series,
    mul_assoc _ (besselJ 2 _) (besselI 2 _),
    besselJ_mul_besselI_eq_series 2 (Or.inr rfl)]
  congr 1
  · rw [← tsum_mul_left, ← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [besselIJDerivativeTerm, show (2 : ℂ) * σ / 2 = σ by ring,
      show 4*(k+1) = (4*k+3)+1 by omega, pow_succ (σ : ℂ) (4*k+3)]
    ring
  · congr 1
    apply tsum_congr
    intro k
    rw [besselIJSeriesTerm, show (2 : ℂ) * σ / 2 = σ by ring]

end DurfeeCCS.Step08
