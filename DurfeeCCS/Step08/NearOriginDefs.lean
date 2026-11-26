module

public import DurfeeCCS.Step06.BesselSeries
public import DurfeeCCS.Step06.DurfeeAngle

/-! The normalized parameters and Bessel model in Lemma 3.1. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open DurfeeCCS.Step06

def nearOriginDelta (σ : ℝ) (n : ℕ) : ℝ := σ ^ 3 / n

def nearOriginEpsilon (σ : ℝ) (n : ℕ) : ℝ :=
  let r := σ ^ 2 / (n : ℝ)
  nearOriginDelta σ n * (0.66 / n + 0.228 * r + 0.35 * r / n)

def nearOriginBudget (σ : ℝ) (n : ℕ) : ℝ :=
  let Δ := nearOriginDelta σ n
  let ε := nearOriginEpsilon σ n
  15 / (2 * Real.pi) * (ε * Real.exp (Δ / 2 + ε) + Δ ^ 2 / 8 * Real.exp (Δ / 2)) +
    Δ * Real.exp (-σ / 2) *
      ((0.48 * σ + 0.36 * σ ^ 2) * Real.exp (1.02 * Δ) + σ / Real.pi ^ 2 + σ ^ 2 / 4)

def nearOriginModel (σ : ℝ) (n : ℕ) : ℂ :=
  (σ : ℂ) / n *
    (besselJ 0 (2 * σ) * besselI 1 (2 * σ) - besselJ 1 (2 * σ) * besselI 0 (2 * σ)) -
    (σ : ℂ) ^ 4 / (2 * (n : ℂ) ^ 2) * besselJ 2 (2 * σ) * besselI 2 (2 * σ)

def nearOriginMainLog (r θ : ℝ) (ζ : ℂ) : ℂ :=
  2 * Complex.I * (r : ℂ) * (Real.cos θ : ℂ) / ζ

def nearOriginCorrection (r θ : ℝ) (ζ : ℂ) : ℂ :=
  (r : ℂ) ^ 2 * (Real.cos (2 * θ) : ℂ) / (2 * ζ)

end DurfeeCCS.Step08
