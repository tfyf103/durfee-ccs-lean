module

public import DurfeeCCS.Step08.NearOriginDefs

/-! Normalization of the four terms in the near-origin contour error. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

theorem nearOrigin_r_div_u {σ : ℝ} {n : ℕ} (hσ : σ ≠ 0) (hn : 0 < n) :
    (σ^2 / (n : ℝ)) / (σ / (n : ℝ)) = σ := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hσ, hnR]

theorem nearOrigin_r_sq_div_u {σ : ℝ} {n : ℕ} (hσ : σ ≠ 0) (hn : 0 < n) :
    (σ^2 / (n : ℝ))^2 / (σ / (n : ℝ)) = nearOriginDelta σ n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold nearOriginDelta
  field_simp [hσ, hnR]

theorem nearOrigin_central_epsilon_normalize (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    let r := σ^2 / (n : ℝ)
    let u := σ / (n : ℝ)
    0.66 * r * u + 0.228 * r * nearOriginDelta σ n + 0.35 * r^2 * u =
      nearOriginEpsilon σ n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [nearOriginEpsilon, nearOriginDelta]
  field_simp [hnR]

theorem nearOrigin_budget_normalize {σ : ℝ} {n : ℕ} (hσ : 0 < σ) (hn : 0 < n)
    {central : ℝ}
    (hc : central =
      nearOriginEpsilon σ n * Real.exp (nearOriginDelta σ n / 2 + nearOriginEpsilon σ n) +
        nearOriginDelta σ n ^ 2 / 8 * Real.exp (nearOriginDelta σ n / 2)) :
    let r := σ^2 / (n : ℝ)
    let u := σ / (n : ℝ)
    Real.exp σ *
      ((2 * Real.pi)⁻¹ * ((15 * u * Real.exp (r/u) / (r/u)) * central) +
        Real.exp (r/u/2 + 1.02 * (r^2/u)) * (0.48 * r^2 + 0.36 * (r^3/u)) +
        (2 * Real.pi)⁻¹ * (2 * Real.exp (r/u/2) * r^2 / Real.pi) +
        (2 * Real.pi)⁻¹ * (Real.pi * Real.exp (r/u/2) * r^3 / (2*u))) =
      Real.exp (2 * σ) * nearOriginBudget σ n / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hExpHalf : Real.exp (σ/2) = Real.exp σ * Real.exp (-σ/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hExpTwo : Real.exp (2*σ) = Real.exp σ * Real.exp σ := by
    rw [two_mul, Real.exp_add]
  dsimp only
  set r : ℝ := σ^2 / (n : ℝ)
  set u : ℝ := σ / (n : ℝ)
  have hσu : r/u = σ := nearOrigin_r_div_u hσ.ne' hn
  have hΔ : r^2/u = nearOriginDelta σ n := nearOrigin_r_sq_div_u hσ.ne' hn
  have hR2 : r^2 = nearOriginDelta σ n * σ / n := by
    dsimp [r, nearOriginDelta]
    ring
  have hR3 : r^3/u = nearOriginDelta σ n * σ^2 / n := by
    dsimp [r, u, nearOriginDelta]
    field_simp [hnR, hσ.ne']
  have hFourth : r^3 / (2*u) = (nearOriginDelta σ n * σ^2 / n) / 2 := by
    rw [mul_comm (2 : ℝ), ← div_div, hR3]
  have hFourth' : Real.pi * Real.exp (r/u/2) * r^3 / (2*u) =
      Real.pi * Real.exp (r/u/2) * ((nearOriginDelta σ n * σ^2 / n) / 2) := by
    rw [mul_div_assoc, hFourth]
  unfold nearOriginBudget
  rw [hFourth', hσu, hΔ, hR2, hR3, hc, Real.exp_add (σ/2), hExpHalf, hExpTwo]
  dsimp [u]
  field_simp [hnR, hσ.ne', Real.pi_ne_zero]
  ring

end DurfeeCCS.Step08
