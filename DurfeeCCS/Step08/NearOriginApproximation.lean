module

public import DurfeeCCS.Step08.NearOriginBudget
public import DurfeeCCS.Step08.NearOriginContour
public import DurfeeCCS.Step08.NearOriginSigns

/-! Lemma 3.1 and Corollary 3.2. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Complex MeasureTheory Set

private theorem nearOrigin_approximation_normalized {n : ℕ} {σ : ℝ}
    (hn : 0 < n) (hσ : 1 ≤ σ) (hr : σ^2 / (n : ℝ) ≤ 1/40)
    (hΔ : nearOriginDelta σ n ≤ 1) :
    ‖(DurfeeCCS.durfeePolynomialComplex n).eval (-((σ^2 / (n : ℝ) : ℝ) : ℂ)^2) -
      nearOriginModel σ n‖ ≤ Real.exp (2*σ) * nearOriginBudget σ n / n := by
  let r : ℝ := σ^2 / (n : ℝ)
  let u : ℝ := σ / (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hσp : 0 < σ := by linarith
  have hrp : 0 < r := by dsimp [r]; positivity
  have hup : 0 < u := by dsimp [u]; positivity
  have hur : u ≤ r := by
    apply div_le_div_of_nonneg_right _ hnR.le
    nlinarith only [mul_nonneg hσp.le (sub_nonneg.mpr hσ)]
  have hu40 : u ≤ 1/40 := hur.trans hr
  have huπ : 4*u ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hσeq : σ^2 = (n : ℝ)*r := by
    dsimp only [r]
    field_simp [hnR.ne']
  have hnu : (n : ℝ)*u = σ := by
    dsimp only [u]
    field_simp [hnR.ne']
  have hδ : r^2/u = nearOriginDelta σ n := nearOrigin_r_sq_div_u hσp.ne' hn
  have hc : nearOriginCentralCoefficient r u =
      nearOriginEpsilon σ n * Real.exp (nearOriginDelta σ n / 2 + nearOriginEpsilon σ n) +
        nearOriginDelta σ n ^ 2 / 8 * Real.exp (nearOriginDelta σ n / 2) := by
    unfold nearOriginCentralCoefficient
    dsimp only
    rw [hδ, show 0.66 * r * u + 0.228 * r * nearOriginDelta σ n + 0.35 * r^2 * u =
      nearOriginEpsilon σ n from nearOrigin_central_epsilon_normalize σ hn]
  let A := ∫ v in Icc (-(4*u)) (4*u), ‖nearOriginCentralError r u v‖
  let B := ∫ v in {v : ℝ | 4*u < |v| ∧ |v| ≤ Real.pi}, ‖nearOriginMiddleError r u v‖
  let C := ∫ v in {v : ℝ | Real.pi < |v|},
    ‖angularAverage (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) - 1)‖
  let D := ∫ v in {v : ℝ | 4*u < |v|}, ‖angularAverage
    (fun θ => exp (nearOriginMainLog r θ (verticalPoint u v)) *
      nearOriginCorrection r θ (verticalPoint u v))‖
  have hA : A ≤ (15*u*Real.exp (r/u)/(r/u)) * nearOriginCentralCoefficient r u :=
    integral_norm_nearOriginCentralError_le hrp hr hup hu40
  have hB : (2 * Real.pi)⁻¹ * B ≤
      Real.exp (r/u/2 + 1.02*(r^2/u)) * (0.48*r^2 + 0.36*(r^3/u)) :=
    integral_norm_nearOriginMiddleError_le hup hur hr (hδ.trans_le hΔ)
  have hC : C ≤ 2*Real.exp (r/u/2)*r^2/Real.pi :=
    integral_norm_nearOriginBase_outer_le hrp.le hup huπ
  have hD : D ≤ Real.pi*Real.exp (r/u/2)*r^3/(2*u) :=
    integral_norm_nearOriginCorrection_outer_le hrp hup
  have hnorm : 0 ≤ (2*Real.pi)⁻¹ := by positivity
  have hsum := add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hA hnorm) hB)
    (mul_le_mul_of_nonneg_left hC hnorm)) (mul_le_mul_of_nonneg_left hD hnorm)
  change ‖(DurfeeCCS.durfeePolynomialComplex n).eval (-(r : ℂ)^2) -
    nearOriginModel σ n‖ ≤ _
  rw [← ofReal_durfeeNegativeValue]
  calc
    _ ≤ Real.exp σ / (2 * Real.pi) * (A+B+C+D) := by
      simpa only [hnu] using
        nearOrigin_contour_difference_le hn hrp hr hup huπ hσeq
    _ = Real.exp σ * ((2*Real.pi)⁻¹*A+(2*Real.pi)⁻¹*B+(2*Real.pi)⁻¹*C+(2*Real.pi)⁻¹*D) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg σ)).trans_eq
      (nearOrigin_budget_normalize hσp hn hc)

/-- The near-origin Bessel approximation in Lemma 3.1. -/
theorem nearOrigin_approximation : NearOriginApproximationStatement := by
  intro n r hn hr₀ hr₁
  dsimp only
  intro hσ hΔ
  let σ := Real.sqrt ((n : ℝ)*r)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hσsq : σ^2 = (n : ℝ)*r := Real.sq_sqrt (by positivity)
  have heq : σ^2 / (n : ℝ) = r := by
    rw [hσsq, mul_comm, mul_div_cancel_right₀ _ hnR.ne']
  have hr : σ^2 / (n : ℝ) ≤ 1/40 := heq.trans_le hr₁
  have ha := nearOrigin_approximation_normalized (σ := σ) hn hσ hr hΔ
  rwa [congrArg Complex.ofReal heq] at ha

/-- The quantitative signed margin at each near-origin sample. -/
theorem nearOrigin_sample_margin {k n : ℕ} (hk : 1 ≤ k) (hn : 6400 ≤ n)
    (hn₂ : 40 * nearOriginSigma k ^ 2 ≤ (n : ℝ))
    (hn₃ : 3 * nearOriginSigma k ^ 3 ≤ (n : ℝ)) :
    3 * Real.exp (2 * nearOriginSigma k) / (400 * (n : ℝ)) <
      originParity k * (DurfeeCCS.durfeePolynomialReal n).eval (nearOriginSample n k) := by
  let σ := nearOriginSigma k
  let r := σ^2 / (n : ℝ)
  obtain ⟨hr₀, hr, hσ, he, hδ⟩ := nearOrigin_sample_parameters hk hn hn₂ hn₃
  have hσ' : 1 ≤ Real.sqrt ((n : ℝ)*r) := by rwa [he]
  have hδ' : nearOriginDelta (Real.sqrt ((n : ℝ)*r)) n ≤ 1 := by rw [he]; linarith
  have hApprox := nearOrigin_approximation (n := n) (r := r) (by omega) hr₀ hr hσ' hδ'
  have hSample : (nearOriginSample n k : ℂ) = -(r : ℂ)^2 := by
    push_cast [nearOriginSample, r, σ, nearOriginSigma]
    ring
  rw [he, ← hSample] at hApprox
  exact nearOrigin_sample_margin_of_local_approximation hk hn hn₂ hn₃ hApprox

/-- The sign at every sample satisfying the thresholds of Corollary 3.2. -/
theorem nearOrigin_sign_at_kpi {k n : ℕ} (hk : 1 ≤ k) (hn : 6400 ≤ n)
    (hn₂ : 40 * nearOriginSigma k ^ 2 ≤ (n : ℝ))
    (hn₃ : 3 * nearOriginSigma k ^ 3 ≤ (n : ℝ)) :
    Real.sign ((DurfeeCCS.durfeePolynomialReal n).eval (nearOriginSample n k)) = (-1 : ℝ)^k :=
  nearOrigin_sign_at_kpi_of_approximation nearOrigin_approximation hk hn hn₂ hn₃

/-- The first eight signs require only the threshold (n ge 6400). -/
theorem nearOrigin_sign_firstEight {k n : ℕ} (hk₁ : 1 ≤ k) (hk₈ : k ≤ 8) (hn : 6400 ≤ n) :
    Real.sign ((DurfeeCCS.durfeePolynomialReal n).eval (nearOriginSample n k)) = (-1 : ℝ)^k :=
  nearOrigin_sign_firstEight_of_approximation nearOrigin_approximation hk₁ hk₈ hn

end DurfeeCCS.Step08
