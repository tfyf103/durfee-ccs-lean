module

public import DurfeeCCS.Step08.PhaseGap
public import DurfeeCCS.Step08.SaddleBesselAverage
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! The central branch of the saddle square root at the two angular endpoints. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex Set Filter DurfeeCCS.Step06 DurfeeCCS.Step07
open scoped Real Topology Interval

/-- The principal saddle square root extends continuously on the closed central arc. -/
theorem continuousOn_saddleG_sqrt_central {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    ContinuousOn (fun θ => (saddleG r θ).sqrt) (Icc (-(Real.pi/2)) (Real.pi/2)) := by
  have hG : Continuous (saddleG r) := continuous_saddleG (by rwa [abs_of_pos hr])
  let f (θ : ℝ) : ℂ := ↑(Real.sqrt ((‖saddleG r θ‖+(saddleG r θ).re)/2)) +
    ↑(Real.sqrt ((‖saddleG r θ‖-(saddleG r θ).re)/2))*I
  have hf : Continuous f := by unfold f; fun_prop
  refine hf.continuousOn.congr ?_
  intro θ hθ
  have hi := saddleG_im_nonneg_of_cos_nonneg hr hr₁ (Real.cos_nonneg_of_mem_Icc hθ)
  simp only [Complex.sqrt_eq_real_add_ite, ite_eq_left hi, one_mul, f]

/-- The central square root has the stated limits when the endpoint angles are approached
through the interior of the central arc. -/
theorem saddleG_sqrt_central_endpoint_limits {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    Tendsto (fun θ => (saddleG r θ).sqrt) (𝓝[Ioo (-(Real.pi/2)) (Real.pi/2)] (-(Real.pi/2)))
      (𝓝 ((saddleG r (-(Real.pi/2))).sqrt)) ∧
    Tendsto (fun θ => (saddleG r θ).sqrt) (𝓝[Ioo (-(Real.pi/2)) (Real.pi/2)] (Real.pi/2))
      (𝓝 ((saddleG r (Real.pi/2)).sqrt)) := by
  have h := continuousOn_saddleG_sqrt_central hr hr₁
  have hpi : -(Real.pi/2) ≤ Real.pi/2 := by linarith [Real.pi_pos]
  exact ⟨(h (x := -(Real.pi/2)) ⟨le_rfl, hpi⟩).mono Ioo_subset_Icc_self,
    (h (x := Real.pi/2) ⟨hpi, le_rfl⟩).mono Ioo_subset_Icc_self⟩

/-- Lemma 3.3, including the continuous extension of the central square root. -/
theorem lemma33 {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    let s := saddleS r
    let a := s.re
    let ρ := saddleSlope r
    let κ := saddleCurvature r
    let γ := saddleGamma r
    (∀ θ : ℝ, saddleG r θ = ∫ y in 0..r, Complex.log (saddleLogArgument θ y) / (y : ℂ)) ∧
    (∀ θ : ℝ, r^2/(1+r^2) * Real.sin θ^2 ≤ (s^2).re - (saddleG r θ).re ∧
      2*r/(1+r^2) * (1-Real.cos θ) ≤ (s^2).im - (saddleG r θ).im) ∧
    (r ≤ a^2 ∧ a^2 ≤ r*(1+0.282*r) ∧ 1-0.282*r ≤ ρ ∧ ρ ≤ 1 ∧ 16*r/9 ≤ ‖s‖^2) ∧
    (1/((1+r^2)*(1+0.282*r)) ≤ κ ∧ κ ≤ 1 ∧ 0.39 < κ) ∧
    (∀ n : ℕ, 0 < n → 4*Real.pi ≤ Real.sqrt (n*r) →
      let ω := a*Real.sqrt n
      4*Real.pi ≤ ω ∧ 2*Real.exp (2*ω)/(3*Real.pi*n) ≤ saddleAmplitude n r) ∧
    (∀ θ η : ℝ, |θ| ≤ Real.pi/2 → 0 ≤ η →
      let ψ := 1-Real.cos θ
      γ*ψ ≤ ((η-ρ)^2+r*κ*ψ*(2-ψ)+2*κ*η*ψ)/(1+η^2) ∧
       ((η-ρ)^2+r*κ*ψ*(2-ψ)+2*κ*η*ψ)/(1+η^2) ≤ saddleGap r θ η) ∧
    (∀ θ : ℝ, |θ| ≤ Real.pi/2 → ((saddleG r θ).sqrt).re ≤ a*Real.sqrt (1-γ*(1-Real.cos θ))) ∧
    ContinuousOn (fun θ => (saddleG r θ).sqrt) (Icc (-(Real.pi/2)) (Real.pi/2)) ∧
    (∀ θ η : ℝ, 0 ≤ η → (η-ρ)^2/(1+η^2) ≤ saddleGap r θ η) ∧
    (∀ θ η : ℝ, Real.pi/2 < |θ| → |θ| ≤ Real.pi → 0 ≤ η → 1-r/2 ≤ saddleGap r θ η) := by
  exact ⟨saddleG_eq_log_integral hr hr₁, saddleG_component_gaps hr hr₁,
    firstSaddle_coordinates_bounds hr hr₁, saddleCurvature_bounds hr hr₁,
    fun _ hn hf => saddle_frequency_amplitude_lower hn hr hr₁ hf,
    fun _ _ ht he => saddleG_gap_main hr hr₁ ht he,
    fun _ ht => saddleG_sqrt_re_le hr hr₁ ht, continuousOn_saddleG_sqrt_central hr hr₁,
    fun _ _ he => saddleG_gap_all hr hr₁ he, fun _ _ ht ht' he => saddleG_gap_opposite hr hr₁ ht ht' he⟩

end DurfeeCCS.Step08
