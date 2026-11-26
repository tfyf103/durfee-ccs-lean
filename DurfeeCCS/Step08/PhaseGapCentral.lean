module

public import DurfeeCCS.Step08.PhaseGapExpansion
public import DurfeeCCS.Step08.SaddleBesselRadicals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The two central saddle approximations of (33) and the Bessel argument bounds. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06

private theorem saddleG_central_normalization {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hψ : 1-Real.cos θ ≤ 0.3) :
    let s := saddleS r
    let g := saddleG r θ
    let w : ℂ := g/s^2-1
    let ψ := 1-Real.cos θ
    0 < s.re ∧ ‖s‖ ≤ 1.4143*s.re ∧ 0 ≤ ψ ∧ ‖w‖ ≤ 1.34*ψ ∧ s^2*(1+w) = g := by
  let s := saddleS r
  let g := saddleG r θ
  let w := g/s^2-1
  let ψ := 1-Real.cos θ
  change 0 < s.re ∧ ‖s‖ ≤ 1.4143*s.re ∧ 0 ≤ ψ ∧ ‖w‖ ≤ 1.34*ψ ∧ s^2*(1+w) = g
  have ha : 0 < s.re := (saddleS_components hr).1.trans (saddleS_components hr).2
  have hs : s ≠ 0 := by intro h; simp [h] at ha
  have hnorm := (saddle_norm_prefactor_bounds hr hr₁).1.le.trans
    (mul_le_mul_of_nonneg_right (show Real.sqrt 2 ≤ 1.4143 by rw [Real.sqrt_le_iff]; norm_num) ha.le)
  refine ⟨ha, hnorm, sub_nonneg.mpr (Real.cos_le_one θ),
    (saddleG_normalized_displacement hr hr₁ hψ).1, ?_⟩
  unfold w
  rw [add_comm 1, sub_add_cancel, mul_div_cancel₀ _ (pow_ne_zero 2 hs)]

/-- The central square-root ratio lies in the open right half-plane. -/
theorem saddleG_central_sqrt_ratio {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hψ : 1-Real.cos θ ≤ 0.3) :
    let s := saddleS r
    let g := saddleG r θ
    let w : ℂ := g/s^2-1
    g.sqrt/s = (1+w).sqrt ∧ 0 < (g.sqrt/s).re := by
  let s := saddleS r
  let g := saddleG r θ
  let w := g/s^2-1
  change g.sqrt/s = (1+w).sqrt ∧ 0 < (g.sqrt/s).re
  obtain ⟨ha, hnorm, hp0, hw, hg⟩ := saddleG_central_normalization hr hr₁ hψ
  change 0 < s.re at ha
  have hs : s ≠ 0 := by intro h; simp [h] at ha
  have hnorm' : ‖s‖ ≤ 1.415*s.re := by linarith only [ha, hnorm]
  have hg' : s^2*(1+w) = g := hg
  have hqr : g.sqrt/s = (1+w).sqrt := by
    rw [← hg', saddleCentral_sqrt_mul ha hnorm' hp0 hψ hw,
      mul_comm s, mul_div_cancel_right₀ _ hs]
  refine ⟨hqr, ?_⟩
  rw [hqr, principalSqrt_re_eq]
  have hw₁ : ‖w‖ ≤ 0.402 := (saddleG_normalized_displacement hr hr₁ hψ).2
  have hneg := Complex.re_le_norm (-w)
  rw [Complex.neg_re, norm_neg] at hneg
  apply Real.sqrt_pos_of_pos
  simp only [Complex.add_re, Complex.one_re]
  linarith only [norm_nonneg (1+w), hneg, hw₁]

/-- The two saddle approximations in (33) for the actual phase and amplitude. -/
theorem saddleG_central_errors {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hψ : 1-Real.cos θ ≤ 0.3) :
    let s := saddleS r
    let g := saddleG r θ
    let ψ := 1-Real.cos θ
    ‖2*(g.sqrt-s)/(s.re : ℂ) + 2*((r : ℂ)*I/(1+(r : ℂ)*I))*(ψ : ℂ)/((s.re : ℂ)*s)‖ ≤ 2.46*ψ^2 ∧
      ‖(g.sqrt/s).sqrt/(Real.sqrt (1-ψ/2) : ℂ)-1‖ ≤ 0.87*ψ := by
  let s := saddleS r
  let g := saddleG r θ
  let ψ := 1-Real.cos θ
  let L := 2*((r : ℂ)*I/(1+(r : ℂ)*I))
  change ‖2*(g.sqrt-s)/(s.re : ℂ) + L*(ψ : ℂ)/((s.re : ℂ)*s)‖ ≤ 2.46*ψ^2 ∧
    ‖(g.sqrt/s).sqrt/(Real.sqrt (1-ψ/2) : ℂ)-1‖ ≤ 0.87*ψ
  obtain ⟨ha, hnorm, hp0, hw, _⟩ := saddleG_central_normalization hr hr₁ hψ
  have hnorm' : ‖s‖ ≤ 1.415*s.re := by linarith only [ha, hnorm]
  have hR := saddleG_log_linear_remainder hr hr₁ (hψ.trans_lt (by norm_num))
  have hR' : ‖g-s^2+L*(ψ : ℂ)‖ ≤ r*ψ^2/(1-ψ) := by
    rw [← norm_neg (g-s^2+L*(ψ : ℂ))]
    convert hR using 2
    unfold L ψ g s
    ring
  have hqr : g.sqrt/s = (1+(g/s^2-1)).sqrt := (saddleG_central_sqrt_ratio hr hr₁ hψ).1
  rw [hqr]
  exact ⟨saddleCentral_exponent_error ha hnorm' (saddle_norm_prefactor_bounds hr hr₁).2.2.1 hp0 hψ hw hR',
    saddleCentral_amplitude_error hp0 hψ hw⟩

/-- The central Bessel argument bounds on p. 15. -/
theorem saddleG_central_bessel_arguments {r θ v : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hψ : 1-Real.cos θ ≤ 0.3) (hv : 0 < v) :
    let s := saddleS r
    let z := 2*(v : ℂ)*(saddleG r θ).sqrt
    ‖z‖ ≤ 3.35*(s.re*v) ∧ 1.35*(s.re*v) ≤ z.re := by
  obtain ⟨ha, hs, hp0, hw, hg⟩ := saddleG_central_normalization hr hr₁ hψ
  have h := saddleCentral_bessel_arguments ha hs hp0 hψ hw hv
  dsimp only at h
  rw [hg] at h
  exact h

end DurfeeCCS.Step08
