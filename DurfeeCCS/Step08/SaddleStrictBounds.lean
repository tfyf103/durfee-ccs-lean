module

public import DurfeeCCS.Step08.MinorArcLogBounds
public import DurfeeCCS.Step08.SaddleOuterArc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Strict versions of three margins used in the first saddle estimates. -/

@[expose] public section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06 DurfeeCCS.Step07

/-- The strict Parseval bound on p. 18. -/
theorem angularMean_norm_sq_saddleG_lt {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    angularMean (fun θ => ‖saddleG r θ‖^2) < 2.17*r^2 := by
  rw [angularMean_norm_sq_saddleG r (by rwa [abs_of_pos hr])]
  let c (n : ℕ) : ℝ := 1 / (((n+1 : ℕ) : ℝ)^4)
  let a (n : ℕ) : ℝ := r^(2*(n+1)) / (((n+1 : ℕ) : ℝ)^4)
  have hc : Summable c := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ)/(n : ℝ)^4) 1).2
    hasSum_zeta_four.summable
  have hcz : (∑' n, c n) = Real.pi^4/90 := by
    have h := hasSum_zeta_four.summable.sum_add_tsum_nat_add 1
    rw [hasSum_zeta_four.tsum_eq] at h
    simpa [c] using h
  have hpoint (n : ℕ) : a n ≤ r^2*c n := by
    dsimp [a,c]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one hr.le hr₁ (by omega)) (by positivity)
  have hb : Summable (fun n => r^2*c n) := hc.mul_left _
  have hsum := (hb.of_nonneg_of_le (fun n => by unfold a; positivity) hpoint).tsum_le_tsum hpoint hb
  rw [tsum_mul_left, hcz] at hsum
  have hnum : 2*(Real.pi^4/90) < 2.17 := by
    have hπ := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 4
    linarith only [hπ]
  calc
    _ ≤ 2*(r^2*(Real.pi^4/90)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (2*(Real.pi^4/90))*r^2 := by ring
    _ < _ := mul_lt_mul_of_pos_right hnum (sq_pos_of_pos hr)

/-- The strict real-part bound for the outer vertical Bessel tail. -/
theorem re_saddleG_div_outer_lt {r u v : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hu : 0 < u) (hv : 16*u ≤ |v|) (θ : ℝ) :
    (saddleG r θ / verticalPoint u v).re < 0.127*((saddleS r).re^2/u) := by
  let a := (saddleS r).re
  have hr' : |r| ≤ 1 := by rwa [abs_of_pos hr]
  have ha : r ≤ a^2 := (firstSaddle_coordinates_bounds hr hr₁).1
  have hsq : r^2 ≤ r := by nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr₁)]
  have hR : (saddleG r θ).re ≤ r^2/2 := by
    have h := (saddleG_component_gaps hr hr₁ θ).1
    rw [saddleS_sq] at h
    have hp : 0 ≤ r^2/(1+r^2)*Real.sin θ^2 := by positivity
    linarith only [h, hp, saddlePhaseSquare_re_le_sq_half hr]
  have hI (φ : ℝ) : (saddleG r φ).im ≤ 2*r := by
    have h := (saddleG_component_gaps hr hr₁ φ).2
    rw [saddleS_sq] at h
    have hp : 0 ≤ 2*r/(1+r^2)*(1-Real.cos φ) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one φ))
    linarith only [h, hp, saddlePhaseSquare_im_le_twice hr]
  have habs : |(saddleG r θ).im| ≤ 2*r := by
    apply abs_le.mpr ⟨?_, hI θ⟩
    have h := hI (θ+Real.pi)
    rw [saddleG_add_pi hr', Complex.conj_im] at h
    linarith only [h]
  rw [Complex.div_re, Complex.normSq_apply, verticalPoint_re, verticalPoint_im,
    ← pow_two, ← pow_two, ← add_div]
  apply (div_lt_iff₀ (by positivity)).mpr
  have hRterm : (saddleG r θ).re*u ≤ a^2/2*u :=
    mul_le_mul_of_nonneg_right (hR.trans (by linarith only [hsq,ha])) hu.le
  have hIterm : (saddleG r θ).im*v ≤ 2*a^2*|v| := by
    calc
      _ ≤ |(saddleG r θ).im*v| := le_abs_self _
      _ = |(saddleG r θ).im| * |v| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (habs.trans (by linarith only [ha])) (abs_nonneg v)
  have hratio₀ : (0.5 : ℝ)*u^2+2*u*|v| ≤ (32.5/257)*(u^2+v^2) := by
    nlinarith only [sq_abs v, sq_nonneg (|v|-16*u), sq_pos_of_pos hu,
      mul_nonneg hu.le (sub_nonneg.mpr hv)]
  have hratio := hratio₀.trans_lt (mul_lt_mul_of_pos_right
    (show (32.5/257 : ℝ) < 0.127 by norm_num) (show 0 < u^2+v^2 by positivity))
  have hA : 0 < a^2/u := div_pos (hr.trans_le ha) hu
  have hscaled := mul_lt_mul_of_pos_left hratio hA
  change (saddleG r θ).re*u+(saddleG r θ).im*v < 0.127*(a^2/u)*(u^2+v^2)
  calc
    _ ≤ a^2/2*u+2*a^2*|v| := add_le_add hRterm hIterm
    _ = (a^2/u)*(0.5*u^2+2*u*|v|) := by field_simp; ring
    _ < _ := by linarith only [hscaled]

/-- The strict origin-arc bound on p. 21. -/
theorem norm_pairedLog_zero_arc_lt {r u : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hu : 0 < u) (θ v : ℝ)
    (hs : ∀ k ∈ Finset.range 7,
      0.99*8*u*((k+1 : ℕ) : ℝ) ≤ |Real.sin ((((k+1 : ℕ) : ℝ)*v)/2)|) :
    ‖pairedLog r θ (verticalPoint u v)‖/(r/u) < 0.478 := by
  have hm : (∑ k ∈ Finset.range 7, logScaledMode r θ u v k) ≤
      ∑ k ∈ Finset.range 7, 1/(0.99*8*((k+1 : ℕ) : ℝ)^2) := by
    apply Finset.sum_le_sum
    intro k hk
    refine (logScaledMode_le_sin hr hr₁ hu (by positivity) θ v k (hs k hk)).trans_eq ?_
    simp only [one_pow]
    field_simp
  refine (norm_pairedLog_le_seven hr hr₁ le_rfl hu θ v hm).trans_lt ?_
  norm_num [firstSaddleTail, Finset.sum_range_succ]

end DurfeeCCS.Step08
