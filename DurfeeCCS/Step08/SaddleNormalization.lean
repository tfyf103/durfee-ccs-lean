module

public import DurfeeCCS.Step07.FirstSaddleRanges
public import DurfeeCCS.Step06.Saddle
public import DurfeeCCS.Step08.NearOriginLaplace

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Normalization of the saddle scale and amplitude in (24). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open DurfeeCCS.Step06 DurfeeCCS.Step07

def saddleOmega (n : ℕ) (r : ℝ) : ℝ := (saddleS r).re * Real.sqrt n

def saddleU (n : ℕ) (r : ℝ) : ℝ := (saddleS r).re / Real.sqrt n

def saddleKappa (r : ℝ) : ℝ := r / ((1 + r ^ 2) * (saddleS r).re ^ 2)

theorem saddleOmega_pos {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    0 < saddleOmega n r := by
  obtain ⟨hb, hab⟩ := saddleS_components hr
  exact mul_pos (hb.trans hab) (Real.sqrt_pos.mpr (by exact_mod_cast hn))

theorem saddleU_pos {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    0 < saddleU n r := by
  obtain ⟨hb, hab⟩ := saddleS_components hr
  exact div_pos (hb.trans hab) (Real.sqrt_pos.mpr (by exact_mod_cast hn))

theorem saddleU_mul_n {n : ℕ} (hn : 0 < n) (r : ℝ) :
    (n : ℝ) * saddleU n r = saddleOmega n r := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnp
  unfold saddleU saddleOmega
  calc
    _ = (Real.sqrt (n : ℝ)) ^ 2 * ((saddleS r).re / Real.sqrt n) := by rw [Real.sq_sqrt hnp.le]
    _ = _ := by field_simp

theorem saddleU_mul_omega {n : ℕ} (hn : 0 < n) (r : ℝ) :
    saddleU n r * saddleOmega n r = (saddleS r).re ^ 2 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnp
  unfold saddleU saddleOmega
  field_simp

theorem saddleOmega_sq {n : ℕ} (r : ℝ) :
    saddleOmega n r ^ 2 = (n : ℝ) * (saddleS r).re ^ 2 := by
  rw [saddleOmega, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_comm]

theorem r_div_saddleU_le_saddleOmega {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) : r / saddleU n r ≤ saddleOmega n r := by
  rw [div_le_iff₀ (saddleU_pos hn hr), mul_comm, saddleU_mul_omega hn]
  exact (firstSaddle_coordinates_bounds hr hr₁).1

theorem n_mul_sq_div_saddleU_le_omega_cube {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) :
    (n : ℝ) * r ^ 2 / saddleU n r ≤ saddleOmega n r ^ 3 := by
  have hlo := (firstSaddle_coordinates_bounds hr hr₁).1
  have hu := saddleU_pos hn hr
  have hω := saddleOmega_pos hn hr
  have hnr : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hr2 := pow_le_pow_left₀ hr.le hlo 2
  calc
    _ ≤ (n : ℝ) * ((saddleS r).re ^ 2) ^ 2 / saddleU n r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 hnr) hu.le
    _ = saddleOmega n r ^ 3 := by
      apply (div_eq_iff hu.ne').mpr
      calc
        _ = ((n : ℝ) * (saddleS r).re ^ 2) * (saddleS r).re ^ 2 := by ring
        _ = _ := by rw [← saddleOmega_sq r, ← saddleU_mul_omega hn r]; ring

theorem norm_exp_nat_verticalPoint (n : ℕ) (u v : ℝ) :
    ‖Complex.exp ((n : ℂ) * verticalPoint u v)‖ = Real.exp ((n : ℝ) * u) := by
  simp [Complex.norm_exp, Complex.mul_re]

theorem saddleOmega_ge_sqrt_mul {n : ℕ} {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    Real.sqrt ((n : ℝ) * r) ≤ saddleOmega n r := by
  obtain ⟨hb, hab⟩ := saddleS_components hr
  have ha := (Real.sqrt_le_iff).mpr ⟨(hb.trans hab).le, (firstSaddle_coordinates_bounds hr hr₁).1⟩
  rw [mul_comm (n : ℝ) r, Real.sqrt_mul hr.le]
  exact mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)

theorem saddleKappa_enclosure {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    1 / ((1 + r ^ 2) * (1 + 0.282 * r)) ≤ saddleKappa r ∧
      saddleKappa r ≤ 1 ∧ 0.39 < saddleKappa r := by
  let a := (saddleS r).re
  obtain ⟨hb, hab⟩ := saddleS_components hr
  have ha : 0 < a := hb.trans hab
  obtain ⟨hlo, hhi, _, _, _⟩ := firstSaddle_coordinates_bounds hr hr₁
  change r ≤ a ^ 2 at hlo
  change a ^ 2 ≤ r * (1 + 0.282 * r) at hhi
  have hp : 0 < 1 + r ^ 2 := by positivity
  have hp' : 0 < (1 + r ^ 2) * (1 + 0.282 * r) := by positivity
  have hlow : 1 / ((1 + r ^ 2) * (1 + 0.282 * r)) ≤ saddleKappa r := by
    change 1 / _ ≤ r / ((1 + r ^ 2) * a ^ 2)
    rw [div_le_div_iff₀ hp' (mul_pos hp (sq_pos_of_pos ha)), one_mul]
    have ht := mul_le_mul_of_nonneg_left hhi hp.le
    linarith only [show (1 + r ^ 2) * (r * (1 + 0.282 * r)) =
      r * ((1 + r ^ 2) * (1 + 0.282 * r)) by ring, ht]
  have hupper : saddleKappa r ≤ 1 := by
    apply (div_le_one (mul_pos hp (sq_pos_of_pos ha))).mpr
    exact hlo.trans (le_mul_of_one_le_left (sq_nonneg _) (by linarith [sq_nonneg r]))
  refine ⟨hlow, hupper, lt_of_lt_of_le ?_ hlow⟩
  apply (lt_div_iff₀ hp').mpr
  have hs : r ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hr.le hr₁ 2
  have ht : (1 + r ^ 2) * (1 + 0.282 * r) ≤ 2 * 1.282 :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  linarith

theorem saddleAmplitude_lower {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    2 * Real.exp (2 * saddleOmega n r) / (3 * Real.pi * n) ≤ saddleAmplitude n r := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsr := Real.sqrt_pos.mpr hr
  have hsq := (firstSaddle_coordinates_bounds hr hr₁).2.2.2.2
  have hnorm : (4 / 3 : ℝ) * Real.sqrt r ≤ ‖saddleS r‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hr.le]
    linarith
  have hroot : 1 ≤ (1 + r ^ 2) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by linarith [sq_nonneg r]) (by norm_num)
  have hb := hnorm.trans (le_mul_of_one_le_right (norm_nonneg _) hroot)
  unfold saddleAmplitude saddleOmega
  rw [← mul_assoc 2 (saddleS r).re (Real.sqrt n)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ 3 * Real.pi * n * Real.exp (2 * (saddleS r).re * Real.sqrt n) by positivity)
  linarith only [h, show (4 / 3 : ℝ) * Real.sqrt r *
      (3 * Real.pi * n * Real.exp (2 * (saddleS r).re * Real.sqrt n)) =
      (2 * Real.exp (2 * (saddleS r).re * Real.sqrt n)) * (2 * Real.pi * n * Real.sqrt r) by ring,
    show ‖saddleS r‖ * (1 + r ^ 2) ^ (1 / 4 : ℝ) *
      (3 * Real.pi * n * Real.exp (2 * (saddleS r).re * Real.sqrt n)) =
      ‖saddleS r‖ * (1 + r ^ 2) ^ (1 / 4 : ℝ) *
        Real.exp (2 * (saddleS r).re * Real.sqrt n) * (3 * Real.pi * n) by ring]

theorem saddleU_lt_bound {n : ℕ} (hn : 6400 ≤ n) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    saddleU n r < 0.01416 := by
  refine (firstSaddleRadius_leU0 hn hr hr₁ le_rfl).trans_lt ?_
  unfold firstSaddleU0
  exact (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Normalize a bound of size `C r² exp(μω)/u` on a vertical integral. -/
theorem saddle_scale_weighted_error_le {n : ℕ} (hn : 0 < n) {r C μ : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hC : 0 ≤ C) :
    let ω := saddleOmega n r
    Real.exp ω / (2 * Real.pi) *
      (C * r ^ 2 / saddleU n r * Real.exp (μ * ω)) ≤
      saddleAmplitude n r * (3 * C / 4 * ω ^ 3 * Real.exp (-(1 - μ) * ω)) := by
  dsimp only
  let ω := saddleOmega n r
  have hw : 0 < ω := saddleOmega_pos hn hr
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnp : (n : ℝ) ≠ 0 := hn'.ne'
  have hs : r ^ 2 / saddleU n r ≤ ω ^ 3 / (n : ℝ) := by
    apply (le_div_iff₀ hn').mpr
    calc
      _ = (n : ℝ) * r ^ 2 / saddleU n r := by ring
      _ ≤ _ := n_mul_sq_div_saddleU_le_omega_cube hn hr hr₁
  change Real.exp ω / (2 * Real.pi) *
      (C * r ^ 2 / saddleU n r * Real.exp (μ * ω)) ≤
    saddleAmplitude n r * (3 * C / 4 * ω ^ 3 * Real.exp (-(1 - μ) * ω))
  have hp : 0 ≤ 3 * C / 4 * ω ^ 3 * Real.exp (-(1 - μ) * ω) := by positivity
  calc
    _ ≤ Real.exp ω / (2 * Real.pi) *
        (C * (ω ^ 3 / (n : ℝ)) * Real.exp (μ * ω)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC) (Real.exp_nonneg _)
    _ = (2 * Real.exp (2 * ω) / (3 * Real.pi * (n : ℝ))) *
        (3 * C / 4 * ω ^ 3 * Real.exp (-(1 - μ) * ω)) := by
      have hx : Real.exp ω * Real.exp (μ * ω) =
          Real.exp (2 * ω) * Real.exp (-(1 - μ) * ω) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = C * (ω ^ 3 / (2 * Real.pi * (n : ℝ))) *
            (Real.exp ω * Real.exp (μ * ω)) := by field_simp <;> ring
        _ = _ := by rw [hx]; field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (saddleAmplitude_lower hn hr hr₁) hp

end DurfeeCCS.Step08
