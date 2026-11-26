module

public import DurfeeCCS.Step06.BesselSeries
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Convex

/-! Derivatives and low-order recurrences for the Bessel series. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step06

open Nat

private theorem deriv_term (m k : ℕ) (z : ℂ) :
    HasDerivAt (besselITerm m k)
      ((↑(2 * k + m) : ℂ) * (z / 2) ^ (2 * k + m - 1) / 2 /
        ((k.factorial : ℂ) * ((k + m).factorial : ℂ))) z := by
  have h := (((hasDerivAt_id z).div_const (2 : ℂ)).pow (2 * k + m)).div_const
    ((k.factorial : ℂ) * ((k + m).factorial : ℂ))
  change HasDerivAt (fun w : ℂ => (w / 2) ^ (2 * k + m) /
    ((k.factorial : ℂ) * ((k + m).factorial : ℂ))) _ z
  simpa only [id_eq, Pi.pow_apply, div_eq_mul_inv, one_mul] using h

private theorem norm_term_le (m k : ℕ) {w : ℂ} {r : ℝ} (hr : 0 ≤ r) (hw : ‖w‖ ≤ r) :
    ‖besselITerm m k w‖ ≤ ‖besselITerm m k (r : ℂ)‖ := by
  simp only [besselITerm, norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr]
  gcongr

private theorem deriv_tsum_ball (f d : ℕ → ℂ → ℂ) (z : ℂ) {M : ℕ → ℝ}
    (hM : Summable M) (h : ∀ k w, HasDerivAt (f k) (d k w) w)
    (hbound : ∀ k w, ‖w‖ ≤ ‖z‖ + 1 → ‖d k w‖ ≤ M k)
    (hs : Summable fun k => f k z) :
    HasDerivAt (fun w => ∑' k, f k w) (∑' k, d k z) z := by
  have hz : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
    simp [Metric.mem_ball, dist_zero_right]
  refine hasDerivAt_tsum_of_isPreconnected hM Metric.isOpen_ball
    (convex_ball (0 : ℂ) (‖z‖ + 1)).isPreconnected (fun k w _ => h k w)
    (fun k w hw => hbound k w ?_) hz hs hz
  exact (by simpa [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < ‖z‖ + 1).le

private theorem deriv_term_zero_succ (k : ℕ) (z : ℂ) :
    HasDerivAt (besselITerm 0 (k + 1)) (besselITerm 1 k z) z := by
  convert deriv_term 0 (k + 1) z using 1
  rw [besselITerm, show 2 * (k + 1) + 0 - 1 = 2 * k + 1 by omega,
    add_zero (k + 1), Nat.factorial_succ k]
  push_cast
  field_simp [show (k.factorial : ℂ) ≠ 0 by exact_mod_cast k.factorial_ne_zero]
  ring

theorem hasDerivAt_besselI_zero (z : ℂ) : HasDerivAt (besselI 0) (besselI 1 z) z := by
  have h := deriv_tsum_ball (fun k => besselITerm 0 (k + 1)) (fun k => besselITerm 1 k) z
    (summable_norm_besselITerm 1 ((‖z‖ + 1 : ℝ) : ℂ)) deriv_term_zero_succ
    (fun k w hw => norm_term_le 1 k (by positivity) hw)
    ((summable_nat_add_iff 1).2 (summable_besselITerm 0 z))
  have heq : besselI 0 = fun w => 1 + ∑' k, besselITerm 0 (k + 1) w := by
    funext w
    rw [besselI, (summable_besselITerm 0 w).tsum_eq_zero_add]
    simp [besselITerm]
  rw [heq]
  exact h.const_add 1

theorem hasDerivAt_besselJ_zero (z : ℂ) : HasDerivAt (besselJ 0) (-besselJ 1 z) z := by
  have h := (hasDerivAt_besselI_zero (Complex.I * z)).comp z
    ((hasDerivAt_id z).const_mul Complex.I)
  change HasDerivAt (fun w => besselI 0 (Complex.I * w)) _ z at h
  have heq : (fun w => besselI 0 (Complex.I * w)) = besselJ 0 := by
    funext w
    simp [besselI_mul_I]
  rw [heq] at h
  convert h using 1
  rw [besselI_mul_I, pow_one, mul_one, mul_right_comm, ← pow_two, Complex.I_sq, neg_one_mul]

private def shiftedTwo (k : ℕ) (z : ℂ) : ℂ :=
  match k with
  | 0 => 0
  | k + 1 => besselITerm 2 k z

private theorem summable_shiftedTwo (z : ℂ) : Summable (fun k => shiftedTwo k z) := by
  apply (summable_nat_add_iff 1).1
  exact summable_besselITerm 2 z

private theorem summable_norm_shiftedTwo (z : ℂ) : Summable (fun k => ‖shiftedTwo k z‖) := by
  apply (summable_nat_add_iff 1).1
  exact summable_norm_besselITerm 2 z

private theorem tsum_shiftedTwo (z : ℂ) : (∑' k, shiftedTwo k z) = besselI 2 z := by
  rw [(summable_shiftedTwo z).tsum_eq_zero_add]
  simp [shiftedTwo, besselI]

private theorem deriv_term_one (k : ℕ) (z : ℂ) :
    HasDerivAt (besselITerm 1 k) ((besselITerm 0 k z + shiftedTwo k z) / 2) z := by
  convert deriv_term 1 k z using 1
  rcases k with _ | k
  · norm_num [besselITerm, shiftedTwo]
  · simp only [shiftedTwo, besselITerm, add_zero, Nat.cast_add, Nat.cast_one]
    rw [show 2 * (k + 1) + 1 - 1 = 2 * k + 2 by omega,
      show 2 * (k + 1) = 2 * k + 2 by omega, Nat.factorial_succ (k + 1), Nat.factorial_succ k]
    push_cast
    have hk : (2 + (k : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + k ≠ 0 by omega)
    field_simp [show (k.factorial : ℂ) ≠ 0 by exact_mod_cast k.factorial_ne_zero, hk]
    ring_nf
    field_simp [hk]
    ring

theorem hasDerivAt_besselI_one (z : ℂ) :
    HasDerivAt (besselI 1) ((besselI 0 z + besselI 2 z) / 2) z := by
  let R : ℝ := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hM := ((summable_norm_besselITerm 0 (R : ℂ)).add
    (summable_norm_shiftedTwo (R : ℂ))).div_const 2
  have h := deriv_tsum_ball (besselITerm 1) (fun k w => (besselITerm 0 k w + shiftedTwo k w) / 2)
    z hM deriv_term_one (fun k w hw => ?_) (summable_besselITerm 1 z)
  · unfold besselI
    rw [tsum_div_const, (summable_besselITerm 0 z).tsum_add (summable_shiftedTwo z),
      tsum_shiftedTwo] at h
    exact h
  · have h2 : ‖shiftedTwo k w‖ ≤ ‖shiftedTwo k (R : ℂ)‖ := by
      rcases k with _ | k
      · rfl
      · exact norm_term_le 2 k hR hw
    calc
      _ ≤ (‖besselITerm 0 k w‖ + ‖shiftedTwo k w‖) / 2 := by
        simpa [norm_div] using div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ _ := by gcongr; exact norm_term_le 0 k hR hw

private theorem recurrence_term (k : ℕ) (z : ℂ) :
    z * besselITerm 0 k z = 2 * besselITerm 1 k z + z * shiftedTwo k z := by
  rcases k with _ | k
  · norm_num [besselITerm, shiftedTwo]
    ring
  · simp only [besselITerm, shiftedTwo, add_zero]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, Nat.factorial_succ (k + 1), Nat.factorial_succ k]
    push_cast
    rw [pow_succ (z / 2) (2 * k + 2)]
    have hk : (2 + (k : ℂ)) ≠ 0 := by exact_mod_cast (show 2 + k ≠ 0 by omega)
    field_simp [show (k.factorial : ℂ) ≠ 0 by exact_mod_cast k.factorial_ne_zero, hk]
    ring_nf
    field_simp [hk]
    ring

theorem besselI_recurrence (z : ℂ) : z * besselI 0 z = 2 * besselI 1 z + z * besselI 2 z := by
  rw [← tsum_shiftedTwo, besselI, besselI, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_besselITerm 1 z).mul_left (2 : ℂ)).tsum_add
      ((summable_shiftedTwo z).mul_left z)]
  exact tsum_congr (fun k => recurrence_term k z)

theorem besselJ_two_eq (z : ℂ) (hz : z ≠ 0) :
    besselJ 2 z = 2 * besselJ 1 z / z - besselJ 0 z := by
  have h := besselI_recurrence (Complex.I * z)
  simp only [besselI_mul_I, pow_zero, one_mul, pow_one, Complex.I_sq, neg_one_mul] at h
  have hc : z * besselJ 0 z = 2 * besselJ 1 z - z * besselJ 2 z := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h
  field_simp
  linear_combination hc

theorem hasDerivAt_besselI_one_of_ne_zero (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (besselI 1) (besselI 0 z - besselI 1 z / z) z := by
  convert hasDerivAt_besselI_one z using 1
  field_simp
  linear_combination besselI_recurrence z

end DurfeeCCS.Step06
