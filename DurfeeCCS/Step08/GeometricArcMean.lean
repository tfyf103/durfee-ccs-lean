module

public import DurfeeCCS.Step08.AngularMeans
public import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The geometric Fourier mean used for the logarithmic minor arc. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06

/-- Mean of the squared geometric kernel at every positive integer frequency. -/
theorem angularMean_geom_kernel {q : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1)
    {k : ℕ} (hk : k ≠ 0) :
    angularMean (fun v => (‖(1 : ℂ) - (q : ℂ) * exp ((k : ℂ) * I * (v : ℂ))‖ ^ 2)⁻¹) =
      (1 - q ^ 2)⁻¹ := by
  let z (v : ℝ) := (q : ℂ) * exp ((k : ℂ) * I * (v : ℂ))
  let G (n : ℕ) (v : ℝ) := z v ^ n
  let F (n : ℕ) (v : ℝ) := starRingEnd ℂ (G n v)
  have hz (v : ℝ) : ‖z v‖ = q := by
    have he : (k : ℂ) * I * (v : ℂ) = ((((k : ℝ) * v : ℝ) : ℂ) * I) := by push_cast; ring
    dsimp only [z]
    rw [norm_mul, he, norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hq₀]
  have hg (n : ℕ) : Continuous (G n) := by unfold G z; fun_prop
  have hf (n : ℕ) : Continuous (F n) := Complex.continuous_conj.comp (hg n)
  have hG (n : ℕ) (v : ℝ) : ‖G n v‖ ≤ q ^ n := by simp only [G, norm_pow, hz, le_rfl]
  have hF (n : ℕ) (v : ℝ) : ‖F n v‖ ≤ q ^ n := by simpa [F] using hG n v
  have horth (i j : ℕ) : (∫ v in -Real.pi..Real.pi, F i v * G j v) =
      if j = i then (2 * Real.pi : ℂ) * ((q ^ 2) ^ i : ℝ) else 0 := by
    let m : ℤ := (k : ℤ) * ((j : ℤ) - (i : ℤ))
    have hterm (v : ℝ) : F i v * G j v =
        (q : ℂ) ^ (i + j) * exp ((m : ℂ) * I * (v : ℂ)) := by
      have hg' (n : ℕ) : G n v =
          (q : ℂ) ^ n * exp ((n : ℂ) * ((k : ℂ) * I * (v : ℂ))) := by
        simp only [G, z, mul_pow, Complex.exp_nat_mul]
      rw [show F i v = starRingEnd ℂ (G i v) from rfl, hg', hg', map_mul, map_pow,
        Complex.conj_ofReal, ← Complex.exp_conj]
      simp only [map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]
      rw [mul_mul_mul_comm, ← pow_add, ← Complex.exp_add]
      congr 2
      dsimp only [m]
      push_cast
      ring
    simp_rw [hterm]
    rw [intervalIntegral.integral_const_mul, integral_integer_mode m]
    by_cases hij : j = i
    · subst j
      simp only [m, sub_self, mul_zero, ite_true, Complex.ofReal_pow]
      rw [← pow_mul, Nat.two_mul, mul_comm]
    · have hji : (j : ℤ) - (i : ℤ) ≠ 0 := by omega
      have hm : m ≠ 0 := mul_ne_zero (by exact_mod_cast hk) hji
      rw [ite_eq_right hm, ite_eq_right hij, mul_zero]
  have hs := summable_geometric_of_lt_one hq₀ hq
  have h := integral_mul_tsum_of_orthogonality hf hg hs hs hF hG _ horth
  have hGsum (v : ℝ) : (∑' i, G i v) = (1 - z v)⁻¹ :=
    tsum_geometric_of_norm_lt_one (by rwa [hz])
  have hn (v : ℝ) : ((((‖1 - z v‖ ^ 2)⁻¹ : ℝ)) : ℂ) =
      (∑' i, F i v) * (∑' i, G i v) := by
    rw [← Complex.conj_tsum, hGsum, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      norm_inv, inv_pow]
  apply Complex.ofReal_injective
  rw [← angularAverage_ofReal]
  change angularAverage (fun v => (((‖1 - z v‖ ^ 2)⁻¹ : ℝ) : ℂ)) = _
  simp_rw [hn]
  unfold angularAverage
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hq₂ : q ^ 2 < 1 := pow_lt_one₀ hq₀ hq (by decide : 2 ≠ 0)
  rw [h, tsum_mul_left, ← Complex.ofReal_tsum,
    tsum_geometric_of_lt_one (sq_nonneg _) hq₂, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

/-- The exact angular mean of the squared hyperbolic-sine denominator. -/
theorem angularMean_inv_norm_sinh_sq {u : ℝ} (hu : 0 < u) {k : ℕ} (hk : k ≠ 0) :
    angularMean (fun v => (‖2 * sinh ((k : ℂ) * ((u : ℂ) + (v : ℂ) * I) / 2)‖ ^ 2)⁻¹) =
      (2 * Real.sinh ((k : ℝ) * u))⁻¹ := by
  let q : ℝ := Real.exp (-(k : ℝ) * u)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  have hq₀ : 0 < q := Real.exp_pos _
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hk' hu])
  have heq (v : ℝ) :
      (‖2 * sinh ((k : ℂ) * ((u : ℂ) + (v : ℂ) * I) / 2)‖ ^ 2)⁻¹ =
        q * (‖(1 : ℂ) - (q : ℂ) * exp ((k : ℂ) * I * (-(v : ℝ) : ℂ))‖ ^ 2)⁻¹ := by
    let w : ℂ := (k : ℂ) * ((u : ℂ) + (v : ℂ) * I) / 2
    have hfac : 2 * sinh w = exp w * (1 - exp (-2 * w)) := by
      rw [Complex.sinh, mul_sub, mul_one, ← Complex.exp_add, show w + -2 * w = -w by ring]
      ring
    have harg : -2 * w = (↑(-(k : ℝ) * u) : ℂ) + (k : ℂ) * I * (-(v : ℝ) : ℂ) := by
      dsimp only [w]
      push_cast
      ring
    have hre : 2 * w.re = (k : ℝ) * u := by
      dsimp only [w]
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
      simp [Complex.mul_re]
      ring
    change (‖2 * sinh w‖ ^ 2)⁻¹ = _
    rw [hfac, norm_mul, mul_pow, mul_inv, Complex.norm_exp, ← Real.exp_nat_mul, Nat.cast_ofNat, hre,
      ← Real.exp_neg, harg, Complex.exp_add, ← Complex.ofReal_exp]
    simp only [q, neg_mul]
  simp_rw [heq]
  unfold angularMean
  rw [intervalIntegral.integral_const_mul]
  let f (v : ℝ) := (‖(1 : ℂ) - (q : ℂ) * exp ((k : ℂ) * I * (v : ℂ))‖ ^ 2)⁻¹
  simp only [← Complex.ofReal_neg]
  change (2 * Real.pi)⁻¹ * (q * ∫ v in -Real.pi..Real.pi, f (-v)) = _
  rw [intervalIntegral.integral_comp_neg f]
  simp only [neg_neg]
  rw [mul_left_comm]
  change q * angularMean (fun v =>
    (‖(1 : ℂ) - (q : ℂ) * exp ((k : ℂ) * I * (v : ℂ))‖ ^ 2)⁻¹) = _
  rw [angularMean_geom_kernel hq₀.le hq hk]
  rw [Real.sinh_eq, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  have hq' : Real.exp ((k : ℝ) * u) = q⁻¹ := by simp [q, ← Real.exp_neg, neg_mul]
  rw [hq', show Real.exp (-((k : ℝ) * u)) = q by unfold q; rw [neg_mul]]
  have hden : 0 < 1 - q ^ 2 := sub_pos.mpr (pow_lt_one₀ hq₀.le hq (by decide : 2 ≠ 0))
  field_simp [hq₀.ne', hden.ne']

end DurfeeCCS.Step08
