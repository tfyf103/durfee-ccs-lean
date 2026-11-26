module

public import DurfeeCCS.Step06.BesselDerivative
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Choose.Cast

/-! The Bessel Cauchy product used in equations (16) and (17). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Finset Nat Polynomial DurfeeCCS.Step06

private theorem factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-- The coefficient obtained by multiplying the two Bessel series, after the common power. -/
def besselConvolutionCoeff (ν m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℂ) ^ j / ((j.factorial : ℂ) * ((m-j).factorial : ℂ) *
      ((j+ν).factorial : ℂ) * ((m-j+ν).factorial : ℂ))

private theorem besselConvolutionCoeff_eq_zero_of_odd (ν m : ℕ) (hm : Odd m) :
    besselConvolutionCoeff ν m = 0 := by
  unfold besselConvolutionCoeff
  have hs := Finset.sum_range_reflect (fun j : ℕ => (-1 : ℂ) ^ j /
    ((j.factorial : ℂ) * ((m-j).factorial : ℂ) *
      ((j+ν).factorial : ℂ) * ((m-j+ν).factorial : ℂ))) (m + 1)
  rw [Nat.add_sub_cancel] at hs
  have hterm (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      (-1 : ℂ) ^ (m-j) /
        (((m-j).factorial : ℂ) * ((m-(m-j)).factorial : ℂ) *
          ((m-j+ν).factorial : ℂ) * ((m-(m-j)+ν).factorial : ℂ)) =
      - ((-1 : ℂ) ^ j /
        ((j.factorial : ℂ) * ((m-j).factorial : ℂ) *
          ((j+ν).factorial : ℂ) * ((m-j+ν).factorial : ℂ))) := by
    have hjm : j ≤ m := by simpa using hj
    have hsign : (-1 : ℂ) ^ (m-j) = -((-1 : ℂ) ^ j) := by
      have hmul : (-1 : ℂ) ^ j * (-1 : ℂ) ^ (m-j) = -1 := by
        rw [← pow_add, Nat.add_sub_of_le hjm, hm.neg_pow, one_pow]
      have hsquare : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
        rw [← mul_pow]; simp
      linear_combination ((-1 : ℂ) ^ j) * hmul - ((-1 : ℂ) ^ (m-j)) * hsquare
    rw [hsign, Nat.sub_sub_self hjm, neg_div]
    congr 2
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hs
  linear_combination -hs / 2

private theorem coeff_sub_X_sq_pow (m k : ℕ) :
    ((X ^ 2 + C (-1) : Polynomial ℂ) ^ m).coeff k =
      if Even k then (-1 : ℂ) ^ (m - k / 2) * (m.choose (k / 2) : ℂ) else 0 := by
  rw [add_pow, Polynomial.finsetSum_coeff]
  simp only [← pow_mul, ← Polynomial.C_pow, ← Polynomial.C_eq_natCast,
    mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
  split_ifs with hk
  · obtain ⟨a, rfl⟩ := hk
    have hd : (a+a)/2 = a := by omega
    rw [hd, Finset.sum_eq_single a]
    · simp [two_mul]
    · intro b hb hne
      have hne' : a+a ≠ 2*b := by omega
      simp [hne']
    · intro ha
      have hma : m < a := by simpa using ha
      simp [two_mul, Nat.choose_eq_zero_of_lt hma]
  · apply Finset.sum_eq_zero
    intro a _
    have hn : k ≠ 2*a := by intro he; apply hk; exact ⟨a, by omega⟩
    simp [hn]

private theorem besselConvolutionCoeff_polynomial (ν m : ℕ) (hm : Even m) :
    besselConvolutionCoeff ν m =
      (((X ^ 2 + C (-1) : Polynomial ℂ) ^ m) * (X + 1) ^ (2*ν)).coeff (m+ν) /
        ((m.factorial : ℂ) * ((m+2*ν).factorial : ℂ)) := by
  have hfactor : ((X ^ 2 + C (-1) : Polynomial ℂ) ^ m) * (X + 1) ^ (2*ν) =
      ((X + C (-1)) ^ m) * (X + 1) ^ (m+2*ν) := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    congr 2
    rw [C_neg, C_1]
    ring
  rw [hfactor, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_div]
  simp only [Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_add_one_pow]
  unfold besselConvolutionCoeff
  trans ∑ j ∈ Finset.range (m + 1),
    (((-1 : ℂ) ^ (m - j) * (m.choose j : ℂ)) * ((m + 2 * ν).choose (m + ν - j) : ℂ)) /
      ((m.factorial : ℂ) * ((m + 2 * ν).factorial : ℂ))
  · apply Finset.sum_congr rfl
    intro j hj
    have hjm : j ≤ m := by simpa using hj
    have h₁ : m + ν - j ≤ m + 2 * ν := by omega
    have h₂ : m + 2 * ν - (m + ν - j) = j + ν := by omega
    have h₃ : m + ν - j = m - j + ν := by omega
    have hsign : (-1 : ℂ) ^ (m-j) = (-1 : ℂ) ^ j := by
      have hmul : (-1 : ℂ) ^ j * (-1 : ℂ) ^ (m-j) = 1 := by
        rw [← pow_add, Nat.add_sub_of_le hjm, hm.neg_pow, one_pow]
      have hsquare : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
        rw [← mul_pow]; simp
      linear_combination ((-1 : ℂ) ^ j) * hmul - ((-1 : ℂ) ^ (m-j)) * hsquare
    rw [Nat.cast_choose ℂ hjm, Nat.cast_choose ℂ h₁, h₂, h₃, hsign]
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      _ = (-1 : ℂ)^j * (((m + 2*ν).factorial : ℂ) * ((m + 2*ν).factorial : ℂ)⁻¹) *
          ((m.factorial : ℂ) * (m.factorial : ℂ)⁻¹) *
          (((m-j+ν).factorial : ℂ)⁻¹ * ((j+ν).factorial : ℂ)⁻¹ *
            ((m-j).factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹) := by
        rw [mul_inv_cancel₀ (factorial_cast_ne_zero _), mul_inv_cancel₀ (factorial_cast_ne_zero _)]
        ring
      _ = _ := by ring
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hnot
    have hlt : m < j := by simpa using hnot
    simp [Nat.choose_eq_zero_of_lt hlt]

private theorem coeff_mul_one_add_X_four (p : Polynomial ℂ) {k : ℕ} (hk : 4 ≤ k) :
    (p * (X + 1)^4).coeff k =
      p.coeff k + 4*p.coeff (k-1) + 6*p.coeff (k-2) + 4*p.coeff (k-3) + p.coeff (k-4) := by
  rw [mul_comm, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_X_add_one_pow]
  rw [← Finset.sum_subset (Finset.range_mono (show 5 ≤ k+1 by omega))
    (f := fun j : ℕ => (((4 : ℕ).choose j : ℂ) * p.coeff (k-j)))
    (by
      intro j hj hn
      have hj' : 4 < j := by simp at hn; omega
      simp [Nat.choose_eq_zero_of_lt hj'])]
  norm_num [Finset.sum_range_succ, show (4 : ℕ).choose 2 = 6 by decide]

/-- The even Cauchy-product coefficients at orders zero and two, as in (16). -/
theorem besselConvolutionCoeff_even (ν d : ℕ) (hν : ν = 0 ∨ ν = 2) :
    besselConvolutionCoeff ν (2*d) = (-1 : ℂ)^d /
      ((d.factorial : ℂ) * ((d+ν).factorial : ℂ) * ((2*d+ν).factorial : ℂ)) := by
  rw [besselConvolutionCoeff_polynomial ν (2*d) (even_two_mul _)]
  rcases hν with rfl | rfl
  · simp only [mul_zero, pow_zero, mul_one, add_zero, coeff_sub_X_sq_pow, even_two_mul, ite_true]
    rw [show 2*d/2 = d by omega, show 2*d-d = d by omega,
      Nat.cast_choose ℂ (show d ≤ 2*d by omega), show 2*d-d = d by omega]
    field_simp [factorial_cast_ne_zero]
  · cases d with
    | zero =>
      norm_num [Polynomial.coeff_X_add_one_pow, show (4 : ℕ).choose 2 = 6 by decide,
        show (4 : ℕ).factorial = 24 by decide]
    | succ d =>
      norm_num only
      rw [coeff_mul_one_add_X_four _ (by omega)]
      simp only [coeff_sub_X_sq_pow]
      rw [show 2 * (d + 1) + 2 = 2 * (d + 2) by omega,
        show 2 * (d + 2) - 1 = 2 * (d + 1) + 1 by omega,
        show 2 * (d + 2) - 2 = 2 * (d + 1) by omega,
        show 2 * (d + 2) - 3 = 2 * d + 1 by omega,
        show 2 * (d + 2) - 4 = 2 * d by omega]
      simp only [even_two_mul, Nat.even_add_one, not_true_eq_false, ite_true, ite_false, mul_zero,
        add_zero]
      rw [show 2 * (d + 2) / 2 = d + 2 by omega,
        show 2 * (d + 1) / 2 = d + 1 by omega, show 2 * d / 2 = d by omega]
      rw [Nat.cast_choose ℂ (show d + 2 ≤ 2 * (d + 1) by omega),
        Nat.cast_choose ℂ (show d + 1 ≤ 2 * (d + 1) by omega),
        Nat.cast_choose ℂ (show d ≤ 2 * (d + 1) by omega)]
      rw [show 2 * (d + 1) - (d + 2) = d by omega,
        show 2 * (d + 1) - (d + 1) = d + 1 by omega,
        show 2 * (d + 1) - d = d + 2 by omega]
      rw [show 2 * (d + 1) + 4 = 2 * (d + 1) + 1 + 1 + 1 + 1 by omega,
        show 2 * (d + 2) = 2 * (d + 1) + 1 + 1 by omega,
        show (d + 1) + 2 = d + 1 + 1 + 1 by omega]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
      have hn (x : ℕ) : (x : ℂ) + 1 ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero x
      have hd1 := hn d
      have hd2 : ((d : ℂ) + 1) + 1 ≠ 0 := by simpa only [Nat.cast_succ] using hn (d+1)
      have hd3 : (((d : ℂ) + 1) + 1) + 1 ≠ 0 := by simpa only [Nat.cast_succ] using hn (d+1+1)
      have hd3' : (d : ℂ) + 2 + 1 ≠ 0 := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hn (d+2)
      have h1 : (2 : ℂ) * ((d : ℂ) + 1) + 1 ≠ 0 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ] using hn (2*(d+1))
      have h2 : (2 : ℂ) * ((d : ℂ) + 1) + 1 + 1 ≠ 0 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ] using hn (2*(d+1)+1)
      have h3 : (2 : ℂ) * ((d : ℂ) + 1) + 1 + 1 + 1 ≠ 0 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ] using hn (2*(d+1)+1+1)
      have h4 : (2 : ℂ) * ((d : ℂ) + 1) + 1 + 1 + 1 + 1 ≠ 0 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ] using hn (2*(d+1)+1+1+1)
      have h3' : (2 : ℂ) * ((d : ℂ) + 1) + 2 + 1 ≠ 0 := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hn (2*(d+1)+2)
      have h4' : (2 : ℂ) * ((d : ℂ) + 1) + 3 + 1 ≠ 0 := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hn (2*(d+1)+3)
      simp only [div_eq_mul_inv, mul_inv_rev]
      field_simp [factorial_cast_ne_zero, hd1, hd2, hd3, hd3', h1, h2, h3, h4, h3', h4']
      have hab : ((d : ℂ) + 1) * 2 + 1 ≠ 0 := by
        simpa only [mul_comm (2 : ℂ)] using h1
      have hac : ((d : ℂ) + 1) * 2 + 1 + 1 ≠ 0 := by
        simpa only [mul_comm (2 : ℂ)] using h2
      have had : ((d : ℂ) + 1 + 1) * 2 + 1 ≠ 0 := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hn ((d+1+1)*2)
      have hae : ((d : ℂ) + 1) * 2 + 3 + 1 ≠ 0 := by
        simpa only [mul_comm (2 : ℂ)] using h4'
      field_simp [factorial_cast_ne_zero, hab, hac, had, hae]
      ring

/-- The series term that remains after the odd Cauchy-product degrees vanish. -/
def besselIJSeriesTerm (ν d : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^d * (z/2)^(4*d+2*ν) /
    ((d.factorial : ℂ) * ((d+ν).factorial : ℂ) * ((2*d+ν).factorial : ℂ))

private theorem besselJ_mul_besselI_convolution_term (ν m : ℕ) (z : ℂ) :
    (∑ ij ∈ Finset.antidiagonal m, besselJTerm ν ij.1 z * besselITerm ν ij.2 z) =
      (z/2)^(2*m+2*ν) * besselConvolutionCoeff ν m := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, besselConvolutionCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using hj
  simp only [besselJTerm, besselITerm]
  have hp : 2*m+2*ν = (2*j+ν) + (2*(m-j)+ν) := by omega
  rw [hp, pow_add]
  ring

private theorem norm_besselJTerm (ν k : ℕ) (z : ℂ) :
    ‖besselJTerm ν k z‖ = ‖besselITerm ν k z‖ := by
  simp [besselJTerm, norm_pow]

private theorem summable_besselJ_mul_besselI_convolution (ν : ℕ) (z : ℂ) :
    Summable fun m => (z/2)^(2*m+2*ν) * besselConvolutionCoeff ν m := by
  let f (k : ℕ) := besselJTerm ν k z
  let g (k : ℕ) := besselITerm ν k z
  have hf : Summable fun k => ‖f k‖ := by
    simpa only [f, norm_besselJTerm] using summable_norm_besselITerm ν z
  have hg : Summable fun k => ‖g k‖ := summable_norm_besselITerm ν z
  have hs := summable_mul_of_summable_norm hf hg
  exact (summable_sum_mul_antidiagonal_of_summable_mul (f := f) (g := g) hs).congr
    (fun m => besselJ_mul_besselI_convolution_term ν m z)

/-- The Bessel product formula in (16), valid for complex arguments. -/
theorem besselJ_mul_besselI_eq_series (ν : ℕ) (hν : ν = 0 ∨ ν = 2) (z : ℂ) :
    besselJ ν z * besselI ν z = ∑' d, besselIJSeriesTerm ν d z := by
  let f (m : ℕ) := (z/2)^(2*m+2*ν) * besselConvolutionCoeff ν m
  have hf : Summable f := summable_besselJ_mul_besselI_convolution ν z
  have hm : besselJ ν z * besselI ν z = ∑' m, f m := by
    rw [besselJ, besselI,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        (by simpa only [norm_besselJTerm] using summable_norm_besselITerm ν z)
        (summable_norm_besselITerm ν z)]
    exact tsum_congr (fun m => besselJ_mul_besselI_convolution_term ν m z)
  rw [hm, ← tsum_even_add_odd
    (show Summable (fun d => f (2*d)) from hf.comp_injective (fun _ _ h => by omega))
    (show Summable (fun d => f (2*d+1)) from hf.comp_injective (fun _ _ h => by omega))]
  have he (d : ℕ) : f (2*d) = besselIJSeriesTerm ν d z := by
    unfold f besselIJSeriesTerm
    rw [besselConvolutionCoeff_even ν d hν, show 2*(2*d)+2*ν = 4*d+2*ν by omega]
    ring
  have ho (d : ℕ) : f (2*d+1) = 0 := by
    unfold f
    rw [besselConvolutionCoeff_eq_zero_of_odd ν _ ⟨d, by omega⟩, mul_zero]
  simp only [he, ho, tsum_zero, add_zero]

theorem summable_besselIJSeriesTerm (ν : ℕ) (hν : ν = 0 ∨ ν = 2) (z : ℂ) :
    Summable fun d => besselIJSeriesTerm ν d z := by
  have hs := (summable_besselJ_mul_besselI_convolution ν z).comp_injective
    (i := fun d : ℕ => 2*d) (fun _ _ h => by dsimp only at h; omega)
  apply hs.congr
  intro d
  dsimp only [Function.comp_apply]
  rw [besselConvolutionCoeff_even ν d hν, show 2*(2*d)+2*ν = 4*d+2*ν by omega,
    besselIJSeriesTerm]
  ring

/-- The derivative term of the order-zero product, after removing its constant. -/
def besselIJDerivativeTerm (k : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^(k+1) * (z/2)^(4*k+3) /
    (((k+1).factorial : ℂ)^2 * ((2*k+1).factorial : ℂ))

private theorem hasDerivAt_besselIJSeriesTerm_zero_succ (k : ℕ) (z : ℂ) :
    HasDerivAt (besselIJSeriesTerm 0 (k+1)) (besselIJDerivativeTerm k z) z := by
  have h := ((((hasDerivAt_id z).div_const (2 : ℂ)).pow (4*(k+1))).const_mul
    ((-1 : ℂ)^(k+1))).div_const
    (((k+1).factorial : ℂ) * ((k+1).factorial : ℂ) * ((2*(k+1)).factorial : ℂ))
  have h' : HasDerivAt (besselIJSeriesTerm 0 (k+1))
      (((-1 : ℂ)^(k+1) * ((4*(k+1) : ℕ) : ℂ) * (z/2)^(4*(k+1)-1) / 2) /
      (((k+1).factorial : ℂ) * ((k+1).factorial : ℂ) * ((2*(k+1)).factorial : ℂ))) z := by
    convert h using 1
    · funext w
      simp [besselIJSeriesTerm]
    · rw [id_eq]
      ring
  convert h' using 1
  unfold besselIJDerivativeTerm
  rw [show 4*(k+1)-1 = 4*k+3 by omega, show 2*(k+1) = (2*k+1)+1 by omega,
    Nat.factorial_succ (2*k+1)]
  have hn : ((2*k+1 : ℕ) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2*k+1)
  push_cast at hn ⊢
  field_simp [factorial_cast_ne_zero, hn]
  ring

private theorem norm_besselIJDerivativeTerm_le (k : ℕ) {z : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖besselIJDerivativeTerm k z‖ ≤ R^4 * ((R^4)^k / (k.factorial : ℝ)) := by
  have hr : 0 ≤ R := by linarith
  have hbase : ‖z / (2 : ℂ)‖ ≤ R := by
    rw [norm_div]
    norm_num
    linarith [norm_nonneg z]
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hfac' : (k.factorial : ℝ) ≤ ((k+1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show k ≤ k+1 by omega)
  have hfac₁ : (1 : ℝ) ≤ (k+1).factorial := by exact_mod_cast Nat.factorial_pos (k+1)
  have hfac₂ : (1 : ℝ) ≤ (2*k+1).factorial := by exact_mod_cast Nat.factorial_pos (2*k+1)
  simp only [besselIJDerivativeTerm, norm_div, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul, Complex.norm_natCast]
  calc
    _ ≤ R^(4*k+3) / (k.factorial : ℝ) := by
      have hpow := pow_le_pow_left₀ (norm_nonneg _) hbase (4*k+3)
      simp only [norm_div] at hpow
      apply div_le_div₀ (pow_nonneg hr _) hpow hfac
      calc
        (k.factorial : ℝ) ≤ ((k+1).factorial : ℝ) * 1 * 1 := by simpa using hfac'
        _ ≤ _ := by rw [pow_two]; gcongr
    _ ≤ R^(4*k+4) / (k.factorial : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_right₀ hR (by omega)) hfac.le
    _ = _ := by rw [pow_add, pow_mul, mul_comm]; ring

private theorem hasDerivAt_besselIJ_series (z : ℂ) :
    HasDerivAt (fun w => ∑' k, besselIJSeriesTerm 0 k w)
      (∑' k, besselIJDerivativeTerm k z) z := by
  let R := ‖z‖+1
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hM : Summable (fun k : ℕ => R^4 * ((R^4)^k / (k.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial (R^4)).mul_left _
  have hz : z ∈ Metric.ball (0 : ℂ) R := by simp [R, Metric.mem_ball, dist_zero_right]
  have hs := hasDerivAt_tsum_of_isPreconnected hM Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected
    (g := fun k => besselIJSeriesTerm 0 (k+1)) (g' := besselIJDerivativeTerm)
    (fun k w _ => hasDerivAt_besselIJSeriesTerm_zero_succ k w)
    (fun k w hw => norm_besselIJDerivativeTerm_le k hR
      ((by simpa [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < R).le))
    hz ((summable_nat_add_iff 1).2 (summable_besselIJSeriesTerm 0 (Or.inl rfl) z)) hz
  have heq (w : ℂ) : (∑' k, besselIJSeriesTerm 0 k w) =
      1 + ∑' k, besselIJSeriesTerm 0 (k+1) w := by
    rw [(summable_besselIJSeriesTerm 0 (Or.inl rfl) w).tsum_eq_zero_add]
    simp [besselIJSeriesTerm]
  simp_rw [heq]
  exact hs.const_add 1

/-- The differentiated order-zero product in (17). -/
theorem besselJ_zero_mul_besselI_one_sub_eq_series (z : ℂ) :
    besselJ 0 z * besselI 1 z - besselJ 1 z * besselI 0 z =
      ∑' k, besselIJDerivativeTerm k z := by
  have h := (hasDerivAt_besselJ_zero z).mul (hasDerivAt_besselI_zero z)
  have h' : HasDerivAt (fun w => besselJ 0 w * besselI 0 w)
      (∑' k, besselIJDerivativeTerm k z) z := by
    simp_rw [besselJ_mul_besselI_eq_series 0 (Or.inl rfl)]
    exact hasDerivAt_besselIJ_series z
  have he := h.unique h'
  calc
    _ = -besselJ 1 z * besselI 0 z + besselJ 0 z * besselI 1 z := by ring
    _ = _ := he

end DurfeeCCS.Step08
