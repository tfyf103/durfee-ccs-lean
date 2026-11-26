module

public import DurfeeCCS.Step12.LogConcavity
import Mathlib.Algebra.Polynomial.Derivative

/-! Darroch's mode bound for positive linear products, using the coefficient identity
obtained by differentiating the product and comparing each leave-one-out product. -/

public noncomputable section

namespace DurfeeCCS

open Polynomial

private abbrev rootProduct {ι : Type*} (s : Finset ι) (r : ι → ℝ) : Polynomial ℝ :=
  ∏ i ∈ s, (X + C (r i))

private def precedingCoeff (Q : Polynomial ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => Q.coeff k

private theorem coeff_mul_linear (Q : Polynomial ℝ) (r : ℝ) (k : ℕ) :
    (Q * (X + C r)).coeff k = precedingCoeff Q k + r * Q.coeff k := by
  rw [mul_add, coeff_add, coeff_mul_C]
  cases k <;> simp [precedingCoeff, mul_comm _ r]

private theorem rootProduct_eq_mul {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℝ)
    {i : ι} (hi : i ∈ s) :
    rootProduct s r = rootProduct (s.erase i) r * (X + C (r i)) :=
  (s.prod_erase_mul (fun j => X + C (r j)) hi).symm

/-- The coefficient times its index's deviation from the mean equals a positive
weighted sum of adjacent differences in the leave-one-out products. -/
private theorem rootProduct_coeff_balance {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i) (k : ℕ) :
    ((k : ℝ) - ∑ i ∈ s, 1 / (1 + r i)) * (rootProduct s r).coeff k =
      ∑ i ∈ s, (r i / (1 + r i)) *
        (precedingCoeff (rootProduct (s.erase i) r) k - (rootProduct (s.erase i) r).coeff k) := by
  have hderivative :
      (k : ℝ) * (rootProduct s r).coeff k =
        ∑ i ∈ s, precedingCoeff (rootProduct (s.erase i) r) k := by
    cases k with
    | zero => simp [precedingCoeff]
    | succ j =>
      have h := congrArg (fun Q : Polynomial ℝ => Q.coeff j)
        (derivative_prod_finset (s := s) (f := fun i => X + C (r i)))
      simpa [precedingCoeff, coeff_derivative, mul_comm] using h
  rw [sub_mul, hderivative, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [rootProduct_eq_mul s r hi, coeff_mul_linear]
  field_simp [show 1 + r i ≠ 0 by linarith [hr i hi]]
  ring

private theorem nextCoeff_lt_of_mode {Q : Polynomial ℝ} {m k : ℕ}
    (hQ : CoefficientShape Q m) (hk : k ≤ m) {r : ℝ} (hr : 0 < r)
    (hmode : (Q * (X + C r)).coeff (k + 1) ≤ (Q * (X + C r)).coeff k) :
    Q.coeff (k + 1) < Q.coeff k := by
  rw [coeff_mul_linear, coeff_mul_linear] at hmode
  change Q.coeff k + r * Q.coeff (k + 1) ≤ precedingCoeff Q k + r * Q.coeff k at hmode
  by_contra! hnext
  have hpos := hQ.pos k hk
  have hprev : precedingCoeff Q k < Q.coeff k := by
    cases k with
    | zero => exact hpos
    | succ j =>
      change Q.coeff j < Q.coeff (j + 1)
      by_contra! hprev
      have hprod := mul_le_mul hprev hnext hpos.le (hQ.nonneg j)
      linarith [hQ.strict_logConcave j hk, sq (Q.coeff (j + 1))]
  have hmul := mul_le_mul_of_nonneg_left hnext hr.le
  linarith

private theorem precedingCoeff_lt_of_mode {Q : Polynomial ℝ} {m k : ℕ}
    (hQ : CoefficientShape Q m) (hk : k ≤ m) {r : ℝ} (hr : 0 < r)
    (hmode : (Q * (X + C r)).coeff k ≤ (Q * (X + C r)).coeff (k + 1)) :
    precedingCoeff Q k < Q.coeff k := by
  rw [coeff_mul_linear, coeff_mul_linear] at hmode
  change precedingCoeff Q k + r * Q.coeff k ≤ Q.coeff k + r * Q.coeff (k + 1) at hmode
  have hpos := hQ.pos k hk
  cases k with
  | zero => exact hpos
  | succ j =>
    change Q.coeff j < Q.coeff (j + 1)
    by_contra! hprev
    have hnext : Q.coeff (j + 2) < Q.coeff (j + 1) := by
      by_contra! hnext
      have hprod := mul_le_mul hprev hnext hpos.le (hQ.nonneg j)
      linarith [hQ.strict_logConcave j hk, sq (Q.coeff (j + 1))]
    have hmul := mul_lt_mul_of_pos_left hnext hr
    change Q.coeff j + r * Q.coeff (j + 1) ≤ Q.coeff (j + 1) + r * Q.coeff (j + 2) at hmode
    linarith

/-- Every mode of a product of positive linear factors is strictly within one of the
sum of the normalized linear coefficients. This includes the empty product. -/
theorem rootProduct_all_modes_near_mean {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) {k : ℕ} (hk : k ≤ s.card)
    (hmode : ∀ j ≤ s.card, (∏ i ∈ s, (X + C (r i))).coeff j ≤
      (∏ i ∈ s, (X + C (r i))).coeff k) :
    |(k : ℝ) - ∑ i ∈ s, 1 / (1 + r i)| < 1 := by
  classical
  let μ : ℝ := ∑ i ∈ s, 1 / (1 + r i)
  change |(k : ℝ) - μ| < 1
  have hQ := coefficientShape_prod_linear s r hr
  have hQi (i : ι) : CoefficientShape (rootProduct (s.erase i) r) (s.erase i).card :=
    coefficientShape_prod_linear _ r (fun j hj => hr j (Finset.mem_of_mem_erase hj))
  have hweight (i : ι) (hi : i ∈ s) : 0 < r i / (1 + r i) :=
    div_pos (hr i hi) (by linarith [hr i hi])
  have hb (j : ℕ) : ((j : ℝ) - μ) * (rootProduct s r).coeff j =
      ∑ i ∈ s, (r i / (1 + r i)) *
        (precedingCoeff (rootProduct (s.erase i) r) j - (rootProduct (s.erase i) r).coeff j) :=
    rootProduct_coeff_balance s r hr j
  rw [abs_lt]
  constructor
  · by_cases hu : k + 1 ≤ s.card
    · have hs : s.Nonempty := Finset.card_pos.mp (by omega)
      have hp := hQ.pos (k + 1) hu
      have hsum : 0 < (((k + 1 : ℕ) : ℝ) - μ) * (rootProduct s r).coeff (k + 1) := by
        rw [hb]
        apply Finset.sum_pos _ hs
        intro i hi
        have hki : k ≤ (s.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
        have h := hmode (k + 1) hu
        change (rootProduct s r).coeff (k + 1) ≤ (rootProduct s r).coeff k at h
        rw [rootProduct_eq_mul s r hi] at h
        exact mul_pos (hweight i hi)
          (sub_pos.mpr (nextCoeff_lt_of_mode (hQi i) hki (hr i hi) h))
      have hdiff := pos_of_mul_pos_left hsum hp.le
      push_cast at hdiff
      linarith
    · have htop : μ ≤ (s.card : ℝ) := by
        calc
          μ ≤ ∑ i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i hi =>
            (div_le_iff₀ (by linarith [hr i hi])).mpr (by linarith [hr i hi])
          _ = s.card := by simp
      have heq : k = s.card := by omega
      rw [heq]
      linarith
  · cases k with
    | zero =>
      have hμ : 0 ≤ μ := Finset.sum_nonneg fun i hi =>
        div_nonneg zero_le_one (by linarith [hr i hi])
      simp only [Nat.cast_zero]
      linarith
    | succ k =>
      have hs : s.Nonempty := Finset.card_pos.mp (by omega)
      have hp := hQ.pos k (by omega)
      have hsum : ((k : ℝ) - μ) * (rootProduct s r).coeff k < 0 := by
        rw [hb]
        apply Finset.sum_neg _ hs
        intro i hi
        have hki : k ≤ (s.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
        have h := hmode k (by omega)
        change (rootProduct s r).coeff k ≤ (rootProduct s r).coeff (k + 1) at h
        rw [rootProduct_eq_mul s r hi] at h
        exact mul_neg_of_pos_of_neg (hweight i hi)
          (sub_neg.mpr (precedingCoeff_lt_of_mode (hQi i) hki (hr i hi) h))
      have hdiff := neg_of_mul_neg_left hsum hp.le
      push_cast
      linarith

/-- The mode bound for ordinary Durfee counts, expressed in the radii of any given
positive linear factorization. The support endpoints and the empty family are included. -/
theorem durfee_all_modes_near_rootMean_of_factorization {n d : ℕ} (hn : 1 ≤ n)
    {r : Fin (n.sqrt - 1) → ℝ} (hr : ∀ i, 0 < r i)
    (hfactor : durfeePolynomialReal n =
      C (p n n.sqrt : ℝ) * X * ∏ i, (X + C (r i)))
    (hmode : ∀ j, 1 ≤ j → j ≤ n.sqrt → p n j ≤ p n d)
    (hd : 1 ≤ d) (hd' : d ≤ n.sqrt) :
    |(d : ℝ) - (1 + ∑ i, 1 / (1 + r i))| < 1 := by
  let P : Polynomial ℝ := ∏ i, (X + C (r i))
  have hlead : 0 < (p n n.sqrt : ℝ) := by
    exact_mod_cast p_pos_of_square_le (Nat.sqrt_pos.mpr hn) (Nat.sqrt_le n)
  have hcoeff (k : ℕ) : (p n (k + 1) : ℝ) = (p n n.sqrt : ℝ) * P.coeff k := by
    rw [← coeff_durfeePolynomialReal, hfactor, mul_assoc, coeff_C_mul, coeff_X_mul]
  have hde : d - 1 + 1 = d := by omega
  have hqmode (j : ℕ) (hj : j ≤ n.sqrt - 1) : P.coeff j ≤ P.coeff (d - 1) := by
    apply le_of_mul_le_mul_left _ hlead
    rw [← hcoeff, ← hcoeff, hde]
    exact_mod_cast hmode (j + 1) (by omega) (by omega)
  have hbound := rootProduct_all_modes_near_mean (Finset.univ : Finset (Fin (n.sqrt - 1))) r
    (fun i _ => hr i) (k := d - 1) (by simpa using Nat.sub_le_sub_right hd' 1)
    (by simpa [P] using hqmode)
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (R := ℝ) hd
  rwa [hcast, sub_sub] at hbound

end DurfeeCCS
