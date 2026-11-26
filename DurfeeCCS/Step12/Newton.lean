module

public import DurfeeCCS.Step12.LogConcavity

/-! # Binomially normalized Newton inequalities for the Durfee quotient -/

public section

namespace DurfeeCCS

open Polynomial

private noncomputable def normalizedCoeff (P : ℝ[X]) (m j : ℕ) : ℝ :=
  P.coeff j / (m.choose j : ℝ)

private theorem normalizedCoeff_nonneg {P : ℝ[X]} {m : ℕ} (hP : CoefficientShape P m)
    (j : ℕ) : 0 ≤ normalizedCoeff P m j :=
  div_nonneg (hP.nonneg j) (Nat.cast_nonneg _)

private theorem normalizedCoeff_pos {P : ℝ[X]} {m j : ℕ} (hP : CoefficientShape P m)
    (hj : j ≤ m) : 0 < normalizedCoeff P m j :=
  div_pos (hP.pos j hj) (by exact_mod_cast Nat.choose_pos hj)

private theorem scaled_normalizedCoeff_mul_linear {P : ℝ[X]} {m : ℕ}
    (hP : CoefficientShape P m) (r : ℝ) {j : ℕ} (hj : j ≤ m) :
    ((m : ℝ) + 1) * normalizedCoeff (P * (X + C r)) (m + 1) (j + 1) =
      ((m : ℝ) - j) * (r * normalizedCoeff P m (j + 1)) +
        ((j : ℝ) + 1) * normalizedCoeff P m j := by
  have hc : (P * (X + C r)).coeff (j + 1) = P.coeff j + P.coeff (j + 1) * r := by
    simp [mul_add, coeff_mul_X, coeff_mul_C]
  by_cases heq : j = m
  · subst j
    simp [normalizedCoeff, hc, hP.zero (m + 1) (by omega), Nat.choose_self, mul_comm]
  have hj' : j + 1 ≤ m := by omega
  have hA : (m.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  have hB : (m.choose (j + 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  have hC : ((m + 1).choose (j + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show j + 1 ≤ m + 1 by omega)).ne'
  have hleft : ((m : ℝ) + 1) / ((m + 1).choose (j + 1) : ℝ) =
      ((j : ℝ) + 1) / (m.choose j : ℝ) := by
    apply (div_eq_div_iff hC hA).mpr
    have h := Nat.add_one_mul_choose_eq m j
    exact_mod_cast h.trans (mul_comm _ _)
  have hright : ((m : ℝ) + 1) / ((m + 1).choose (j + 1) : ℝ) =
      ((m : ℝ) - j) / (m.choose (j + 1) : ℝ) := by
    apply (div_eq_div_iff hC hB).mpr
    have h := Nat.choose_mul_succ_eq m (j + 1)
    rw [show m + 1 - (j + 1) = m - j by omega] at h
    have hcast : (↑(m.choose (j + 1)) : ℝ) * ((m : ℝ) + 1) =
        ↑((m + 1).choose (j + 1)) * ↑(m - j) := by exact_mod_cast h
    rw [Nat.cast_sub hj, mul_comm (↑(m.choose (j + 1)) : ℝ), mul_comm _ ((m : ℝ) - j)] at hcast
    exact hcast
  unfold normalizedCoeff
  rw [hc]
  calc
    _ = P.coeff j * (((m : ℝ) + 1) / ↑((m + 1).choose (j + 1))) +
        (r * P.coeff (j + 1)) * (((m : ℝ) + 1) / ↑((m + 1).choose (j + 1))) := by ring
    _ = _ := by
      conv_lhs => arg 1; rw [hleft]
      rw [hright]
      ring

private theorem normalizedCoeff_logConcave_mul_linear {P : ℝ[X]} {m : ℕ} {r : ℝ}
    (hP : CoefficientShape P m) (hr : 0 < r)
    (hlog : ∀ j, j + 2 ≤ m → normalizedCoeff P m j * normalizedCoeff P m (j + 2) ≤
      normalizedCoeff P m (j + 1) ^ 2)
    (j : ℕ) (hj : j + 2 ≤ m + 1) :
    normalizedCoeff (P * (X + C r)) (m + 1) j *
      normalizedCoeff (P * (X + C r)) (m + 1) (j + 2) ≤
      normalizedCoeff (P * (X + C r)) (m + 1) (j + 1) ^ 2 := by
  let a := normalizedCoeff P m
  let b := normalizedCoeff (P * (X + C r)) (m + 1)
  let M : ℝ := (m : ℝ) + 1
  let B (i : ℕ) : ℝ := M * b i
  change b j * b (j + 2) ≤ b (j + 1) ^ 2
  have hB (k : ℕ) (hk : k ≤ m) :
      B (k + 1) = ((m : ℝ) - k) * (r * a (k + 1)) + ((k : ℝ) + 1) * a k :=
    scaled_normalizedCoeff_mul_linear hP r hk
  have hB0 : B 0 = M * (r * a 0) := by
    simp [B, a, b, normalizedCoeff, mul_add, mul_comm]
  have ha (k : ℕ) : 0 ≤ a k := normalizedCoeff_nonneg hP _
  have hBn (k : ℕ) (hk : k ≤ m + 1) : 0 ≤ B k := by
    cases k with
    | zero =>
      rw [hB0]
      exact mul_nonneg (by dsimp [M]; positivity) (mul_nonneg hr.le (ha 0))
    | succ k =>
      rw [hB k (by omega)]
      have hcast : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hcast) (mul_nonneg hr.le (ha _)))
        (mul_nonneg (by positivity) (ha _))
  let T := r * a (j + 1) - a j
  have hleft : a (j + 1) * B j ≤ a j * (B (j + 1) + T) := by
    dsimp only [T]
    cases j with
    | zero =>
      rw [hB0, hB 0 (by omega)]
      simp only [Nat.cast_zero, sub_zero, zero_add]
      dsimp [M]
      ring_nf
      exact le_rfl
    | succ k =>
      rw [hB k (by omega), hB (k + 1) (by omega)]
      have h := mul_le_mul_of_nonneg_left (hlog k (by omega)) (show 0 ≤ (k : ℝ) + 1 by positivity)
      change ((k : ℝ) + 1) * (a k * a (k + 2)) ≤ ((k : ℝ) + 1) * a (k + 1) ^ 2 at h
      push_cast
      nlinarith only [h]
  have hright : a j * B (j + 2) ≤ a (j + 1) * (B (j + 1) - T) := by
    dsimp only [T]
    rw [show j + 2 = (j + 1) + 1 by omega, hB (j + 1) (by omega), hB j (by omega)]
    have h : a j * a (j + 2) ≤ a (j + 1) ^ 2 := by
      by_cases hk : j + 2 ≤ m
      · exact hlog j hk
      · have hz := hP.zero (j + 2) (by omega)
        simp [a, normalizedCoeff, hz, sq_nonneg]
    have hcast : (↑(j + 1) : ℝ) ≤ m := by exact_mod_cast (show j + 1 ≤ m by omega)
    have h' := mul_le_mul_of_nonneg_left h (mul_nonneg (sub_nonneg.mpr hcast) hr.le)
    simp only [show j + 1 + 1 = j + 2 by omega, Nat.cast_add, Nat.cast_one] at h' ⊢
    nlinarith only [h']
  have hpair : 0 < a j * a (j + 1) :=
    mul_pos (normalizedCoeff_pos hP (by omega)) (normalizedCoeff_pos hP (by omega))
  have hprod := mul_le_mul hleft hright
    (mul_nonneg (ha j) (hBn (j + 2) hj)) ((mul_nonneg (ha (j + 1)) (hBn j (by omega))).trans hleft)
  have hscaled : B j * B (j + 2) ≤ B (j + 1) ^ 2 := by
    apply le_of_mul_le_mul_left _ hpair
    nlinarith only [hprod, mul_nonneg hpair.le (sq_nonneg T)]
  apply le_of_mul_le_mul_left _ (sq_pos_of_pos (show 0 < M by dsimp [M]; positivity))
  dsimp [B] at hscaled
  nlinarith only [hscaled]

/-- Newton's adjacent inequality for a product of positive linear factors, with
each coefficient divided by the corresponding binomial coefficient. -/
theorem positiveLinearProduct_newton {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i) (j : ℕ) (hj : j + 2 ≤ s.card) :
    let P : ℝ[X] := ∏ i ∈ s, (X + C (r i))
    (P.coeff j / (s.card.choose j : ℝ)) * (P.coeff (j + 2) / (s.card.choose (j + 2) : ℝ)) ≤
      (P.coeff (j + 1) / (s.card.choose (j + 1) : ℝ)) ^ 2 := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty => simp at hj
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.card_insert_of_notMem hi] at hj ⊢
    rw [mul_comm (X + C (r i))]
    have hrest : ∀ k ∈ s, 0 < r k := fun k hk => hr k (Finset.mem_insert_of_mem hk)
    exact normalizedCoeff_logConcave_mul_linear (coefficientShape_prod_linear s r hrest)
      (hr i (Finset.mem_insert_self i s)) (ih hrest) j hj

/-- The Durfee quotient coefficients satisfy the binomially normalized Newton inequality. -/
theorem durfee_newton_normalized (n d : ℕ) (hn : 1 ≤ n) (hd : 1 < d) (hm : d < n.sqrt) :
    let m := n.sqrt - 1
    ((p n (d - 1) : ℝ) / (m.choose (d - 2) : ℝ)) *
      ((p n (d + 1) : ℝ) / (m.choose d : ℝ)) ≤
      ((p n d : ℝ) / (m.choose (d - 1) : ℝ)) ^ 2 := by
  obtain ⟨r, hr, hf⟩ := durfee_factorization n hn
  let P : ℝ[X] := ∏ i, (X + C (r i))
  have hc (i : ℕ) : (p n (i + 1) : ℝ) = (p n n.sqrt : ℝ) * P.coeff i := by
    rw [← coeff_durfeePolynomialReal, hf, mul_assoc, coeff_C_mul, coeff_X_mul]
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 2 := ⟨d - 2, by omega⟩
  have h := positiveLinearProduct_newton (Finset.univ : Finset (Fin (n.sqrt - 1))) r
    (fun i _ => hr i) j (by simp; omega)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  dsimp only
  rw [show j + 2 - 1 = j + 1 by omega, show j + 2 - 2 = j by omega, hc j, hc (j + 2),
    show j + 2 = (j + 1) + 1 by omega, hc (j + 1)]
  simp only [mul_div_assoc]
  nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg (p n n.sqrt : ℝ))]

end DurfeeCCS
