module

public import DurfeeCCS.Main

/-! # Strict log-concavity and unimodality of the Durfee coefficients -/

public section

namespace DurfeeCCS

open Polynomial

/-- A polynomial with positive coefficients through degree `m`, zero coefficients beyond `m`,
    and strictly log-concave adjacent triples centered at indices from `1` to `m`. -/
structure CoefficientShape (P : ℝ[X]) (m : ℕ) where
  pos : ∀ k ≤ m, 0 < P.coeff k
  zero : ∀ k, m < k → P.coeff k = 0
  strict_logConcave : ∀ k, k + 1 ≤ m → P.coeff k * P.coeff (k + 2) < P.coeff (k + 1) ^ 2

theorem CoefficientShape.nonneg {P : ℝ[X]} {m : ℕ}
    (h : CoefficientShape P m) (k : ℕ) : 0 ≤ P.coeff k := by
  by_cases hk : k ≤ m
  · exact (h.pos k hk).le
  · rw [h.zero k (Nat.lt_of_not_ge hk)]

theorem CoefficientShape.logConcave {P : ℝ[X]} {m : ℕ}
    (h : CoefficientShape P m) (k : ℕ) :
    P.coeff k * P.coeff (k + 2) ≤ P.coeff (k + 1) ^ 2 := by
  by_cases hk : k + 1 ≤ m
  · exact (h.strict_logConcave k hk).le
  · rw [h.zero (k + 2) (by omega), mul_zero]
    exact sq_nonneg _

private theorem CoefficientShape.cross {P : ℝ[X]} {m : ℕ}
    (h : CoefficientShape P m) (k : ℕ) :
    P.coeff k * P.coeff (k + 3) ≤ P.coeff (k + 1) * P.coeff (k + 2) := by
  by_cases hk : k + 3 ≤ m
  · have hmid : 0 < P.coeff (k + 1) * P.coeff (k + 2) :=
      mul_pos (h.pos _ (by omega)) (h.pos _ (by omega))
    apply le_of_mul_le_mul_right ?_ hmid
    calc
      (P.coeff k * P.coeff (k + 3)) * (P.coeff (k + 1) * P.coeff (k + 2)) =
          (P.coeff k * P.coeff (k + 2)) * (P.coeff (k + 1) * P.coeff (k + 3)) := by ring
      _ ≤ P.coeff (k + 1) ^ 2 * P.coeff (k + 2) ^ 2 :=
        mul_le_mul (h.logConcave k) (h.logConcave (k + 1))
          (mul_nonneg (h.nonneg _) (h.nonneg _)) (sq_nonneg _)
      _ = (P.coeff (k + 1) * P.coeff (k + 2)) * (P.coeff (k + 1) * P.coeff (k + 2)) := by ring
  · rw [h.zero (k + 3) (Nat.lt_of_not_ge hk), mul_zero]
    exact mul_nonneg (h.nonneg _) (h.nonneg _)

private theorem CoefficientShape.mul_linear {P : ℝ[X]} {m : ℕ}
    (h : CoefficientShape P m) {r : ℝ} (hr : 0 < r) :
    CoefficientShape (P * (X + C r)) (m + 1) := by
  have hz : (P * (X + C r)).coeff 0 = P.coeff 0 * r := by
    simp [mul_add]
  have hs (k : ℕ) : (P * (X + C r)).coeff (k + 1) =
      P.coeff k + P.coeff (k + 1) * r := by
    simp [mul_add, coeff_mul_X, coeff_mul_C]
  constructor
  · intro k hk
    cases k with
    | zero =>
      rw [hz]
      exact mul_pos (h.pos 0 (Nat.zero_le _)) hr
    | succ k =>
      rw [hs]
      exact add_pos_of_pos_of_nonneg (h.pos k (by omega)) (mul_nonneg (h.nonneg _) hr.le)
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Nat.succ_eq_add_one, hs, h.zero j (by omega), h.zero (j + 1) (by omega)]
    simp
  · intro k hk
    cases k with
    | zero =>
      rw [hz]
      simp only [Nat.zero_add]
      rw [hs 0, hs 1]
      have hlead := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr (h.logConcave 0))
      have hmid := mul_nonneg hr.le (mul_nonneg (h.nonneg 0) (h.nonneg 1))
      have hpos := sq_pos_of_pos (h.pos 0 (Nat.zero_le _))
      nlinarith only [hlead, hmid, hpos]
    | succ k =>
      rw [hs k, hs (k + 1), show k + 1 + 2 = (k + 2) + 1 by omega, hs (k + 2)]
      have hlead := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr (h.logConcave (k + 1)))
      have hmid := mul_nonneg hr.le (sub_nonneg.mpr (h.cross k))
      have hpos := h.strict_logConcave k (by omega)
      nlinarith only [hlead, hmid, hpos]

/-- Finite products of positive linear factors have strictly log-concave coefficients. -/
theorem coefficientShape_prod_linear {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i) :
    CoefficientShape (∏ i ∈ s, (X + C (r i))) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty]
    exact ⟨fun k hk => by simp [Nat.eq_zero_of_le_zero hk],
      fun k hk => by simp [coeff_one, hk.ne'], fun k hk => (by omega : False).elim⟩
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, mul_comm]
    exact (ih fun j hj => hr j (Finset.mem_insert_of_mem hj)).mul_linear
      (hr i (Finset.mem_insert_self i s))

/-- The positive Durfee coefficients are strictly log-concave at every interior index. -/
theorem durfee_strict_logConcave (n d : ℕ) (hn : 1 ≤ n) (hd : 1 < d) (hm : d < n.sqrt) :
    p n (d - 1) * p n (d + 1) < (p n d) ^ 2 := by
  obtain ⟨r, hr, hf⟩ := durfee_factorization n hn
  let P : ℝ[X] := ∏ i, (X + C (r i))
  have hshape : CoefficientShape P (n.sqrt - 1) := by
    simpa [P] using coefficientShape_prod_linear Finset.univ r (fun i _ => hr i)
  have hcoef (k : ℕ) : (p n (k + 1) : ℝ) = (p n n.sqrt : ℝ) * P.coeff k := by
    rw [← coeff_durfeePolynomialReal, hf, mul_assoc, coeff_C_mul, ← show P = _ from rfl,
      coeff_X_mul]
  have ht : (0 : ℝ) < p n n.sqrt := by
    exact_mod_cast p_pos_of_square_le (Nat.sqrt_pos.mpr hn) (Nat.sqrt_le n)
  obtain ⟨k, hk⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  subst d
  rw [show k + 2 - 1 = k + 1 by omega]
  have hlt := mul_lt_mul_of_pos_left
    (hshape.strict_logConcave k (by omega)) (sq_pos_of_pos ht)
  have hreal : (p n (k + 1) : ℝ) * p n (k + 2 + 1) < (p n (k + 2) : ℝ) ^ 2 := by
    rw [hcoef k, hcoef (k + 2), show k + 2 = (k + 1) + 1 by omega, hcoef (k + 1)]
    nlinarith only [hlt]
  exact_mod_cast hreal

/-- A nonincrease forces a strict decrease at the next step inside the support. -/
private theorem durfee_next_lt_of_le {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hm : d + 2 ≤ n.sqrt) (h : p n (d + 1) ≤ p n d) : p n (d + 2) < p n (d + 1) := by
  have hlog := durfee_strict_logConcave n (d + 1) hn (by omega) (by omega)
  rw [Nat.add_sub_cancel] at hlog
  by_contra! h'
  have hmul := Nat.mul_le_mul h h'
  rw [← pow_two] at hmul
  exact (not_lt_of_ge hmul) hlog

/-- The coefficients increase weakly up to a mode and decrease weakly thereafter. -/
theorem durfee_unimodal (n : ℕ) (hn : 1 ≤ n) :
    ∃ mode, 1 ≤ mode ∧ mode ≤ n.sqrt ∧
      MonotoneOn (p n) (Set.Icc 1 mode) ∧ AntitoneOn (p n) (Set.Icc mode n.sqrt) := by
  have hm : 1 ≤ n.sqrt := Nat.sqrt_pos.mpr hn
  let good (k : ℕ) : Prop := 1 ≤ k ∧ p n (k + 1) ≤ p n k
  have hex : ∃ k, good k := by
    refine ⟨n.sqrt, hm, ?_⟩
    rw [p_eq_zero_of_sq_gt (Nat.sqrt_lt.mp (Nat.lt_succ_self _))]
    exact Nat.zero_le _
  let mode := Nat.find hex
  have hmode : good mode := Nat.find_spec hex
  have hmode_le : mode ≤ n.sqrt := Nat.find_min' hex (by
    refine ⟨hm, ?_⟩
    rw [p_eq_zero_of_sq_gt (Nat.sqrt_lt.mp (Nat.lt_succ_self _))]
    exact Nat.zero_le _)
  have hdec (k : ℕ) (hkm : mode ≤ k) (hks : k < n.sqrt) : p n (k + 1) ≤ p n k := by
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases heq : k + 1 = mode
      · simpa [Nat.succ_eq_add_one, heq] using hmode.2
      · exact (durfee_next_lt_of_le hn (by have := hmode.1; omega) (by omega)
          (ih (by omega) (by omega))).le
  refine ⟨mode, hmode.1, hmode_le, ?_, ?_⟩
  · apply monotoneOn_of_le_add_one Set.ordConnected_Icc
    intro k _ hk hk'
    have hklt : k < mode := by have := hk'.2; omega
    exact le_of_lt (lt_of_not_ge fun hb => (Nat.find_min hex hklt) ⟨hk.1, hb⟩)
  · apply antitoneOn_of_add_one_le Set.ordConnected_Icc
    intro k _ hk hk'
    exact hdec k hk.1 (by have := hk'.2; omega)

end DurfeeCCS
