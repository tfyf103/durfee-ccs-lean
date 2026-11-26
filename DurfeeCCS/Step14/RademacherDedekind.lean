module

public import DurfeeCCS.Step06.Dedekind
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Reciprocity of the Dedekind sums occurring in the cusp phase of (14).
The proof counts the lattice points on either side of the diagonal of a rectangle.
-/

public section

namespace DurfeeCCS.Step14

open Finset DurfeeCCS.Step06

private theorem sum_ico_id (n : ℕ) :
    ∑ i ∈ Ico 1 n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num
    · rw [sum_Ico_succ_top (by omega), ih, Nat.cast_succ]
      ring

private theorem sum_ico_sq (n : ℕ) :
    ∑ i ∈ Ico 1 n, (i : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num
    · rw [sum_Ico_succ_top (by omega), ih, Nat.cast_succ]
      ring

private theorem sum_remainder_perm {a b : ℕ} (hb : 0 < b) (hab : a.Coprime b)
    (f : ℕ → ℝ) (hf : f 0 = 0) :
    ∑ i ∈ Ico 1 b, f (a * i % b) = ∑ i ∈ Ico 1 b, f i := by
  let m : Fin b → Fin b := fun i => ⟨a * i.val % b, Nat.mod_lt _ hb⟩
  have hsurj : Function.Surjective m := by
    intro j
    obtain ⟨i, hi, he⟩ := Nat.exists_mul_mod_eq_of_coprime j.val hab hb.ne'
    exact ⟨⟨i, hi⟩, Fin.ext (he.trans (Nat.mod_eq_of_lt j.isLt))⟩
  let e := Equiv.ofBijective m ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have he : ∑ i ∈ range b, f (a * i % b) = ∑ i ∈ range b, f i := by
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range f]
    exact e.sum_comp (fun j : Fin b => f j.val)
  simpa only [range_eq_Ico, sum_eq_sum_Ico_succ_bot hb, Nat.zero_add, mul_zero,
    Nat.zero_mod, hf, zero_add] using he

private noncomputable def floorMoment (a b : ℕ) : ℝ :=
  ∑ i ∈ Ico 1 b, (i : ℝ) * ((a * i / b : ℕ) : ℝ)

private noncomputable def floorCount (a b : ℕ) : ℝ :=
  ∑ i ∈ Ico 1 b, ((a * i / b : ℕ) : ℝ)

private noncomputable def floorSquare (a b : ℕ) : ℝ :=
  ∑ i ∈ Ico 1 b, (((a * i / b : ℕ) : ℝ) ^ 2)

private theorem remainder_eq (a b i : ℕ) :
    ((a * i % b : ℕ) : ℝ) = (a : ℝ) * i - (b : ℝ) * ((a * i / b : ℕ) : ℝ) := by
  have h := congrArg (fun j : ℕ => (j : ℝ)) (Nat.mod_add_div (a * i) b)
  push_cast at h
  linarith

private theorem floorCount_eq {a b : ℕ} (hb : 0 < b) (hab : a.Coprime b) :
    floorCount a b = ((a : ℝ) - 1) * ((b : ℝ) - 1) / 2 := by
  have h := sum_remainder_perm hb hab (fun i => (i : ℝ)) (by simp)
  simp_rw [remainder_eq a b] at h
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_ico_id, ← floorCount] at h
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  apply mul_left_cancel₀ hb'
  linear_combination -h

private theorem floorSquare_eq {a b : ℕ} (hb : 0 < b) (hab : a.Coprime b) :
    (b : ℝ) ^ 2 * floorSquare a b =
      2 * (a : ℝ) * b * floorMoment a b +
        (1 - (a : ℝ) ^ 2) * (∑ i ∈ Ico 1 b, (i : ℝ) ^ 2) := by
  have h := sum_remainder_perm hb hab (fun i => (i : ℝ) ^ 2) (by norm_num)
  simp_rw [remainder_eq a b, show ∀ (i q : ℝ),
    ((a : ℝ) * i - (b : ℝ) * q) ^ 2 =
      (a : ℝ) ^ 2 * i ^ 2 - (2 * (a : ℝ) * b) * (i * q) + (b : ℝ) ^ 2 * q ^ 2
      by intros; ring] at h
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    ← floorMoment, ← floorSquare] at h
  linear_combination h

private theorem floor_lt_upper {a b i : ℕ} (ha : 0 < a) (hb : 0 < b) (hi : i < b) :
    a * i / b < a := by
  apply (Nat.div_lt_iff_lt_mul hb).mpr
  exact Nat.mul_lt_mul_of_pos_left hi ha

private theorem filter_le_floor {a b i : ℕ} (ha : 0 < a) (hb : 0 < b) (hi : i < b) :
    (Ico 1 a).filter (fun j => j ≤ a * i / b) = Ico 1 (a * i / b + 1) := by
  ext j
  simp only [mem_filter, mem_Ico]
  have hf := floor_lt_upper ha hb hi
  omega

private theorem strictly_below_transposed {a b i j : ℕ}
    (ha : 0 < a) (hab : a.Coprime b) (hj : j ∈ Ico 1 a) :
    i * a < j * b ↔ i ≤ b * j / a := by
  rw [Nat.le_div_iff_mul_le ha, Nat.mul_comm b j]
  have hne : i * a ≠ j * b := by
    intro he
    have hd : a ∣ j * b := he ▸ dvd_mul_left a i
    have hdiv : a ∣ j := hab.dvd_of_dvd_mul_right hd
    exact (Nat.not_dvd_of_pos_of_lt (mem_Ico.mp hj).1 (mem_Ico.mp hj).2) hdiv
  exact ⟨le_of_lt, fun hl => lt_of_le_of_ne hl hne⟩

private theorem floorMoments_transpose {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    floorMoment b a + (floorSquare a b + floorCount a b) / 2 =
      ((b : ℝ) - 1) * (a : ℝ) * ((a : ℝ) - 1) / 2 := by
  let w (i j : ℕ) : ℝ := if i * a < j * b then (j : ℝ) else 0
  have hc : (∑ j ∈ Ico 1 a, ∑ i ∈ Ico 1 b, w i j) = floorMoment b a := by
    unfold floorMoment
    apply sum_congr rfl
    intro j hj
    have h : (∑ i ∈ Ico 1 b, w i j) =
        ∑ i ∈ Ico 1 b, (if i ≤ b * j / a then (j : ℝ) else 0) := by
      apply sum_congr rfl
      intro i _
      simp only [w, strictly_below_transposed ha hab hj]
    rw [h, ← sum_filter, filter_le_floor hb ha (mem_Ico.mp hj).2,
      sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
  have hr : (∑ i ∈ Ico 1 b, ∑ j ∈ Ico 1 a, w i j) =
      ((b : ℝ) - 1) * ((a : ℝ) * ((a : ℝ) - 1) / 2) -
        (floorSquare a b + floorCount a b) / 2 := by
    have h (i : ℕ) (hi : i ∈ Ico 1 b) : (∑ j ∈ Ico 1 a, w i j) =
        (a : ℝ) * ((a : ℝ) - 1) / 2 -
          ((((a * i / b : ℕ) : ℝ) ^ 2) + ((a * i / b : ℕ) : ℝ)) / 2 := by
      calc
        _ = ∑ j ∈ Ico 1 a, ((j : ℝ) - (if j ≤ a * i / b then (j : ℝ) else 0)) := by
          apply sum_congr rfl
          intro j hj
          simp only [w, Nat.le_div_iff_mul_le hb]
          rw [Nat.mul_comm a i]
          by_cases hz : i * a < j * b
          · simp [hz, not_le_of_gt hz]
          · simp [hz, le_of_not_gt hz]
        _ = _ := by
          rw [sum_sub_distrib, ← sum_filter, filter_le_floor ha hb (mem_Ico.mp hi).2,
            sum_ico_id, sum_ico_id]
          push_cast
          ring
    unfold floorCount floorSquare
    rw [sum_congr rfl h, sum_sub_distrib, sum_const, Nat.card_Ico,
      nsmul_eq_mul, Nat.cast_sub hb, Nat.cast_one]
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul, sum_add_distrib]
  rw [sum_comm, hr] at hc
  linarith

private theorem dedekindSum_eq_floorMoment {a b : ℕ} (hb : 0 < b) (hab : a.Coprime b) :
    dedekindSum a b =
      (a : ℝ) / (b : ℝ) ^ 2 * (∑ i ∈ Ico 1 b, (i : ℝ) ^ 2) -
        floorMoment a b / b - ((b : ℝ) - 1) / 4 := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [dedekindSum_eq_IJT hb hab, dedekindSumIJT]
  have h (i : ℕ) : (i : ℝ) / b * (dedekindFraction (↑(a * i : ℕ)) b - 1 / 2) =
      (a : ℝ) / (b : ℝ) ^ 2 * (i : ℝ) ^ 2 -
        ((i : ℝ) * ((a * i / b : ℕ) : ℝ)) / b - (i : ℝ) / (2 * b) := by
    rw [dedekindFraction_eq_mod_div _ hb, remainder_eq a b]
    field_simp
  simp_rw [h]
  simp_rw [div_eq_mul_inv]
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, ← sum_mul,
    ← floorMoment, sum_ico_id]
  field_simp
  ring

/-- Dedekind reciprocity in the convention of the Rademacher phase of (14). -/
theorem dedekindSum_reciprocity {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    dedekindSum a b + dedekindSum b a =
      -1 / 4 + ((a : ℝ) / b + (b : ℝ) / a + 1 / ((a : ℝ) * b)) / 12 := by
  let A : ℝ := a
  let B : ℝ := b
  let S₂ : ℝ := ∑ i ∈ Ico 1 b, (i : ℝ) ^ 2
  have hA : A ≠ 0 := by dsimp [A]; exact_mod_cast ha.ne'
  have hB : B ≠ 0 := by dsimp [B]; exact_mod_cast hb.ne'
  have ht := floorMoments_transpose ha hb hab
  have hr := floorSquare_eq hb hab
  have hc := floorCount_eq hb hab
  have hF : floorMoment a b / B + floorMoment b a / A =
      (B - 1) * (A - 1) / 2 + (A ^ 2 - 1) * S₂ / (2 * A * B ^ 2) -
        floorCount a b / (2 * A) := by
    field_simp [hA, hB]
    dsimp only [A, B, S₂]
    linear_combination 2 * (b : ℝ) ^ 2 * ht - hr
  rw [dedekindSum_eq_floorMoment hb hab, dedekindSum_eq_floorMoment ha hab.symm]
  change _ = -1 / 4 + (A / B + B / A + 1 / (A * B)) / 12
  rw [show (a : ℝ) / (b : ℝ) ^ 2 * S₂ - floorMoment a b / B - (B - 1) / 4 +
      ((b : ℝ) / (a : ℝ) ^ 2 * (∑ i ∈ Ico 1 a, (i : ℝ) ^ 2) -
        floorMoment b a / A - (A - 1) / 4) =
      A / B ^ 2 * S₂ + B / A ^ 2 * (∑ i ∈ Ico 1 a, (i : ℝ) ^ 2) -
        (floorMoment a b / B + floorMoment b a / A) -
        (B - 1) / 4 - (A - 1) / 4 by ring, hF, hc]
  rw [show S₂ = B * (B - 1) * (2 * B - 1) / 6 by exact sum_ico_sq b, sum_ico_sq]
  field_simp [hA, hB]
  ring

/-- Changing the numerator by a whole period preserves the Dedekind sum. -/
theorem dedekindSum_add_mul (h t : ℤ) {k : ℕ} (hk : 0 < k) :
    dedekindSum (h + t * (k : ℤ)) k = dedekindSum h k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold dedekindSum
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold dedekindFraction
  have he : (((h + t * (k : ℤ)) * (j : ℤ) : ℤ) : ℝ) / (k : ℝ) =
      ((h * (j : ℤ) : ℤ) : ℝ) / (k : ℝ) + ((t * (j : ℤ) : ℤ) : ℝ) := by
    push_cast
    field_simp [hkR]
  rw [he, Int.floor_add_intCast, Int.cast_add]
  ring

/-- The Dedekind sum changes sign when a reduced numerator is negated. -/
theorem dedekindSum_neg_nat {h k : ℕ} (hk : 0 < k) (hred : h.Coprime k) :
    dedekindSum (-(h : ℤ)) k = -dedekindSum h k := by
  unfold dedekindSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hd : ¬ k ∣ h * j := fun he =>
    (Nat.not_dvd_of_pos_of_lt (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)
      (hred.symm.dvd_of_dvd_mul_left he)
  have hmod : 0 < h * j % k := Nat.pos_of_ne_zero fun he => hd (Nat.dvd_of_mod_eq_zero he)
  have hpos : 0 < dedekindFraction (↑(h * j : ℕ)) k := by
    rw [dedekindFraction_eq_mod_div _ hk]
    positivity
  let x : ℝ := ((h * j : ℕ) : ℝ) / (k : ℝ)
  have hpos' : 0 < x - (⌊x⌋ : ℝ) := by simpa only [x, dedekindFraction, Int.cast_natCast] using hpos
  have hfloor : ⌊-x⌋ = -⌊x⌋ - 1 := Int.floor_eq_iff.mpr (by
    push_cast
    constructor
    · linarith only [Int.lt_floor_add_one x]
    · linarith only [hpos'])
  simp only [neg_mul, ← Int.natCast_mul, dedekindFraction, Int.cast_neg, Int.cast_natCast,
    neg_div]
  rw [show ((h * j : ℕ) : ℝ) / (k : ℝ) = x from rfl, hfloor]
  push_cast
  ring

end DurfeeCCS.Step14
