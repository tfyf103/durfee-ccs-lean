module

public import DurfeeCCS.RootAssembly
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Convert the interior sign witnesses in (77) into the full list of simple roots. -/

public section

namespace DurfeeCCS

open Filter Polynomial
open scoped BigOperators

/-- The interior witnesses in (77), enumerated from the origin towards the negative tail. -/
@[expose] def HasFiniteWitnesses (n : ℕ) : Prop :=
  ∃ y : Fin (n.sqrt - 2) → ℝ,
    (∀ i, 0 < y i) ∧ StrictMono y ∧
      (∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * (durfeeQuotientReal n).eval (-(y i)))

/-- All roots of the Durfee polynomial: zero and `⌊√n⌋ - 1` simple negative roots. -/
@[expose] def HasDurfeeRoots (n : ℕ) : Prop :=
  ∃ r : Fin (n.sqrt - 1) ↪ ℝ, (∀ i, r i < 0) ∧ RootCompletion (durfeePolynomialReal n) r

private theorem mul_neg_of_alternatingSign {a b : ℝ} {j : ℕ}
    (ha : 0 < (-1 : ℝ) ^ j * a) (hb : 0 < (-1 : ℝ) ^ (j + 1) * b) : a * b < 0 := by
  have hunit : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have hflip : (-1 : ℝ) ^ j * ((-1 : ℝ) ^ j * -1) = -1 := by
    rw [← mul_assoc, hunit, one_mul]
  have h := mul_pos ha hb
  rw [pow_succ, mul_mul_mul_comm, hflip, neg_one_mul] at h
  exact neg_pos.mp h

private theorem hasDurfeeRoots_of_descendingPoints {n k : ℕ} (hn : 0 < n) (hm : n.sqrt = k + 1)
    (x : Fin (k + 1) → ℝ) (hdesc : StrictAnti x) (hneg : ∀ i, x i ≤ 0)
    (hsign : ∀ i, 0 < (-1 : ℝ) ^ i.val * (durfeeQuotientReal n).eval (x i)) :
    HasDurfeeRoots n := by
  let q := durfeeQuotientReal n
  have hprod (i : Fin k) : q.eval (x i.castSucc) * q.eval (x i.succ) < 0 :=
    mul_neg_of_alternatingSign (hsign i.castSucc) (hsign i.succ)
  let z : Fin (k + 1) → ℝ := fun i => x i.rev
  have hz : StrictMono z := hdesc.comp Fin.rev_strictAnti
  have hsign' (i : Fin k) : q.eval (z i.castSucc) * q.eval (z i.succ) < 0 := by
    dsimp [z]
    rw [Fin.rev_castSucc, Fin.rev_succ, mul_comm]
    exact hprod i.rev
  obtain ⟨r, hr, hcomplete⟩ :=
    durfeeRootCompletion_of_alternating hn hm z hz (fun i => hneg i.rev) hsign'
  have hcount : n.sqrt - 1 = k := by omega
  rw [HasDurfeeRoots, hcount]
  exact ⟨r, fun i => (hr i).2.2.1, hcomplete⟩

private theorem strictAnti_snoc {m : ℕ} (y : Fin m → ℝ) (a : ℝ)
    (hdesc : StrictAnti y) (ha : ∀ i, a < y i) : StrictAnti (Fin.snoc y a) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last => exact (not_lt_of_ge (Fin.le_last j) hij).elim
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa using ha i
    | cast j => simpa using hdesc (Fin.castSucc_lt_castSucc_iff.mp hij)

private theorem strictAnti_cons {m : ℕ} (y : Fin m → ℝ) (a : ℝ)
    (hdesc : StrictAnti y) (ha : ∀ i, y i < a) : StrictAnti (Fin.cons a y) := by
  intro i j hij
  induction j using Fin.cases with
  | zero => exact (not_lt_of_ge (Fin.zero_le i) hij).elim
  | succ j =>
    induction i using Fin.cases with
    | zero => simpa using ha j
    | succ i => simpa using hdesc (Fin.succ_lt_succ_iff.mp hij)

/-- Extend the interior witness chain with zero and a point in the negative tail. -/
theorem hasDurfeeRoots_of_finiteWitnesses {n : ℕ} (hn : 0 < n) (hm : 2 ≤ n.sqrt)
    (hw : HasFiniteWitnesses n) : HasDurfeeRoots n := by
  obtain ⟨y, hy, hyMono, hySign⟩ := hw
  let m := n.sqrt - 2
  have hm' : n.sqrt = (m + 1) + 1 := by dsimp [m]; omega
  obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp (eventually_signed_durfeeQuotientReal_atBot hn)
  let s : ℝ := ∑ i, y i
  let a : ℝ := min b (-s - 1)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun i _ => (hy i).le)
  have ha : a < 0 := (min_le_right _ _).trans_lt (by linarith)
  have haY (i : Fin m) : a < -(y i) := by
    have hsum : y i ≤ s := Finset.single_le_sum (fun j _ => (hy j).le) (Finset.mem_univ i)
    exact (min_le_right _ _).trans_lt (by linarith)
  let w : Fin (m + 1) → ℝ := Fin.snoc (fun i => -(y i)) a
  let x : Fin (m + 2) → ℝ := Fin.cons 0 w
  have hwAnti : StrictAnti w := strictAnti_snoc _ _ (fun _ _ hij => neg_lt_neg (hyMono hij)) haY
  have hwNeg (i : Fin (m + 1)) : w i < 0 := by
    induction i using Fin.lastCases with
    | last => simpa [w] using ha
    | cast i => simpa [w] using neg_neg_of_pos (hy i)
  have hxAnti : StrictAnti x := strictAnti_cons _ _ hwAnti hwNeg
  have hxNeg (i : Fin (m + 2)) : x i ≤ 0 := by
    induction i using Fin.cases with
    | zero => simp [x]
    | succ i => simpa [x] using (hwNeg i).le
  have hxSign (i : Fin (m + 2)) : 0 < (-1 : ℝ) ^ i.val * (durfeeQuotientReal n).eval (x i) := by
    induction i using Fin.cases with
    | zero => simpa [x] using (show (0 : ℝ) < n by exact_mod_cast hn)
    | succ i =>
      induction i using Fin.lastCases with
      | last =>
        have h := hb a (min_le_left _ _)
        have hd : n.sqrt - 1 = m + 1 := by omega
        simpa [x, w, hd] using h
      | cast i => simpa [x, w] using hySign i
  exact hasDurfeeRoots_of_descendingPoints hn hm' x hxAnti hxNeg hxSign

/-- Sizes below nine have degree one or two. For degree two there are no interior tests. -/
theorem hasDurfeeRoots_of_small {n : ℕ} (hn : 0 < n) (hn' : n ≤ 8) : HasDurfeeRoots n := by
  have hpos : 0 < n.sqrt := Nat.sqrt_pos.mpr hn
  have hlt : n.sqrt < 3 := Nat.sqrt_lt.mpr (by omega)
  by_cases hm : 2 ≤ n.sqrt
  · apply hasDurfeeRoots_of_finiteWitnesses hn hm
    have hempty : n.sqrt - 2 = 0 := by omega
    rw [HasFiniteWitnesses, hempty]
    refine ⟨Fin.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    intro i
    exact i.elim0
  · have hm' : n.sqrt = 0 + 1 := by omega
    have hcount : n.sqrt - 1 = 0 := by omega
    let r : Fin 0 ↪ ℝ := ⟨Fin.elim0, fun i => i.elim0⟩
    rw [HasDurfeeRoots, hcount]
    exact ⟨r, fun i => i.elim0, durfeeRootCompletion_of_quotientRoots hn hm' r (fun i => i.elim0)⟩

end DurfeeCCS
