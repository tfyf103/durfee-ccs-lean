module

public import DurfeeCCS.EquationOne
public import DurfeeCCS.Quotient

/-! Dynamic programming for the exact Durfee coefficients. -/

@[expose] public section

namespace DurfeeCCS

open PowerSeries

/-- Compute the first `length` coefficients of a series after applying one geometric factor.
Reading an earlier entry of the output accounts for a further occurrence of size `d`. -/
def geometricPrefix (d : ℕ) (a : Array ℤ) : ℕ → Array ℤ
  | 0 => #[]
  | length + 1 =>
    let b := geometricPrefix d a length
    b.push (a[length]! + if d ≤ length then b[length - d]! else 0)

@[simp] theorem size_geometricPrefix (d : ℕ) (a : Array ℤ) (length : ℕ) :
    (geometricPrefix d a length).size = length := by
  induction length with
  | zero => rfl
  | succ length ih => simp [geometricPrefix, ih]

theorem coeff_mul_geometric (A : ℤ⟦X⟧) (d n : ℕ) (hd : 0 < d) :
    coeff n (A * durfeeGeometricFactor d) = coeff n A +
      if d ≤ n then coeff (n - d) (A * durfeeGeometricFactor d) else 0 := by
  have h : (A * durfeeGeometricFactor d) * (1 - X ^ d) = A := by
    rw [mul_assoc, durfeeGeometricFactor_mul d (Nat.ne_of_gt hd), mul_one]
  have hc := congrArg (coeff n) h
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow'] at hc
  exact sub_eq_iff_eq_add.mp hc

theorem restrictedPairSeries_succ_eq_twice (d : ℕ) :
    restrictedPairSeries (d + 1) =
      restrictedPairSeries d * durfeeGeometricFactor (d + 1) * durfeeGeometricFactor (d + 1) := by
  unfold restrictedPairSeries
  rw [Finset.prod_range_succ, pow_two, mul_assoc]

private theorem getElem!_push_lt {α : Type*} [Inhabited α] (a : Array α) (x : α)
    (i : ℕ) (hi : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simpa using Nat.lt_succ_of_lt hi), getElem!_pos a i hi]
  rw [Array.getElem_push_lt hi]

private theorem getElem!_push_size {α : Type*} [Inhabited α] (a : Array α) (x : α) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

theorem geometricPrefix_correct (A : ℤ⟦X⟧) {d : ℕ} (hd : 0 < d) (a : Array ℤ)
    (length : ℕ) (ha : ∀ i < length, a[i]! = coeff i A) :
    ∀ i < length, (geometricPrefix d a length)[i]! = coeff i (A * durfeeGeometricFactor d) := by
  induction length with
  | zero => simp
  | succ length ih =>
    have ih' := ih (fun i hi => ha i (Nat.lt_succ_of_lt hi))
    intro i hi
    rw [geometricPrefix]
    by_cases hlt : i < length
    · rw [getElem!_push_lt _ _ _ (by simpa using hlt)]
      exact ih' i hlt
    · have hEq : i = length := by omega
      subst i
      have hp := getElem!_push_size (geometricPrefix d a length)
        (a[length]! + if d ≤ length then (geometricPrefix d a length)[length - d]! else 0)
      rw [size_geometricPrefix] at hp
      rw [hp]
      rw [ha length hi, coeff_mul_geometric A d length hd]
      split_ifs with h
      · rw [ih' (length - d) (by omega)]
      · rfl

/-- One array per number of allowed part sizes, with two geometric passes per size. -/
def pairCoefficientRows (length : ℕ) : ℕ → Array (Array ℤ)
  | 0 => #[Array.ofFn (fun i : Fin length => if i.val = 0 then 1 else 0)]
  | d + 1 =>
    let rows := pairCoefficientRows length d
    let first := geometricPrefix (d + 1) rows.back! length
    rows.push (geometricPrefix (d + 1) first length)

@[simp] theorem size_pairCoefficientRows (length degree : ℕ) :
    (pairCoefficientRows length degree).size = degree + 1 := by
  induction degree with
  | zero => rfl
  | succ degree ih => simp [pairCoefficientRows, ih]

private theorem pairCoefficientRows_back (length degree : ℕ) :
    (pairCoefficientRows length degree).back! = (pairCoefficientRows length degree)[degree]! := by
  cases degree with
  | zero =>
    unfold pairCoefficientRows
    rw [getElem!_pos _ _ (by simp)]
    rfl
  | succ degree =>
    unfold pairCoefficientRows
    rw [Array.back!_push]
    symm
    simpa only [size_pairCoefficientRows] using getElem!_push_size (pairCoefficientRows length degree)
      (geometricPrefix (degree + 1)
        (geometricPrefix (degree + 1) (pairCoefficientRows length degree).back! length) length)

theorem pairCoefficientRows_correct (length degree : ℕ) :
    ∀ d ≤ degree, ∀ n < length,
      ((pairCoefficientRows length degree)[d]!)[n]! = coeff n (restrictedPairSeries d) := by
  induction degree with
  | zero =>
    intro d hd n hn
    have hEq : d = 0 := by omega
    subst d
    rw [pairCoefficientRows, getElem!_pos
      (#[Array.ofFn (fun i : Fin length => if i.val = 0 then (1 : ℤ) else 0)]) 0 (by simp)]
    change (Array.ofFn (fun i : Fin length => if i.val = 0 then (1 : ℤ) else 0))[n]! = _
    have hn' : n < (Array.ofFn (fun i : Fin length => if i.val = 0 then (1 : ℤ) else 0)).size := by
      simpa using hn
    rw [getElem!_pos _ n hn', Array.getElem_ofFn]
    simp [restrictedPairSeries, PowerSeries.coeff_one]
  | succ degree ih =>
    intro d hd n hn
    rw [pairCoefficientRows]
    by_cases hlt : d ≤ degree
    · rw [getElem!_push_lt _ _ _ (by simp; omega)]
      exact ih d hlt n hn
    · have hEq : d = degree + 1 := by omega
      subst d
      have hp := getElem!_push_size (pairCoefficientRows length degree)
        (geometricPrefix (degree + 1)
          (geometricPrefix (degree + 1) (pairCoefficientRows length degree).back! length) length)
      rw [size_pairCoefficientRows] at hp
      rw [hp]
      have hfirst := geometricPrefix_correct (restrictedPairSeries degree)
        (Nat.succ_pos degree) (pairCoefficientRows length degree).back! length
        (fun i hi => by rw [pairCoefficientRows_back]; exact ih degree le_rfl i hi)
      rw [geometricPrefix_correct _ (Nat.succ_pos degree) _ _ hfirst n hn]
      rw [restrictedPairSeries_succ_eq_twice]

/-- Read the coefficients of `Qₙ` from lowest to highest degree. The caller supplies the
number of coefficients and a table covering their part sizes and weights. -/
def quotientCoefficients (rows : Array (Array ℤ)) (n m : ℕ) : List ℤ :=
  (List.range m).map fun i => (rows[i + 1]!)[n - (i + 1) * (i + 1)]!

@[simp] theorem length_quotientCoefficients (rows : Array (Array ℤ)) (n m : ℕ) :
    (quotientCoefficients rows n m).length = m := by
  simp [quotientCoefficients]

theorem quotientCoefficients_correct_of_lookup (rows : Array (Array ℤ)) (n m : ℕ)
    (hs : m ≤ n.sqrt)
    (lookup : ∀ d ≤ m, ∀ w ≤ n, (rows[d]!)[w]! = coeff w (restrictedPairSeries d)) :
    quotientCoefficients rows n m =
      List.ofFn (fun i : Fin m => (p n (i.val + 1) : ℤ)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < m := by simpa using h₁
    have hsq : (i + 1) * (i + 1) ≤ n := Nat.le_sqrt.mp (by omega)
    rw [List.getElem_ofFn]
    simp only [quotientCoefficients, List.getElem_map, List.getElem_range]
    rw [lookup (i + 1) (by omega) _ (Nat.sub_le _ _)]
    exact (p_eq_coeff_restrictedPairSeries hsq).symm

theorem quotientCoefficients_correct (length degree n m : ℕ)
    (hn : n < length) (hm : m ≤ degree) (hs : m ≤ n.sqrt) :
    quotientCoefficients (pairCoefficientRows length degree) n m =
      List.ofFn (fun i : Fin m => (p n (i.val + 1) : ℤ)) := by
  apply quotientCoefficients_correct_of_lookup _ _ _ hs
  intro d hd w hw
  exact pairCoefficientRows_correct length degree d (hd.trans hm) w (hw.trans_lt hn)

end DurfeeCCS
