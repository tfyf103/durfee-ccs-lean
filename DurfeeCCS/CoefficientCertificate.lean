module

public import DurfeeCCS.EquationOne
public import DurfeeCCS.Degree
import Mathlib.Tactic.Ring

/-! A certificate of the double geometric-factor recurrence, organized by Durfee side. -/

@[expose] public section

open PowerSeries

namespace DurfeeCCS

private noncomputable def sideSeries (d : ℕ) : ℤ⟦X⟧ :=
  X ^ (d * d) * restrictedPairSeries d

private theorem coeff_sideSeries (n d : ℕ) : coeff n (sideSeries d) = (p n d : ℤ) :=
  (p_eq_coeff_shifted n d).symm

private theorem sideSeries_step (d : ℕ) :
    sideSeries (d + 1) * (1 - X ^ (d + 1)) ^ 2 = X ^ (2 * d + 1) * sideSeries d := by
  have hgeom := durfeeGeometricFactor_mul (d + 1) (Nat.succ_ne_zero d)
  have hprod : restrictedPairSeries (d + 1) =
      restrictedPairSeries d * durfeeGeometricFactor (d + 1) ^ 2 :=
    Finset.prod_range_succ _ _
  simp only [sideSeries, hprod]
  calc
    _ = (X ^ ((d + 1) * (d + 1)) * restrictedPairSeries d) *
        (durfeeGeometricFactor (d + 1) * (1 - X ^ (d + 1))) ^ 2 := by ring
    _ = X ^ ((d + 1) * (d + 1)) * restrictedPairSeries d := by rw [hgeom, one_pow, mul_one]
    _ = _ := by rw [← mul_assoc, ← pow_add]; congr 1; ring

/-- The squared denominator gives the direct recurrence obtained by eliminating the
intermediate row of the two geometric passes. An index below a shift contributes zero. -/
theorem coefficient_pair_recurrence (d n : ℕ) :
    (p n (d + 1) : ℤ) =
      (if 2 * d + 1 ≤ n then (p (n - (2 * d + 1)) d : ℤ) else 0) +
      ((if d + 1 ≤ n then (p (n - (d + 1)) (d + 1) : ℤ) else 0) +
       (if d + 1 ≤ n then (p (n - (d + 1)) (d + 1) : ℤ) else 0)) -
      (if (d + 1) + (d + 1) ≤ n then (p (n - ((d + 1) + (d + 1))) (d + 1) : ℤ) else 0) := by
  have h := sideSeries_step d
  have hrearrange :
      sideSeries (d + 1) * (1 - X ^ (d + 1)) ^ 2 =
        sideSeries (d + 1) -
          (sideSeries (d + 1) * X ^ (d + 1) + sideSeries (d + 1) * X ^ (d + 1)) +
          sideSeries (d + 1) * X ^ ((d + 1) + (d + 1)) := by rw [pow_add _ (d + 1)]; ring
  rw [hrearrange] at h
  have hc := congrArg (coeff n) h
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_X_pow_mul', coeff_sideSeries] at hc
  omega

def shiftRow (offset : ℕ) (row : List ℤ) : List ℤ :=
  List.replicate offset 0 ++ row

private theorem getElem?_shiftRow {row : List ℤ} {i offset : ℕ} (hi : i < row.length) :
    (shiftRow offset row)[i]? = if h : offset ≤ i then some (row[i - offset]'(by omega)) else some 0 := by
  by_cases h : offset ≤ i
  · rw [dite_eq_left h, shiftRow, List.getElem?_append_right (by simpa using h)]
    simp [List.getElem?_eq_getElem (show i - offset < row.length by omega)]
  · rw [dite_eq_right h, shiftRow, List.getElem?_append_left (by simpa using Nat.lt_of_not_ge h)]
    simp [Nat.lt_of_not_ge h]

/-- This bounded row records `p(0,d), p(1,d), …`, including the out-of-range zero entries. -/
def CoefficientRowSpec (d : ℕ) (row : List ℤ) : Prop :=
  ∀ i (hi : i < row.length), row[i] = (p i d : ℤ)

def verifyPairRow (d : ℕ) (previous current : List ℤ) : Bool :=
  (current.length == previous.length) &&
    (current == (List.zipWith (fun a bc => a + (bc.1 + bc.1) - bc.2)
      (shiftRow (2 * d + 1) previous)
      (List.zipWith Prod.mk (shiftRow (d + 1) current) (shiftRow ((d + 1) + (d + 1)) current))).take
        current.length)

theorem verifyPairRow_length {d : ℕ} {previous current : List ℤ}
    (h : verifyPairRow d previous current = true) : current.length = previous.length := by
  rw [verifyPairRow, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem verifyPairRow_sound {d : ℕ} {previous current : List ℤ}
    (hprev : CoefficientRowSpec d previous) (h : verifyPairRow d previous current = true) :
    CoefficientRowSpec (d + 1) current := by
  rw [verifyPairRow, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨hlen, heq⟩ := h
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    have hprevBound : i < previous.length := by omega
    have hprevious : (shiftRow (2 * d + 1) previous)[i]? =
        some (if 2 * d + 1 ≤ i then (p (i - (2 * d + 1)) d : ℤ) else 0) := by
      rw [getElem?_shiftRow hprevBound]
      split_ifs with h
      · exact congrArg some (hprev _ (by omega))
      · rfl
    have hcurrent (offset : ℕ) (ho : 0 < offset) : (shiftRow offset current)[i]? =
        some (if offset ≤ i then (p (i - offset) (d + 1) : ℤ) else 0) := by
      rw [getElem?_shiftRow hi]
      split_ifs with h
      · exact congrArg some (ih _ (by omega) (by omega))
      · rfl
    have hlocal := congrArg (fun row : List ℤ => row[i]?) heq
    simp only [List.getElem?_eq_getElem hi, List.getElem?_take, ite_eq_left hi, List.getElem?_zipWith, hprevious,
      hcurrent (d + 1) (by omega), hcurrent ((d + 1) + (d + 1)) (by omega),
      Option.some.injEq] at hlocal
    exact hlocal.trans (coefficient_pair_recurrence d i).symm

/-- The column for side zero up to weight `stop`. -/
def baseCoefficientRow (stop : ℕ) : List ℤ := 1 :: List.replicate stop 0

theorem baseCoefficientRow_spec (stop : ℕ) : CoefficientRowSpec 0 (baseCoefficientRow stop) := by
  intro i hi
  cases i with
  | zero => simp [baseCoefficientRow]
  | succ i => simp [baseCoefficientRow, p_zero_of_pos]

theorem coefficientColumn_slice {d lo len : ℕ} {column : List ℤ}
    (h : CoefficientRowSpec d column) (hbound : lo + len ≤ column.length)
    {i : ℕ} (hi : i < len) :
    ((column.drop lo).take len)[i]! = (p (lo + i) d : ℤ) := by
  have hslice : i < ((column.drop lo).take len).length := by
    simp only [List.length_take, List.length_drop]
    omega
  rw [getElem!_pos ((column.drop lo).take len) i hslice, List.getElem_take, List.getElem_drop]
  exact h _ (by omega)

def CoefficientColumnsSpec (firstSide : ℕ) (columns : List (List ℤ)) : Prop :=
  ∀ j (hj : j < columns.length), CoefficientRowSpec (firstSide + j) columns[j]

theorem coefficientColumnsSpec_nil (firstSide : ℕ) : CoefficientColumnsSpec firstSide [] := by
  intro j hj
  simp at hj

theorem coefficientColumnsSpec_cons {firstSide : ℕ} {column : List ℤ} {columns : List (List ℤ)}
    (h : CoefficientRowSpec firstSide column) (hs : CoefficientColumnsSpec (firstSide + 1) columns) :
    CoefficientColumnsSpec firstSide (column :: columns) := by
  intro j hj
  cases j with
  | zero => simpa using h
  | succ j => simpa [Nat.add_assoc, Nat.add_comm 1 j] using hs j (by simpa using hj)

/-- Produce weight-ordered rows from side-ordered columns. The folds traverse each column once. -/
def transposeCoefficientColumns (height : ℕ) : List (List ℤ) → List (List ℤ)
  | [] => List.replicate height []
  | col :: cols => List.zipWith List.cons col (transposeCoefficientColumns height cols)

private theorem getElem?_transposeCoefficientColumns (height : ℕ) (columns : List (List ℤ))
    (i : ℕ) (hi : i < height) (hlen : ∀ c ∈ columns, c.length = height) :
    (transposeCoefficientColumns height columns)[i]? =
      some (columns.map fun column => column[i]!) := by
  induction columns with
  | nil => simp [transposeCoefficientColumns, hi]
  | cons col cols ih =>
    have hc : i < col.length := by rw [hlen col (by simp)]; exact hi
    simp only [transposeCoefficientColumns, List.getElem?_zipWith, List.getElem?_eq_getElem hc,
      ih (fun c h => hlen c (by simp [h])), List.map_cons, getElem!_pos col i hc]

/-- All coefficients in a block's witness rows have the correct values and lengths. Its
columns hold the slice starting at weight `lo`, with one column per positive Durfee side. -/
def checkCoefficientBlock (lo : ℕ) (columns rows : List (List ℤ)) : Bool :=
  ((rows.zipIdx lo).all fun ⟨row, n⟩ =>
    decide (row.length * row.length ≤ n ∧ n < (row.length + 1) * (row.length + 1))) &&
  (rows == List.zipWith (fun row ref => ref.take row.length)
    rows (transposeCoefficientColumns rows.length columns))

theorem checkCoefficientBlock_sound {lo : ℕ} {columns rows : List (List ℤ)}
    (hlen : ∀ c ∈ columns, c.length = rows.length)
    (hcolumns : ∀ j (hj : j < columns.length) i, i < rows.length →
      columns[j][i]! = (p (lo + i) (j + 1) : ℤ))
    (h : checkCoefficientBlock lo columns rows = true) (i : Fin rows.length) :
    rows[i.val] = List.ofFn (fun j : Fin (lo + i.val).sqrt => (p (lo + i.val) (j.val + 1) : ℤ)) := by
  rw [checkCoefficientBlock, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hsquares, hzip⟩ := h
  have hi : i.val < (rows.zipIdx lo).length := by simp
  have hbounds := hsquares _ (List.getElem_mem hi)
  rw [List.getElem_zipIdx hi] at hbounds
  have hbounds := of_decide_eq_true hbounds
  have hsqrt : rows[i.val].length = (lo + i.val).sqrt :=
    le_antisymm (Nat.le_sqrt.mpr hbounds.1) (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr hbounds.2))
  have hcoeffs := congrArg (fun rs : List (List ℤ) => rs[i.val]?) hzip
  simp only [List.getElem?_eq_getElem i.isLt, List.getElem?_zipWith,
    getElem?_transposeCoefficientColumns rows.length columns i.val i.isLt hlen,
    Option.some.injEq] at hcoeffs
  apply List.ext_getElem (by simpa using hsqrt)
  intro j hj hj'
  have hbound : j < columns.length := by
    have hl := congrArg List.length hcoeffs
    simp only [List.length_take, List.length_map] at hl
    exact hj.trans_le (hl.symm ▸ min_le_right _ _)
  rw [List.getElem_ofFn]
  have hentry := List.getElem_of_eq hcoeffs hj
  simp only [List.getElem_take, List.getElem_map] at hentry
  exact hentry.trans (hcolumns j hbound i.val i.isLt)

end DurfeeCCS
