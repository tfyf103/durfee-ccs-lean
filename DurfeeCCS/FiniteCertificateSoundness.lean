module

public import DurfeeCCS.CertificateCheck
public import DurfeeCCS.FiniteRoots

/-! Bind the exact integer witness checker to the paper's Durfee polynomial. -/

@[expose] public section

namespace DurfeeCCS

open Polynomial

/-- The coefficients of the quotient, starting at its constant term. -/
noncomputable def finiteCoefficientList (n : ℕ) : List ℤ :=
  List.ofFn fun i : Fin n.sqrt => (p n (i.val + 1) : ℤ)

private noncomputable def polynomialOfIntCoefficients : List ℤ → ℝ[X]
  | [] => 0
  | c :: cs => C (c : ℝ) + X * polynomialOfIntCoefficients cs

private theorem coeff_polynomialOfIntCoefficients (cs : List ℤ) (d : ℕ) :
    (polynomialOfIntCoefficients cs).coeff d = ((cs[d]?).getD 0 : ℝ) := by
  induction cs generalizing d with
  | nil => simp [polynomialOfIntCoefficients]
  | cons c cs ih =>
    cases d with
    | zero => simp [polynomialOfIntCoefficients]
    | succ d =>
      rw [polynomialOfIntCoefficients, coeff_add, coeff_C, coeff_X_mul, ih]
      simp

private theorem eval_polynomialOfIntCoefficients (cs : List ℤ) (x : ℝ) :
    (polynomialOfIntCoefficients cs).eval x = evalAscending cs x := by
  induction cs with
  | nil => simp [polynomialOfIntCoefficients, evalAscending]
  | cons c cs ih => simp [polynomialOfIntCoefficients, evalAscending, ih]

private theorem polynomialOf_finiteCoefficientList (n : ℕ) :
    polynomialOfIntCoefficients (finiteCoefficientList n) = durfeeQuotientReal n := by
  ext d
  rw [coeff_polynomialOfIntCoefficients, coeff_durfeeQuotientReal]
  by_cases hd : d < n.sqrt
  · have hget : (finiteCoefficientList n)[d]? = some (p n (d + 1) : ℤ) := by
      rw [List.getElem?_eq_getElem (by simpa [finiteCoefficientList] using hd)]
      simp [finiteCoefficientList]
    rw [hget]
    simp
  · have hget : (finiteCoefficientList n)[d]? = none := by
      apply List.getElem?_eq_none
      simpa [finiteCoefficientList] using Nat.le_of_not_lt hd
    have hs : n.sqrt < d + 1 := Nat.lt_succ_of_le (Nat.le_of_not_lt hd)
    rw [hget, p_eq_zero_of_sq_gt (Nat.sqrt_lt.mp hs)]
    simp

/-- A row contains the exact integer coefficients and the dyadic interior points. -/
abbrev FiniteWitnessRow := List ℤ × List (ℕ × ℕ)

def checkFiniteWitnessRow (row : FiniteWitnessRow) : Bool :=
  (row.2.length == row.1.length - 2) && checkCertificate row.1 row.2

def checkFiniteWitnessBlock (rows : List FiniteWitnessRow) : Bool :=
  rows.all checkFiniteWitnessRow

theorem hasFiniteWitnesses_of_checkedRow {n : ℕ} {row : FiniteWitnessRow}
    (hcoeff : row.1 = finiteCoefficientList n) (hcheck : checkFiniteWitnessRow row = true) :
    HasFiniteWitnesses n := by
  obtain ⟨hlen, hsign⟩ := Bool.and_eq_true_iff.mp hcheck
  have hsize : row.2.length = n.sqrt - 2 := by
    simpa [hcoeff, finiteCoefficientList] using (beq_iff_eq.mp hlen)
  obtain ⟨hpos, hmono, hpoints⟩ := checkCertificate_sound hsign
  let j (i : Fin (n.sqrt - 2)) := Fin.cast hsize.symm i
  let y (i : Fin (n.sqrt - 2)) := dyadicValue (row.2.get (j i))
  have heval (x : ℝ) : evalAscending row.1 x = (durfeeQuotientReal n).eval x := by
    rw [← eval_polynomialOfIntCoefficients, hcoeff, polynomialOf_finiteCoefficientList]
  refine ⟨y, fun i => hpos (j i), ?_, ?_⟩
  · intro a b hab
    exact hmono (show j a < j b from hab)
  · intro i
    simpa only [heval, y, j, Fin.val_cast] using hpoints (j i)

theorem hasFiniteWitnesses_of_checkedBlock {lo : ℕ} {rows : List FiniteWitnessRow}
    (hcoeff : ∀ i : Fin rows.length, (rows.get i).1 = finiteCoefficientList (lo + i.val))
    (hcheck : checkFiniteWitnessBlock rows = true) :
    ∀ n, lo ≤ n → n < lo + rows.length → HasFiniteWitnesses n := by
  intro n hlo hhi
  let i : Fin rows.length := ⟨n - lo, by omega⟩
  have hn : lo + i.val = n := by dsimp [i]; omega
  have hi := hasFiniteWitnesses_of_checkedRow (hcoeff i)
    (List.all_eq_true.mp hcheck _ (List.get_mem _ _))
  simpa only [hn] using hi

end DurfeeCCS
