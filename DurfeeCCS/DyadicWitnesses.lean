module

public import DurfeeCCS.FiniteCertificateSoundness

/-! Keep the exact dyadic coordinates when transferring the sign certificates to (77). -/

public section

namespace DurfeeCCS

open Polynomial

/-- The ordered positive points in (77), presented as numerators and power-of-two exponents. -/
@[expose] def HasDyadicFiniteWitnesses (n : ℕ) : Prop :=
  ∃ w : Fin (n.sqrt - 2) → ℕ × ℕ,
    (∀ i, 0 < dyadicValue (w i)) ∧ StrictMono (fun i => dyadicValue (w i)) ∧
      (∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * (durfeeQuotientReal n).eval (-(dyadicValue (w i))))

theorem HasDyadicFiniteWitnesses.toFinite {n : ℕ} (h : HasDyadicFiniteWitnesses n) :
    HasFiniteWitnesses n := by
  obtain ⟨w, hpos, hmono, hsign⟩ := h
  exact ⟨fun i => dyadicValue (w i), hpos, hmono, hsign⟩

private theorem evalAscending_eq_of_coeffs (cs : List ℤ) (P : ℝ[X]) (x : ℝ)
    (h : ∀ d, P.coeff d = ((cs[d]?).getD 0 : ℝ)) : evalAscending cs x = P.eval x := by
  induction cs generalizing P with
  | nil =>
    have hP : P = 0 := by ext d; simpa using h d
    simp [hP, evalAscending]
  | cons c cs ih =>
    have h₀ : P.coeff 0 = (c : ℝ) := by simpa using h 0
    have hshift (d : ℕ) : P.divX.coeff d = ((cs[d]?).getD 0 : ℝ) := by
      simpa using h (d + 1)
    calc
      evalAscending (c :: cs) x = (X * P.divX + C (P.coeff 0)).eval x := by
        simp [evalAscending, ih P.divX hshift, h₀, add_comm]
      _ = P.eval x := congrArg (Polynomial.eval x) P.X_mul_divX_add

private theorem evalAscending_finiteCoefficientList (n : ℕ) (x : ℝ) :
    evalAscending (finiteCoefficientList n) x = (durfeeQuotientReal n).eval x := by
  apply evalAscending_eq_of_coeffs
  intro d
  rw [coeff_durfeeQuotientReal]
  by_cases hd : d < n.sqrt
  · rw [List.getElem?_eq_getElem (by simpa [finiteCoefficientList] using hd)]
    simp [finiteCoefficientList]
  · have hget : (finiteCoefficientList n)[d]? = none := by
      apply List.getElem?_eq_none
      simpa [finiteCoefficientList] using Nat.le_of_not_lt hd
    have hs : n.sqrt < d + 1 := Nat.lt_succ_of_le (Nat.le_of_not_lt hd)
    rw [hget, p_eq_zero_of_sq_gt (Nat.sqrt_lt.mp hs)]
    simp

theorem hasDyadicFiniteWitnesses_of_checkedRow {n : ℕ} {row : FiniteWitnessRow}
    (hcoeff : row.1 = finiteCoefficientList n) (hcheck : checkFiniteWitnessRow row = true) :
    HasDyadicFiniteWitnesses n := by
  obtain ⟨hlen, hsign⟩ := Bool.and_eq_true_iff.mp hcheck
  have hsize : row.2.length = n.sqrt - 2 := by
    simpa [hcoeff, finiteCoefficientList] using (beq_iff_eq.mp hlen)
  obtain ⟨hpos, hmono, hpoints⟩ := checkCertificate_sound hsign
  let j (i : Fin (n.sqrt - 2)) := Fin.cast hsize.symm i
  let w (i : Fin (n.sqrt - 2)) := row.2.get (j i)
  refine ⟨w, fun i => hpos (j i), ?_, ?_⟩
  · intro a b hab
    exact hmono (show j a < j b from hab)
  · intro i
    simpa only [hcoeff, evalAscending_finiteCoefficientList, w, j, Fin.val_cast] using hpoints (j i)

theorem hasDyadicFiniteWitnesses_of_checkedBlock {lo : ℕ} {rows : List FiniteWitnessRow}
    (hcoeff : ∀ i : Fin rows.length, (rows.get i).1 = finiteCoefficientList (lo + i.val))
    (hcheck : checkFiniteWitnessBlock rows = true) :
    ∀ n, lo ≤ n → n < lo + rows.length → HasDyadicFiniteWitnesses n := by
  intro n hlo hhi
  let i : Fin rows.length := ⟨n - lo, by omega⟩
  have hn : lo + i.val = n := by dsimp [i]; omega
  have hi := hasDyadicFiniteWitnesses_of_checkedRow (hcoeff i)
    (List.all_eq_true.mp hcheck _ (List.get_mem _ _))
  simpa only [hn] using hi

end DurfeeCCS
