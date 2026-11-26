module

public import DurfeeCCS.CoefficientCertificate
public import DurfeeCCS.DyadicWitnesses

/-! Assemble the coefficient and sign certificates for a contiguous interval of weights. -/

@[expose] public section

namespace DurfeeCCS

def coefficientSlices (columns : List (List ℤ)) (lo count : ℕ) : List (List ℤ) :=
  columns.map fun values => (values.drop lo).take count

private theorem coefficientSlice_length {columns : List (List ℤ)} {lo count limit : ℕ}
    (hlength : ∀ c ∈ columns, c.length = limit) (hbound : lo + count ≤ limit) :
    ∀ c ∈ coefficientSlices columns lo count, c.length = count := by
  intro c hc
  obtain ⟨values, hvalues, rfl⟩ := List.mem_map.mp hc
  rw [List.length_take, List.length_drop, hlength values hvalues]
  omega

private theorem coefficientSlice_correct {columns : List (List ℤ)} {lo count limit : ℕ}
    (hlength : ∀ c ∈ columns, c.length = limit)
    (hcoeff : ∀ j (hj : j < columns.length), CoefficientRowSpec (j + 1) columns[j])
    (hbound : lo + count ≤ limit) (j : ℕ) (hj : j < (coefficientSlices columns lo count).length)
    (i : ℕ) (hi : i < count) :
    (coefficientSlices columns lo count)[j][i]! = (p (lo + i) (j + 1) : ℤ) := by
  have hj' : j < columns.length := by simpa [coefficientSlices] using hj
  have hm := hlength columns[j] (List.getElem_mem hj')
  have hb : lo + i < columns[j].length := by omega
  have hslice : i < ((coefficientSlices columns lo count)[j]).length := by
    simpa [coefficientSlice_length hlength hbound _ (List.getElem_mem hj)] using hi
  rw [getElem!_pos ((coefficientSlices columns lo count)[j]) i hslice]
  simpa only [coefficientSlices, List.getElem_map, List.getElem_take, List.getElem_drop] using
    hcoeff j hj' (lo + i) hb

/-- A certificate block whose coefficient and sign checks pass verifies (77) throughout its
range. The certified coefficient columns are shared across all the blocks. -/
theorem finiteWitnessBlock_of_checks {columns : List (List ℤ)} {rows : List FiniteWitnessRow}
    {lo limit : ℕ}
    (hlength : ∀ c ∈ columns, c.length = limit)
    (hcoeff : ∀ j (hj : j < columns.length), CoefficientRowSpec (j + 1) columns[j])
    (hbound : lo + rows.length ≤ limit)
    (hmatch : checkCoefficientBlock lo (coefficientSlices columns lo rows.length)
      (rows.map Prod.fst) = true)
    (hsign : checkFiniteWitnessBlock rows = true) :
    ∀ n, lo ≤ n → n < lo + rows.length → HasDyadicFiniteWitnesses n := by
  apply hasDyadicFiniteWitnesses_of_checkedBlock (lo := lo) (rows := rows) ?_ hsign
  intro i
  have hlen : (rows.map Prod.fst).length = rows.length := List.length_map _
  let j : Fin (rows.map Prod.fst).length := Fin.cast hlen.symm i
  have hlen' : ∀ c ∈ coefficientSlices columns lo rows.length, c.length = (rows.map Prod.fst).length :=
    fun c hc => (coefficientSlice_length hlength hbound c hc).trans hlen.symm
  have href (d : ℕ) (hd : d < (coefficientSlices columns lo rows.length).length) (t : ℕ)
      (ht : t < (rows.map Prod.fst).length) :
      (coefficientSlices columns lo rows.length)[d][t]! = (p (lo + t) (d + 1) : ℤ) :=
    coefficientSlice_correct hlength hcoeff hbound d hd t (by simpa only [hlen] using ht)
  simpa only [finiteCoefficientList, j, Fin.val_cast, List.getElem_map, List.get_eq_getElem] using
    checkCoefficientBlock_sound hlen' href hmatch j

end DurfeeCCS
