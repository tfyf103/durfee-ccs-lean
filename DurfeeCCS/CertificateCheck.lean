module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Integer verification of the signs in the finite Durfee root certificates. -/

@[expose] public section

namespace DurfeeCCS

/-- Evaluate coefficients in order from constant to leading coefficient. -/
noncomputable def evalAscending : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * evalAscending cs x

/-- Evaluate at a/b using integer arithmetic. The second component tracks the power
of the denominator needed by the next coefficient. -/
def homogeneousHorner (a b : ℤ) : List ℤ → ℤ × ℤ
  | [] => (0, 1)
  | c :: cs =>
    let (value, scale) := homogeneousHorner a b cs
    (c * scale + a * value, b * scale)

theorem homogeneousHorner_scale (a b : ℤ) (cs : List ℤ) :
    (homogeneousHorner a b cs).2 = b ^ cs.length := by
  induction cs with
  | nil => simp [homogeneousHorner]
  | cons c cs ih =>
    change b * (homogeneousHorner a b cs).2 = b ^ (cs.length + 1)
    rw [ih, pow_succ, mul_comm]

/-- Clear the denominator of the real evaluation using a power of the denominator. -/
theorem homogeneousHorner_eq (a b : ℤ) (cs : List ℤ) (hb : b ≠ 0) :
    ((homogeneousHorner a b cs).1 : ℝ) =
      (b : ℝ) ^ (cs.length - 1) * evalAscending cs ((a : ℝ) / (b : ℝ)) := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  induction cs with
  | nil => simp [homogeneousHorner, evalAscending]
  | cons c cs ih =>
    change ((c * (homogeneousHorner a b cs).2 + a * (homogeneousHorner a b cs).1 : ℤ) : ℝ) =
      (b : ℝ) ^ (cs.length + 1 - 1) *
        ((c : ℝ) + (a : ℝ) / (b : ℝ) * evalAscending cs ((a : ℝ) / (b : ℝ)))
    rw [homogeneousHorner_scale, Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_pow,
      ih, Nat.add_sub_cancel]
    cases cs with
    | nil => simp [evalAscending]
    | cons d ds =>
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [pow_succ]
      field_simp

/-- A certificate stores the numerator and the exponent of its power-of-two denominator. -/
def dyadicDenominator (point : ℕ × ℕ) : ℕ := 1 <<< point.2

@[simp] theorem dyadicDenominator_eq (point : ℕ × ℕ) :
    dyadicDenominator point = 2 ^ point.2 := by
  simp [dyadicDenominator, Nat.shiftLeft_eq]

/-- The positive sample coordinate, whose negative is supplied to the polynomial. -/
noncomputable def dyadicValue (point : ℕ × ℕ) : ℝ :=
  (point.1 : ℝ) / (dyadicDenominator point : ℝ)

private theorem dyadicDenominator_pos (point : ℕ × ℕ) :
    0 < dyadicDenominator point := by
  simp

def dyadicHornerStep (u e : ℕ) (state : ℕ × ℕ × ℕ) (c : ℤ) : ℕ × ℕ × ℕ :=
  let (positive, negative, shift) := state
  match c with
  | .ofNat z => ((z <<< shift) + u * negative, u * positive, shift + e)
  | .negSucc z => (u * negative, ((z + 1) <<< shift) + u * positive, shift + e)

/-- The evaluator at a negative dyadic number sums nonnegative contributions separately,
using shifts for denominator powers and postponing subtraction until the sign test. -/
def dyadicHorner (coeffs : List ℤ) (u e : ℕ) : ℕ × ℕ × ℕ :=
  coeffs.reverse.foldl (dyadicHornerStep u e) (0, 0, 0)

private theorem dyadicHorner_cons (c : ℤ) (cs : List ℤ) (u e : ℕ) :
    dyadicHorner (c :: cs) u e = dyadicHornerStep u e (dyadicHorner cs u e) c := by
  simp [dyadicHorner, List.foldl_append]

theorem dyadicHorner_represents (coeffs : List ℤ) (u e : ℕ) :
    let r := dyadicHorner coeffs u e
    ((r.1 : ℤ) - (r.2.1 : ℤ)) =
      (homogeneousHorner (-(u : ℤ)) (dyadicDenominator (u, e) : ℤ) coeffs).1 ∧
    r.2.2 = e * coeffs.length := by
  induction coeffs with
  | nil => simp [dyadicHorner, homogeneousHorner]
  | cons c cs ih =>
    simp only [] at ih ⊢
    rw [dyadicHorner_cons]
    rcases hs : dyadicHorner cs u e with ⟨positive, negative, shift⟩
    rw [hs] at ih
    have hshift : shift = e * cs.length := ih.2
    have hscale : (((2 : ℕ) ^ shift) : ℤ) =
        (dyadicDenominator (u, e) : ℤ) ^ cs.length := by
      rw [hshift, dyadicDenominator_eq, pow_mul, Int.natCast_pow]
    change ((dyadicHornerStep u e (positive, negative, shift) c).1 : ℤ) -
        ((dyadicHornerStep u e (positive, negative, shift) c).2.1 : ℤ) =
        c * (homogeneousHorner (-(u : ℤ)) (dyadicDenominator (u, e) : ℤ) cs).2 +
        -(u : ℤ) * (homogeneousHorner (-(u : ℤ)) (dyadicDenominator (u, e) : ℤ) cs).1 ∧ _
    rw [homogeneousHorner_scale, ← ih.1, ← hscale]
    cases c <;> constructor
    · simp only [dyadicHornerStep, Nat.shiftLeft_eq, Int.natCast_mul, Int.natCast_add,
        Int.natCast_pow, Int.ofNat_eq_natCast]
      ring
    · simp [dyadicHornerStep, hshift, Nat.mul_succ]
    · simp only [dyadicHornerStep, Nat.shiftLeft_eq, Int.natCast_mul, Int.natCast_add,
        Int.natCast_pow, Int.negSucc_eq]
      ring
    · simp [dyadicHornerStep, hshift, Nat.mul_succ]

def checkPointSign (coeffs : List ℤ) (i : ℕ) (point : ℕ × ℕ) : Bool :=
  let (positive, negative, _) := dyadicHorner coeffs point.1 point.2
  if i % 2 = 0 then decide (positive < negative) else decide (negative < positive)

def checkPointOrder (a b : ℕ × ℕ) : Bool :=
  decide (a.1 * dyadicDenominator b < b.1 * dyadicDenominator a)

/-- Check positive numerators, every alternating sign, and every adjacent ordering. -/
def checkCertificate (coeffs : List ℤ) (points : List (ℕ × ℕ)) : Bool :=
  (points.zipIdx.all fun (point, i) => decide (0 < point.1) && checkPointSign coeffs i point) &&
    ((points.zip points.tail).all fun (a, b) => checkPointOrder a b)

private theorem neg_one_pow_succ (i : ℕ) :
    (-1 : ℝ) ^ (i + 1) = if i % 2 = 0 then -1 else 1 := by
  have hi : i + 1 = 2 * (i / 2) + (i % 2 + 1) := by omega
  rw [hi, pow_add, pow_mul]
  have h₂ : (-1 : ℝ) ^ (2 : ℕ) = 1 := by norm_num
  rw [h₂, one_pow, one_mul]
  have hi' : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hi' with h | h <;> simp [h]

private theorem checkPointSign_sound {coeffs : List ℤ} {i : ℕ} {point : ℕ × ℕ}
    (h : checkPointSign coeffs i point = true) :
    0 < (-1 : ℝ) ^ (i + 1) * evalAscending coeffs (-(dyadicValue point)) := by
  let a : ℤ := -(point.1 : ℤ)
  let b : ℤ := dyadicDenominator point
  let r := dyadicHorner coeffs point.1 point.2
  have hrep : (r.1 : ℤ) - (r.2.1 : ℤ) = (homogeneousHorner a b coeffs).1 :=
    (dyadicHorner_represents coeffs point.1 point.2).1
  have hb : 0 < b := Int.natCast_pos.mpr (dyadicDenominator_pos point)
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have harg : (a : ℝ) / (b : ℝ) = -(dyadicValue point) := by simp [a, b, dyadicValue, neg_div]
  have hhom := homogeneousHorner_eq a b coeffs hb.ne'
  rw [harg] at hhom
  have hscale : 0 < (b : ℝ) ^ (coeffs.length - 1) := pow_pos hb' _
  rw [neg_one_pow_succ]
  by_cases hi : i % 2 = 0
  · have hlt : r.1 < r.2.1 := by
      exact of_decide_eq_true (by simpa [checkPointSign, hi, r] using h)
    have hval : (homogeneousHorner a b coeffs).1 < 0 := by
      rw [← hrep]
      exact sub_neg.mpr (Int.ofNat_lt.mpr hlt)
    have hcast : (((homogeneousHorner a b coeffs).1 : ℤ) : ℝ) < 0 := by exact_mod_cast hval
    rw [hhom] at hcast
    simp only [ite_eq_left hi, neg_mul, one_mul]
    apply (mul_pos_iff_of_pos_left hscale).1
    rw [mul_neg]
    exact neg_pos.mpr hcast
  · have hlt : r.2.1 < r.1 := by
      exact of_decide_eq_true (by simpa [checkPointSign, hi, r] using h)
    have hval : 0 < (homogeneousHorner a b coeffs).1 := by
      rw [← hrep]
      exact sub_pos.mpr (Int.ofNat_lt.mpr hlt)
    have hcast : 0 < (((homogeneousHorner a b coeffs).1 : ℤ) : ℝ) := by exact_mod_cast hval
    rw [hhom] at hcast
    simpa [hi] using (mul_pos_iff_of_pos_left hscale).1 hcast

private theorem dyadicValue_lt_of_order {a b : ℕ × ℕ}
    (h : checkPointOrder a b = true) : dyadicValue a < dyadicValue b := by
  have ha : 0 < (dyadicDenominator a : ℝ) := by exact_mod_cast dyadicDenominator_pos a
  have hb : 0 < (dyadicDenominator b : ℝ) := by exact_mod_cast dyadicDenominator_pos b
  have hcross : a.1 * dyadicDenominator b < b.1 * dyadicDenominator a := by
    simpa [checkPointOrder] using h
  apply (div_lt_div_iff₀ ha hb).2
  exact_mod_cast hcross

private theorem strictMono_of_adjacent_check {points : List (ℕ × ℕ)}
    (h : ((points.zip points.tail).all fun (a, b) => checkPointOrder a b) = true) :
    StrictMono (fun i : Fin points.length => dyadicValue (points.get i)) := by
  cases points with
  | nil => exact fun i _ _ => i.elim0
  | cons hd tl =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hi : i.val < ((hd :: tl).zip (hd :: tl).tail).length := by
      simp [List.length_zip]
    have hab := List.all_eq_true.mp h _ (List.getElem_mem hi)
    rw [List.getElem_zip, List.getElem_tail] at hab
    exact dyadicValue_lt_of_order hab

/-- An accepted certificate represents strictly increasing positive samples on which the
polynomial evaluated at their negatives alternates in sign, starting with a negative sign. -/
theorem checkCertificate_sound {coeffs : List ℤ} {points : List (ℕ × ℕ)}
    (h : checkCertificate coeffs points = true) :
    (∀ i : Fin points.length, 0 < dyadicValue (points.get i)) ∧
    StrictMono (fun i : Fin points.length => dyadicValue (points.get i)) ∧
    (∀ i : Fin points.length,
      0 < (-1 : ℝ) ^ (i.val + 1) * evalAscending coeffs (-(dyadicValue (points.get i)))) := by
  obtain ⟨hpts, horder⟩ := Bool.and_eq_true_iff.mp h
  have hi (i : Fin points.length) :
      0 < (points.get i).1 ∧ checkPointSign coeffs i.val (points.get i) = true := by
    have hb : i.val < points.zipIdx.length := by simp
    have hk := List.all_eq_true.mp hpts _ (List.getElem_mem hb)
    rw [List.getElem_zipIdx] at hk
    simpa [List.get_eq_getElem] using hk
  refine ⟨?_, strictMono_of_adjacent_check horder, fun i => checkPointSign_sound (hi i).2⟩
  intro i
  apply div_pos
  · exact_mod_cast (hi i).1
  · exact_mod_cast dyadicDenominator_pos (points.get i)

end DurfeeCCS
