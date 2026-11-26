module

public import DurfeeCCS.Step14.RademacherFarey
public import DurfeeCCS.Step14.RademacherContour
import all DurfeeCCS.Step14.RademacherContour

/-! Parametric Ford arcs, including their shared endpoints and the two halves
of the endpoint arc of denominator one. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step14

open Complex Set MeasureTheory
open UpperHalfPlane (upperHalfPlaneSet)
open DurfeeCCS.Step06 DurfeeCCS.Step08

/-- The forward Ford arc with center fraction a/q and inverse coordinate
having real part 1 and imaginary part v. -/
def fordPath (a q : ℤ) (v : ℝ) : ℂ :=
  (a : ℂ) / q + I / ((q : ℂ) ^ 2 * verticalPoint 1 v)

/-- The tangent vector of the forward Ford arc. -/
def fordVelocity (q : ℤ) (v : ℝ) : ℂ :=
  1 / ((q : ℂ) ^ 2 * (verticalPoint 1 v) ^ 2)

def fordPathIntegrand (n : ℕ) (a q : ℤ) (v : ℝ) : ℂ :=
  twoColourFareyIntegrand n (fordPath a q v) * fordVelocity q v

private theorem fordVertical_ne_zero (v : ℝ) : verticalPoint 1 v ≠ 0 := by
  apply verticalPoint_ne_zero (by norm_num : (0 : ℝ) < 1)

private theorem hasDerivAt_fordVertical (v : ℝ) : HasDerivAt (verticalPoint 1) I v := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const I
  change HasDerivAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) I v
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using h.const_add (c := 1)

theorem hasDerivAt_fordPath (a q : ℤ) (hq : q ≠ 0) (v : ℝ) :
    HasDerivAt (fordPath a q) (fordVelocity q v) v := by
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hw := fordVertical_ne_zero v
  have hd := ((hasDerivAt_const v I).div ((hasDerivAt_fordVertical v).const_mul ((q : ℂ) ^ 2))
    (mul_ne_zero (pow_ne_zero 2 hqc) hw)).const_add ((a : ℂ) / q)
  convert hd using 1
  · rfl
  · unfold fordVelocity
    field_simp [hqc, hw]
    ring_nf
    simp [Complex.I_sq]

theorem continuous_fordVelocity (q : ℤ) (hq : q ≠ 0) : Continuous (fordVelocity q) := by
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hw : Continuous (verticalPoint 1) :=
    continuous_iff_continuousAt.mpr (fun v => (hasDerivAt_fordVertical v).continuousAt)
  unfold fordVelocity
  exact continuous_const.div (continuous_const.mul (hw.pow 2)) (fun v =>
    mul_ne_zero (pow_ne_zero 2 hqc) (pow_ne_zero 2 (fordVertical_ne_zero v)))

private theorem fordPath_eq_real_cast (a q : ℤ) (v : ℝ) :
    fordPath a q v =
      (((a : ℝ) / q : ℝ) : ℂ) + I * (((1 / (q : ℝ) ^ 2 : ℝ) : ℂ) *
        (verticalPoint 1 v)⁻¹) := by
  unfold fordPath
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem fordPath_mem_upperHalfPlane (a q : ℤ) (hq : q ≠ 0) (v : ℝ) :
    fordPath a q v ∈ upperHalfPlaneSet := by
  change 0 < (fordPath a q v).im
  rw [fordPath_eq_real_cast]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.mul_re, Complex.ofReal_re, zero_mul, one_mul, zero_add, sub_zero,
    Complex.inv_re, verticalPoint_re]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hw := Complex.normSq_pos.mpr (fordVertical_ne_zero v)
  positivity

private theorem fordPath_eq_of_normalized {a q : ℤ} (hq : q ≠ 0) {v : ℝ} {z : ℂ}
    (hz : -I * (q : ℂ) ^ 2 * (z - (((a : ℝ) / q : ℝ) : ℂ)) = (verticalPoint 1 v)⁻¹) :
    fordPath a q v = z := by
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hfactor : I * ((1 / (q : ℂ) ^ 2) * (-I * (q : ℂ) ^ 2)) = 1 := by
    field_simp [hqc]
    ring_nf
    simp [Complex.I_sq]
  calc
    _ = ((a : ℂ) / q) + (I * ((1 / (q : ℂ) ^ 2) * (-I * (q : ℂ) ^ 2))) *
        (z - ((a : ℂ) / q)) := by
      rw [fordPath_eq_real_cast, ← hz]
      push_cast
      ring
    _ = z := by rw [hfactor, one_mul, add_sub_cancel]

/-- The Ford arcs at adjacent fractions are stitched at the same point, with
the right inverse ordinate s/q in the first arc and the left ordinate -q/s in
the second arc. -/
theorem fordPath_at_farey_contact {a q b s : ℤ} (hq : 0 < q) (hs : 0 < s)
    (hdet : q * b - a * s = 1) :
    fordPath a q ((s : ℝ) / q) = fordContact a q b s ∧
    fordPath b s (-(q : ℝ) / s) = fordContact a q b s := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hl : (fordEndpoint q (-s : ℝ))⁻¹ = verticalPoint 1 ((s : ℝ) / q) := by
    rw [fordEndpoint_inv hqr]
    simp [verticalPoint, neg_div, sub_neg_eq_add]
  have hr : (fordEndpoint s q)⁻¹ = verticalPoint 1 (-(q : ℝ) / s) := by
    rw [fordEndpoint_inv hsr]
    simp [verticalPoint, neg_div, sub_eq_add_neg]
  obtain ⟨htl, htr, _, _⟩ := fordContact_geometry hq hs hdet
  exact ⟨fordPath_eq_of_normalized hq.ne' (by rw [← hl, inv_inv]; exact htl),
    fordPath_eq_of_normalized hs.ne' (by rw [← hr, inv_inv]; exact htr)⟩

@[simp] theorem fordPath_zero_one_zero : fordPath 0 1 0 = I := by
  simp [fordPath, verticalPoint]

@[simp] theorem fordPath_one_one_zero : fordPath 1 1 0 = 1 + I := by
  simp [fordPath, verticalPoint]

theorem fordPath_one_one_eq_zero_one_add_one (v : ℝ) :
    fordPath 1 1 v = fordPath 0 1 v + 1 := by
  simp [fordPath, add_comm]

/-- The two denominator-one arcs have identical integrands after horizontal
translation by 1. -/
theorem fordPathIntegrand_one_one (n : ℕ) (v : ℝ) :
    fordPathIntegrand n 1 1 v = fordPathIntegrand n 0 1 v := by
  unfold fordPathIntegrand
  rw [fordPath_one_one_eq_zero_one_add_one, twoColourFareyIntegrand_periodic n]

theorem intervalIntegrable_fordPathIntegrand (n : ℕ) (a q : ℤ) (hq : 0 < q) (l r : ℝ) :
    IntervalIntegrable (fordPathIntegrand n a q) volume l r := by
  apply Continuous.intervalIntegrable
  have hp : Continuous (fordPath a q) :=
    continuous_iff_continuousAt.mpr (fun v => (hasDerivAt_fordPath a q hq.ne' v).continuousAt)
  exact (continuousOn_univ.mp ((differentiableOn_twoColourFareyIntegrand n).continuousOn.comp
    hp.continuousOn (fun v _ => fordPath_mem_upperHalfPlane a q hq.ne' v))).mul
    (continuous_fordVelocity q hq.ne')

/-- Merge the final half of the denominator-one arc with its initial half. -/
theorem integral_fordPath_denominator_one_merge (n : ℕ) (l r : ℝ) :
    (∫ v in l..0, fordPathIntegrand n 1 1 v) +
      (∫ v in 0..r, fordPathIntegrand n 0 1 v) = ∫ v in l..r, fordPathIntegrand n 0 1 v := by
  simp_rw [fordPathIntegrand_one_one]
  exact intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_fordPathIntegrand n 0 1 (by decide) l 0)
    (intervalIntegrable_fordPathIntegrand n 0 1 (by decide) 0 r)

/-- The coefficient integral over the chain of Ford arcs. The initial point
is the contact of the 0/1 circle with the previous chain's final circle.
The terminal point is its translate by 1, so the first arc is a full arc
and the second copy of the denominator-one circle does not occur in the sum. -/
theorem twoColourPartitionCount_eq_fordPath_merged_sum (n m : ℕ) (a q : ℕ → ℤ)
    (hq : ∀ j ≤ m, 0 < q j) (ha₀ : a 0 = 0) (hq₀ : q 0 = 1)
    (ha₁ : a m = 1) (hq₁ : q m = 1)
    (hdet : ∀ j < m, q j * a (j + 1) - a j * q (j + 1) = 1) :
    (twoColourPartitionCount n : ℂ) =
      (∫ v in (-(q (m - 1) : ℝ))..(q 1 : ℝ), fordPathIntegrand n 0 1 v) +
      ∑ j ∈ Finset.range (m - 1),
        ∫ v in (-(q j : ℝ) / (q (j + 1) : ℝ))..((q (j + 2) : ℝ) / (q (j + 1) : ℝ)),
          fordPathIntegrand n (a (j + 1)) (q (j + 1)) v := by
  have hm : 0 < m := by
    by_contra! h
    rw [show m = 0 by omega, ha₀] at ha₁
    norm_num at ha₁
  let start := fordPath 0 1 (-(q (m - 1) : ℝ))
  let vertex (j : ℕ) := if j = 0 then start else fordContact (a (j - 1)) (q (j - 1)) (a j) (q j)
  let l (j : ℕ) := if j = 0 then -(q (m - 1) : ℝ) else -(q (j - 1) : ℝ) / (q j : ℝ)
  let r (j : ℕ) := (q (j + 1) : ℝ) / (q j : ℝ)
  let γ (j : ℕ) := fordPath (a j) (q j)
  let γ' (j : ℕ) := fordVelocity (q j)
  have hheight : 0 < start.im := fordPath_mem_upperHalfPlane 0 1 (by decide) _
  have hfirst : vertex 0 = (start.re : ℂ) + (start.im : ℂ) * I := by
    simp only [vertex, ite_true]
    exact (Complex.re_add_im _).symm
  have hlast : vertex m = ((start.re + 1 : ℝ) : ℂ) + (start.im : ℂ) * I := by
    have hidx : m - 1 + 1 = m := by omega
    have hd := hdet (m - 1) (by omega)
    rw [hidx] at hd
    have hh := (fordPath_at_farey_contact (hq (m - 1) (by omega)) (hq m le_rfl) hd).2.symm
    rw [ha₁, hq₁, Int.cast_one, div_one, fordPath_one_one_eq_zero_one_add_one] at hh
    rw [show vertex m = fordContact (a (m - 1)) (q (m - 1)) (a m) (q m) by
      simp only [vertex, hm.ne', ite_false], ha₁, hq₁, hh, Complex.ofReal_add, Complex.ofReal_one,
      add_right_comm, Complex.re_add_im]
  have hleft (j : ℕ) (hj : j < m) : γ j (l j) = vertex j := by
    by_cases hj₀ : j = 0
    · subst j
      simp [γ, l, vertex, start, ha₀, hq₀]
    · have hidx : j - 1 + 1 = j := by omega
      have hd := hdet (j - 1) (by omega)
      rw [hidx] at hd
      simpa only [γ, l, vertex, hj₀, ite_false] using
        (fordPath_at_farey_contact (hq (j - 1) (by omega)) (hq j (by omega)) hd).2
  have hright (j : ℕ) (hj : j < m) : γ j (r j) = vertex (j + 1) := by
    simpa only [γ, r, vertex, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] using
      (fordPath_at_farey_contact (hq j (by omega)) (hq (j + 1) (by omega)) (hdet j hj)).1
  have ht := twoColourPartitionCount_eq_farey_arc_sum n m hheight start.re
    vertex l r γ γ' hfirst hlast hleft hright
    (fun j hj v _ => fordPath_mem_upperHalfPlane (a j) (q j) (hq j (by omega)).ne' v)
    (fun j hj v _ => hasDerivAt_fordPath (a j) (q j) (hq j (by omega)).ne' v)
    (fun j hj => (continuous_fordVelocity (q j) (hq j (by omega)).ne').continuousOn)
  let f (j : ℕ) := ∫ v in l j..r j, fordPathIntegrand n (a j) (q j) v
  change (twoColourPartitionCount n : ℂ) = ∑ j ∈ Finset.range m, f j at ht
  have hsum : ∑ j ∈ Finset.range m, f j =
      (∑ j ∈ Finset.range (m - 1), f (j + 1)) + f 0 := by
    have h' := Finset.sum_range_succ' f (m - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h'
  rw [ht, hsum, add_comm]
  congr 1
  simp [f, l, r, ha₀, hq₀]

end DurfeeCCS.Step14
