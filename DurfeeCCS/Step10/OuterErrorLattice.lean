module

public import DurfeeCCS.Step07.OuterTableMonotone
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-! Counting and summing the odd frequencies on pages 41–43. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real

/-- The frequencies in the Poisson formula, indexed without repetition. -/
def outerFrequency (p : ℤ) : ℝ := (2 * (p : ℝ) + 1) * π

/-- The positive magnitude of the odd frequency pair with index m. -/
def outerPositiveFrequency (m : ℕ) : ℝ := outerFrequency m

theorem outerFrequency_nat (m : ℕ) :
    outerFrequency (m : ℤ) = (2 * (m : ℝ) + 1) * π := by
  simp [outerFrequency]

theorem outerFrequency_neg_nat (m : ℕ) :
    outerFrequency (-(m + 1 : ℤ)) = -outerPositiveFrequency m := by
  simp [outerFrequency, outerPositiveFrequency]
  ring

@[simp] theorem outerPositiveFrequency_zero : outerPositiveFrequency 0 = π := by
  simp [outerPositiveFrequency, outerFrequency]

theorem outerPositiveFrequency_pos (m : ℕ) : 0 < outerPositiveFrequency m := by
  rw [outerPositiveFrequency, outerFrequency_nat]
  positivity

theorem outerPositiveFrequency_succ (m : ℕ) :
    outerPositiveFrequency (m + 1) = outerPositiveFrequency m + 2 * π := by
  simp [outerPositiveFrequency, outerFrequency]
  ring

theorem outerPositiveFrequency_mono : StrictMono outerPositiveFrequency := by
  intro a b hab
  simp only [outerPositiveFrequency, outerFrequency_nat]
  have h : (a : ℝ) < b := by exact_mod_cast hab
  exact mul_lt_mul_of_pos_right (by linarith) pi_pos

theorem exists_outerPositiveFrequency_gt (h : ℝ) : ∃ m, h < outerPositiveFrequency m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (h / π)
  have hm' := (div_lt_iff₀ pi_pos).mp hm
  have hm₀ : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨m, hm'.trans_le ?_⟩
  rw [outerPositiveFrequency, outerFrequency_nat]
  gcongr
  linarith

/-- First positive odd frequency whose magnitude exceeds the cutoff h. -/
def outerFrequencyCutoff (h : ℝ) : ℕ := Nat.find (exists_outerPositiveFrequency_gt h)

theorem outerFrequencyCutoff_spec (h : ℝ) (m : ℕ) :
    h < outerPositiveFrequency m ↔ outerFrequencyCutoff h ≤ m := by
  constructor
  · exact Nat.find_min' (exists_outerPositiveFrequency_gt h)
  · intro hm
    exact (Nat.find_spec (exists_outerPositiveFrequency_gt h)).trans_le
      (outerPositiveFrequency_mono.monotone hm)

theorem outerPositiveFrequency_le_iff (h : ℝ) (m : ℕ) :
    outerPositiveFrequency m ≤ h ↔ m < outerFrequencyCutoff h := by
  rw [← not_lt, outerFrequencyCutoff_spec, not_le]

/-- There are at most h/π + 1 odd frequencies of magnitude at most h. -/
theorem outerFrequencyCutoff_count {h : ℝ} (hh : 0 ≤ h) :
    2 * (outerFrequencyCutoff h : ℝ) ≤ h / π + 1 := by
  generalize hm : outerFrequencyCutoff h = m
  cases m with
  | zero =>
    simp only [Nat.cast_zero, mul_zero]
    exact add_nonneg (div_nonneg hh pi_pos.le) zero_le_one
  | succ m =>
    have hprev := (outerPositiveFrequency_le_iff h m).2 (by omega)
    rw [outerPositiveFrequency, outerFrequency_nat] at hprev
    have hd := (le_div_iff₀ pi_pos).2 hprev
    rw [Nat.cast_succ]
    linarith

private theorem outerHigh_positiveReciprocalSum (h w : ℝ)
    (hh : 0 < h) (hw : h < w) :
    let R (m : ℕ) : ℝ := 1 / (h ^ 2 + (w + (m : ℝ) * (2 * π)) ^ 2)
    Summable R ∧ (∑' m, R m) ≤ 1 / h ^ 2 + 1 / (2 * π * h) := by
  dsimp only
  let R (m : ℕ) : ℝ := 1 / (h ^ 2 + (w + (m : ℝ) * (2 * π)) ^ 2)
  let g (m : ℕ) : ℝ := 1 / (2 * π * (w + (m : ℝ) * (2 * π)))
  have hw₀ : 0 < w := hh.trans hw
  have g₀ (m : ℕ) : 0 ≤ g m := by dsimp [g]; positivity
  have R₀ (m : ℕ) : 0 ≤ R m := by dsimp [R]; positivity
  have Rfirst : R 0 ≤ 1 / h ^ 2 := by
    dsimp [R]
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    nlinarith
  have Rnext (m : ℕ) : R (m + 1) ≤ g m - g (m + 1) := by
    let x := w + (m : ℝ) * (2 * π)
    let d := 2 * π
    have hx : 0 < x := by dsimp [x]; positivity
    have hd : 0 < d := by dsimp [d]; positivity
    have hshift : w + ((m + 1 : ℕ) : ℝ) * (2 * π) = x + d := by
      push_cast
      dsimp [x, d]
      ring
    have hstep : R (m + 1) ≤ 1 / (x * (x + d)) := by
      dsimp [R]
      rw [hshift]
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      nlinarith
    apply hstep.trans_eq
    dsimp [g]
    rw [hshift]
    change 1 / (x * (x + d)) = 1 / (d * x) - 1 / (d * (x + d))
    field_simp
    ring
  have hgfirst : g 0 ≤ 1 / (2 * π * h) := by
    simp only [g, Nat.cast_zero, zero_mul, add_zero]
    gcongr
  have hsum (n : ℕ) : (∑ m ∈ Finset.range n, R m) ≤
      1 / h ^ 2 + 1 / (2 * π * h) := by
    cases n with
    | zero => exact add_nonneg (by positivity) (by positivity)
    | succ n =>
      rw [Finset.sum_range_succ']
      have hbound := Finset.sum_le_sum (fun (m : ℕ) (_ : m ∈ Finset.range n) => Rnext m)
      rw [Finset.sum_range_sub'] at hbound
      linarith [g₀ n]
  exact ⟨summable_of_sum_range_le R₀ hsum, Real.tsum_le_of_sum_range_le R₀ hsum⟩

/-- The positive half of the reciprocal-square tail over the odd lattice. -/
theorem outerHighReciprocal_positive {h : ℝ} (hh : 0 < h) :
    let R (m : ℕ) := if h < outerPositiveFrequency m then
        1 / (h ^ 2 + outerPositiveFrequency m ^ 2) else 0
    Summable R ∧ (∑' m, R m) ≤ 1 / h ^ 2 + 1 / (2 * π * h) := by
  dsimp only
  let R (m : ℕ) := if h < outerPositiveFrequency m then
        1 / (h ^ 2 + outerPositiveFrequency m ^ 2) else 0
  let j := outerFrequencyCutoff h
  have hfirst : h < outerPositiveFrequency j := (outerFrequencyCutoff_spec h j).2 le_rfl
  have hns (m : ℕ) :
      R (m + j) = 1 / (h ^ 2 + (outerPositiveFrequency j + (m : ℝ) * (2 * π)) ^ 2) := by
    dsimp only [R]
    rw [ite_eq_left ((outerFrequencyCutoff_spec h _).2 (by omega : j ≤ m+j))]
    simp [outerPositiveFrequency, outerFrequency]
    congr 2
    ring
  obtain ⟨hs, hsum⟩ := outerHigh_positiveReciprocalSum h _ hh hfirst
  have htail : Summable (fun m => R (m + j)) := hs.congr (fun m => (hns m).symm)
  have hfinite : (∑ m ∈ Finset.range j, R m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hbelow : m < j := Finset.mem_range.mp hm
    exact ite_eq_right (not_lt.mpr ((outerPositiveFrequency_le_iff h m).2 hbelow))
  refine ⟨htail.comp_nat_add, ?_⟩
  rw [← htail.sum_add_tsum_nat_add', hfinite, zero_add]
  exact (tsum_congr hns).le.trans hsum

/-- The reciprocal-square tail over both signs of the odd lattice, as used on page 42. -/
theorem outerHighReciprocal_sum {h : ℝ} (hh : 0 < h) :
    let R (p : ℤ) := if h < |outerFrequency p| then 1 / (h ^ 2 + outerFrequency p ^ 2) else 0
    Summable R ∧ (∑' p, R p) ≤ 2 / h ^ 2 + 1 / (π * h) := by
  dsimp only
  let R (p : ℤ) := if h < |outerFrequency p| then 1 / (h ^ 2 + outerFrequency p ^ 2) else 0
  let Q (m : ℕ) := if h < outerPositiveFrequency m then
      1 / (h ^ 2 + outerPositiveFrequency m ^ 2) else 0
  obtain ⟨hQ, hQsum⟩ := outerHighReciprocal_positive hh
  have hp (m : ℕ) : R m = Q m := by
    dsimp only [R, Q]
    rw [show outerFrequency ↑m = outerPositiveFrequency m from rfl, abs_of_pos (outerPositiveFrequency_pos m)]
  have hn (m : ℕ) : R (-(m + 1 : ℤ)) = Q m := by
    dsimp only [R, Q]
    rw [outerFrequency_neg_nat, abs_neg, abs_of_pos (outerPositiveFrequency_pos m), neg_sq]
  have hR : Summable R := ((hQ.congr (fun m => (hp m).symm)).hasSum.of_nat_of_neg_add_one
    (hQ.congr (fun m => (hn m).symm)).hasSum).summable
  refine ⟨hR, ?_⟩
  rw [← tsum_nat_add_neg_add_one hR]
  simp_rw [hp, hn]
  rw [hQ.tsum_add hQ]
  convert add_le_add hQsum hQsum using 1
  field_simp
  ring

/-- Every function supported on low frequencies is finitely summable, together with the paired sum. -/
theorem outerLow_frequency_sum {G : Type*} [NormedAddCommGroup G] (h : ℝ) (f : ℤ → G) :
    let F (p : ℤ) := if |outerFrequency p| ≤ h then f p else 0
    Summable F ∧
      (∑' p, F p) = ∑ m ∈ Finset.range (outerFrequencyCutoff h), (f m + f (-(m + 1 : ℤ))) := by
  dsimp only
  let F (p : ℤ) := if |outerFrequency p| ≤ h then f p else 0
  let j := outerFrequencyCutoff h
  have hAbs₁ (m : ℕ) : |outerFrequency (m : ℤ)| = outerPositiveFrequency m :=
    abs_of_pos (outerPositiveFrequency_pos m)
  have hAbs₂ (m : ℕ) : |outerFrequency (-(m + 1 : ℤ))| = outerPositiveFrequency m := by
    rw [outerFrequency_neg_nat, abs_neg, abs_of_pos (outerPositiveFrequency_pos m)]
  have hM₁ (m : ℕ) : F m = if m < j then f m else 0 := by
    simp only [F, hAbs₁, outerPositiveFrequency_le_iff, j]
  have hM₂ (m : ℕ) : F (-(m + 1 : ℤ)) = if m < j then f (-(m + 1 : ℤ)) else 0 := by
    simp only [F, hAbs₂, outerPositiveFrequency_le_iff, j]
  have h₁ : Summable (fun m : ℕ => F m) := by
    apply summable_of_ne_finset_zero (s := Finset.range j)
    intro m hm
    rw [hM₁, ite_eq_right (fun h => hm (Finset.mem_range.mpr h))]
  have h₂ : Summable (fun m : ℕ => F (-(m + 1 : ℤ))) := by
    apply summable_of_ne_finset_zero (s := Finset.range j)
    intro m hm
    rw [hM₂, ite_eq_right (fun h => hm (Finset.mem_range.mpr h))]
  have hF : Summable F := (h₁.hasSum.of_nat_of_neg_add_one h₂.hasSum).summable
  refine ⟨hF, ?_⟩
  rw [← tsum_nat_add_neg_add_one hF]
  trans ∑ m ∈ Finset.range j, (F m + F (-(m + 1 : ℤ)))
  · apply tsum_eq_sum
    intro m hm
    rw [hM₁, hM₂]
    simp [show ¬m < j from fun h => hm (Finset.mem_range.mpr h)]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [hM₁, hM₂, ite_eq_left (Finset.mem_range.mp hm), ite_eq_left (Finset.mem_range.mp hm)]

end DurfeeCCS.Step10
