module

public import DurfeeCCS.Step10.OuterBesselBounds
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! The integer indices added in the shifted Poisson step, and their exact support count. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset

/-- The nonpositive integer indices in the closed support of the shifted kernel. -/
def outerNegativeIndices (y : ℝ) (k : ℕ) : Finset ℤ :=
  (Finset.Icc ⌈-y - (k : ℝ) / 2⌉ ⌊y - (k : ℝ) / 2⌋).filter (fun d => d ≤ 0)

private def outerPositiveIndices (m : ℕ) : Finset ℤ :=
  Finset.Icc 1 (m : ℤ)

/-- The shifted summand in the integer Poisson sum, before the partition weights. -/
def outerKernelSummand (y h : ℝ) (k : ℕ) (d : ℤ) : ℝ :=
  (-exp h) ^ d * outerBesselKernel y ((d : ℝ) + (k : ℝ) / 2)

theorem outerNegativeIndices_card {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    ((outerNegativeIndices y k).card : ℝ) ≤ 2 * y + 1 := by
  let a : ℤ := ⌈-y - (k : ℝ) / 2⌉
  let b : ℤ := ⌊y - (k : ℝ) / 2⌋
  have hcard : (outerNegativeIndices y k).card ≤ (Finset.Icc a b).card :=
    Finset.card_filter_le _ _
  have hlo : -y - (k : ℝ) / 2 ≤ (a : ℝ) := Int.le_ceil _
  have hhi : (b : ℝ) ≤ y - (k : ℝ) / 2 := Int.floor_le _
  rw [Int.card_Icc] at hcard
  have hbound : (((b + 1 - a).toNat : ℕ) : ℝ) ≤ 2 * y + 1 := by
    by_cases hh : 0 ≤ b + 1 - a
    · rw [show ((b + 1 - a).toNat : ℝ) = (b : ℝ) + 1 - (a : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg hh]
      linarith
    · have hz : (b + 1 - a).toNat = 0 := by omega
      rw [hz, Nat.cast_zero]
      linarith
  exact (by exact_mod_cast hcard : ((outerNegativeIndices y k).card : ℝ) ≤
    (((b + 1 - a).toNat : ℕ) : ℝ)).trans hbound

private theorem outerKernelSummand_zero_outside {y h : ℝ} {k m : ℕ}
    (hy : 0 ≤ y) (hm : y ≤ (m : ℝ) + 1) {d : ℤ}
    (hd : d ∉ outerPositiveIndices m ∪ outerNegativeIndices y k) :
    outerKernelSummand y h k d = 0 := by
  have hneg : d ∉ outerNegativeIndices y k := fun hx => hd (Finset.mem_union_right _ hx)
  have hpos : d ∉ outerPositiveIndices m := fun hx => hd (Finset.mem_union_left _ hx)
  have hY : y ≤ |(d : ℝ) + (k : ℝ) / 2| := by
    by_contra! hy'
    have hx := abs_lt.mp hy'
    by_cases hd0 : d ≤ 0
    · apply hneg
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by linarith [hx.1]),
        Int.le_floor.mpr (by linarith [hx.2])⟩, hd0⟩
    · apply hpos
      apply Finset.mem_Icc.mpr
      have hmd : (d : ℝ) < (m : ℝ) + 1 := by
        have hk : (0 : ℝ) ≤ k := by positivity
        linarith [hx.2]
      have hmd' : d < (m : ℤ) + 1 := by exact_mod_cast hmd
      omega
  unfold outerKernelSummand
  rw [outerBesselKernel_eq_zero hy hY, mul_zero]

private theorem outerPositiveIndices_sum (y h : ℝ) (k m : ℕ) :
    (∑ d ∈ outerPositiveIndices m, outerKernelSummand y h k d) =
      ∑ d ∈ Finset.Icc 1 m, (-exp h) ^ d * outerBesselKernel y ((d : ℝ) + (k : ℝ) / 2) := by
  let e : ℕ ↪ ℤ := ⟨(↑), Int.ofNat_injective⟩
  have hmap : (Finset.Icc 1 m).map e = outerPositiveIndices m := by
    ext i
    simp only [outerPositiveIndices, Finset.mem_map, Finset.mem_Icc]
    constructor
    · rintro ⟨d, ⟨hd, hd'⟩, hi⟩
      change (d : ℤ) = i at hi
      subst i
      exact ⟨by exact_mod_cast hd, by exact_mod_cast hd'⟩
    · intro ⟨hi, him⟩
      have hN : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg (by omega)
      refine ⟨i.toNat, ⟨?_, ?_⟩, hN⟩
      · exact_mod_cast hN ▸ hi
      · exact_mod_cast hN ▸ him
  rw [← hmap, Finset.sum_map]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [outerKernelSummand, e]

/-- Exact finite-support identity for extending the positive part to all integers. -/
theorem outerKernel_tsum_sub_pos_eq {y h : ℝ} {k m : ℕ}
    (hy : 0 ≤ y) (hm : y ≤ (m : ℝ) + 1) :
    (∑' d : ℤ, (-(exp h : ℂ)) ^ d *
      (outerBesselKernel y ((d : ℝ) + (k : ℝ) / 2) : ℂ)).re -
      (∑ d ∈ Finset.Icc 1 m, (-exp h) ^ d * outerBesselKernel y ((d : ℝ) + (k : ℝ) / 2)) =
      ∑ d ∈ outerNegativeIndices y k, outerKernelSummand y h k d := by
  have hdis : Disjoint (outerPositiveIndices m) (outerNegativeIndices y k) := by
    rw [Finset.disjoint_left]
    intro i hi hn
    have hp := (Finset.mem_Icc.mp hi).1
    have hneg := (Finset.mem_filter.mp hn).2
    omega
  have hcast (d : ℤ) :
      (-(exp h : ℂ)) ^ d * (outerBesselKernel y ((d : ℝ) + (k : ℝ) / 2) : ℂ) =
      (outerKernelSummand y h k d : ℂ) := by simp [outerKernelSummand]
  simp_rw [hcast]
  rw [tsum_eq_sum (s := outerPositiveIndices m ∪ outerNegativeIndices y k)
    (fun d hd => by rw [outerKernelSummand_zero_outside hy hm hd, Complex.ofReal_zero]),
    Complex.re_sum, Finset.sum_union hdis]
  simp only [Complex.ofReal_re]
  rw [outerPositiveIndices_sum]
  ring

theorem outerNegativeIndices_abs_sum_bound {y Y h : ℝ} (hy : 0 < y) (hyY : y ≤ Y)
    (hh : 0 ≤ h) (k : ℕ) :
    (∑ d ∈ outerNegativeIndices y k, |outerKernelSummand y h k d|) ≤
      (2 * Y + 1) * (π ^ 3 / 36) * exp (2 * π * Y / sqrt 3) := by
  have hy0 : 0 < Y := hy.trans_le hyY
  have hb : ∀ d ∈ outerNegativeIndices y k,
      |outerKernelSummand y h k d| ≤ (π ^ 3 / 36) * exp (2 * π * Y / sqrt 3) := by
    intro d hd
    have hd0 : d ≤ 0 := (Finset.mem_filter.mp hd).2
    have hpow := zpow_le_one_of_nonpos₀ (one_le_exp hh) hd0
    have hk := outerBesselKernel_bounds hy ((d : ℝ) + (k : ℝ) / 2)
    rw [outerKernelSummand, abs_mul, abs_zpow, abs_neg, abs_of_pos (exp_pos h),
      abs_of_nonneg hk.1]
    calc
      _ ≤ 1 * outerBesselKernel y ((d : ℝ) + (k : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hpow hk.1
      _ ≤ (π ^ 3 / 36) * exp (2 * π * y / sqrt 3) := by simpa only [one_mul] using hk.2
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ _d ∈ outerNegativeIndices y k, (π ^ 3 / 36) * exp (2 * π * Y / sqrt 3) := Finset.sum_le_sum hb
    _ = ((outerNegativeIndices y k).card : ℝ) * ((π ^ 3 / 36) * exp (2 * π * Y / sqrt 3)) := by simp
    _ ≤ (2 * Y + 1) * ((π ^ 3 / 36) * exp (2 * π * Y / sqrt 3)) :=
      mul_le_mul_of_nonneg_right ((outerNegativeIndices_card hy.le k).trans (by linarith)) (by positivity)
    _ = _ := by ring

end DurfeeCCS.Step10
