module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Dedekind sums and the parameter-two circle-method phase in equation (14). -/

@[expose] public section
namespace DurfeeCCS.Step06

/-- The fractional part of an integer divided by the denominator. -/
noncomputable def dedekindFraction (a : ℤ) (ℓ : ℕ) : ℝ :=
  (a : ℝ) / ℓ - (⌊(a : ℝ) / ℓ⌋ : ℝ)

/-- The symmetric Dedekind sum in the manuscript. For reduced fractions the summation
runs over the nonzero residues modulo the denominator. -/
noncomputable def dedekindSum (h : ℤ) (ℓ : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 ℓ, ((j : ℝ) / ℓ - 1 / 2) * (dedekindFraction (h * j) ℓ - 1 / 2)

/-- The convention of Iskander–Jain–Talvola (1907.03026v3, (1.3)). -/
noncomputable def dedekindSumIJT (h ℓ : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 ℓ, ((j : ℝ) / ℓ) * (dedekindFraction (↑(h * j : ℕ)) ℓ - 1 / 2)

@[simp] theorem dedekindSum_one (h : ℤ) : dedekindSum h 1 = 0 := by
  simp [dedekindSum]

theorem dedekindFraction_eq_mod_div (a : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    dedekindFraction a ℓ = ((a % ℓ : ℕ) : ℝ) / ℓ := by
  have hcast : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hdec : (a : ℝ) / ℓ = (a / ℓ : ℕ) + ((a % ℓ : ℕ) : ℝ) / ℓ := by
    field_simp [hcast.ne']
    exact_mod_cast (Nat.mod_add_div a ℓ).symm.trans (Nat.add_comm _ _)
  have hlo : (0 : ℝ) ≤ ((a % ℓ : ℕ) : ℝ) / ℓ := by positivity
  have hhi : ((a % ℓ : ℕ) : ℝ) / ℓ < 1 := by
    rw [div_lt_one hcast]
    exact_mod_cast Nat.mod_lt a hℓ
  have hf : ⌊(a : ℝ) / ℓ⌋ = ((a / ℓ : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff, hdec, Int.cast_natCast]
    exact ⟨le_add_of_nonneg_right hlo, add_lt_add_right hhi _⟩
  rw [dedekindFraction, Int.cast_natCast, hf, hdec, Int.cast_natCast]
  ring

private theorem sum_dedekindFraction_sub_half_eq_zero {h ℓ : ℕ} (hℓ : 0 < ℓ)
    (hred : h.Coprime ℓ) :
    (∑ j ∈ Finset.Ico 1 ℓ, (dedekindFraction (↑(h * j : ℕ)) ℓ - 1 / 2)) = 0 := by
  let f : Fin ℓ → Fin ℓ := fun j => ⟨(h * j.val) % ℓ, Nat.mod_lt _ hℓ⟩
  have hs : Function.Surjective f := by
    intro j
    obtain ⟨i, hi, heq⟩ := Nat.exists_mul_mod_eq_of_coprime j.val hred hℓ.ne'
    exact ⟨⟨i, hi⟩, Fin.ext (heq.trans (Nat.mod_eq_of_lt j.isLt))⟩
  let e := Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  have hperm : (∑ j ∈ Finset.range ℓ, ((h * j) % ℓ : ℕ)) = ∑ j ∈ Finset.range ℓ, j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (h * j) % ℓ) ℓ,
      ← Fin.sum_univ_eq_sum_range (fun j => j) ℓ]
    exact e.sum_comp (fun j : Fin ℓ => j.val)
  have hsum : (∑ j ∈ Finset.range ℓ, (j : ℝ)) * 2 = (ℓ : ℝ) * ((ℓ : ℝ) - 1) := by
    have hh := congrArg (fun x : ℕ => (x : ℝ)) (Finset.sum_range_id_mul_two ℓ)
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one,
      Nat.cast_ofNat] using hh
  have hrange : (∑ j ∈ Finset.range ℓ, (dedekindFraction (↑(h * j : ℕ)) ℓ - 1 / 2)) = -(1 / 2) := by
    simp_rw [dedekindFraction_eq_mod_div _ hℓ, div_eq_mul_inv]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Nat.cast_sum, hperm, Nat.cast_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hℓ' : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
    field_simp [hℓ']
    linarith [hsum]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hℓ] at hrange
  have hzero : dedekindFraction (↑(h * 0 : ℕ)) ℓ - 1 / 2 = -(1 / 2) := by simp [dedekindFraction]
  rw [hzero] at hrange
  exact add_left_cancel (hrange.trans (add_zero _).symm)

/-- Centering the first factor does not change the IJT sum on reduced fractions. -/
theorem dedekindSum_eq_IJT {h ℓ : ℕ} (hℓ : 0 < ℓ) (hred : h.Coprime ℓ) :
    dedekindSum h ℓ = dedekindSumIJT h ℓ := by
  simp_rw [dedekindSum, dedekindSumIJT, ← Int.natCast_mul, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_dedekindFraction_sub_half_eq_zero hℓ hred, mul_zero, sub_zero]

/-- The complex phase of the summand attached to the reduced fraction `h/ℓ`. -/
noncomputable def twoColourPhase (n h ℓ : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * (dedekindSum h ℓ - (n : ℝ) * h / ℓ) : ℝ) : ℂ) * Complex.I)

/-- The weight `A_ℓ⁽²⁾(n)` of equation (14). -/
noncomputable def twoColourKloosterman (n ℓ : ℕ) : ℂ :=
  ∑ h ∈ (Finset.range ℓ).filter (fun h => Nat.Coprime h ℓ), twoColourPhase n h ℓ

@[simp] theorem norm_twoColourPhase (n h ℓ : ℕ) : ‖twoColourPhase n h ℓ‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

@[simp] theorem twoColourKloosterman_one (n : ℕ) : twoColourKloosterman n 1 = 1 := by
  simp [twoColourKloosterman, twoColourPhase]

theorem norm_twoColourKloosterman_le (n ℓ : ℕ) : ‖twoColourKloosterman n ℓ‖ ≤ (ℓ : ℝ) := by
  calc
    _ ≤ ∑ h ∈ (Finset.range ℓ).filter (fun h => Nat.Coprime h ℓ), ‖twoColourPhase n h ℓ‖ :=
      norm_sum_le _ _
    _ = (((Finset.range ℓ).filter (fun h => Nat.Coprime h ℓ)).card : ℝ) := by simp
    _ ≤ _ := by
      exact_mod_cast (Finset.card_filter_le (Finset.range ℓ) (fun h => Nat.Coprime h ℓ)).trans_eq
        (Finset.card_range ℓ)

/-- The manuscript phase is the α=2, m=0 phase of 1907.03026v3 (1.7). -/
theorem twoColourPhase_eq_exp_IJT {n h ℓ : ℕ} (hℓ : 0 < ℓ) (hred : h.Coprime ℓ) :
    twoColourPhase n h ℓ =
      Complex.exp (2 * Real.pi * Complex.I * (dedekindSumIJT h ℓ : ℂ) -
        2 * Real.pi * Complex.I * n * h / ℓ) := by
  unfold twoColourPhase
  rw [dedekindSum_eq_IJT hℓ hred]
  congr 1
  push_cast
  ring

/-- Identify the complete finite weight with the α=2, m=0 weight of (1.7). -/
theorem twoColourKloosterman_eq_IJT (n : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    twoColourKloosterman n ℓ =
      ∑ h ∈ (Finset.range ℓ).filter (fun h => Nat.Coprime h ℓ),
        Complex.exp (2 * Real.pi * Complex.I * (dedekindSumIJT h ℓ : ℂ) -
          2 * Real.pi * Complex.I * n * h / ℓ) := by
  unfold twoColourKloosterman
  refine Finset.sum_congr rfl (fun h hh => ?_)
  exact twoColourPhase_eq_exp_IJT hℓ (Finset.mem_filter.mp hh).2

end DurfeeCCS.Step06
