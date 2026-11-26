module

public import DurfeeCCS.Step06.EulerConstantTerm
public import DurfeeCCS.Step06.RademacherGenerating
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open DurfeeCCS.Step06 Finset

/-- The exponent contributed by choosing a terms in the Euler tail after index d. -/
def outerTailPower (d a : ℕ) : ℕ := d * a + (a + 1).choose 2

def outerTailTerm (q : ℂ) (d a : ℕ) : ℂ :=
  (-1 : ℂ) ^ a * q ^ outerTailPower d a / qPochhammer q q a

private theorem outerTailTerm_eq (q : ℂ) (d a : ℕ) :
    outerTailTerm q d a = eulerQTerm q (-(q ^ (d + 1))) a := by
  unfold outerTailTerm eulerQTerm outerTailPower
  rw [neg_pow (q ^ (d + 1)), ← pow_mul, mul_assoc, ← pow_add]
  have he : d * a + (a + 1).choose 2 = (d + 1) * a + a.choose 2 := by
    rw [show (a + 1).choose 2 = a.choose 1 + a.choose 2 from Nat.choose_succ_succ a 1,
      Nat.choose_one_right, Nat.add_mul, one_mul]
    omega
  rw [he]

theorem summable_norm_outerTailTerm {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) :
    Summable fun a : ℕ => ‖outerTailTerm q d a‖ := by
  simpa only [outerTailTerm_eq] using summable_norm_eulerQTerm hq (-(q ^ (d + 1)))

/-- Euler expansion of the tail strictly beyond the Durfee index. -/
theorem eulerTail_eq_tsum {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) :
    (∏' j : ℕ, (1 - q ^ (j + d + 1))) = ∑' a : ℕ, outerTailTerm q d a := by
  simp_rw [outerTailTerm_eq, eulerQSeries_eq_tprod hq]
  refine tprod_congr (fun j => ?_)
  rw [neg_mul, ← pow_add, ← sub_eq_add_neg]
  congr 2
  omega

/-- The product of the two Euler expansions is an absolutely convergent double series. -/
theorem eulerTail_sq_eq_doubleSum {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) :
    (∏' j : ℕ, (1 - q ^ (j + d + 1))) ^ 2 =
      ∑' ab : ℕ × ℕ, outerTailTerm q d ab.1 * outerTailTerm q d ab.2 := by
  rw [eulerTail_eq_tsum hq, pow_two]
  exact tsum_mul_tsum_of_summable_norm (summable_norm_outerTailTerm hq d)
    (summable_norm_outerTailTerm hq d)

private theorem summable_eulerTailPerturbation {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) :
    Summable (fun j : ℕ => ‖-(q ^ (j + d + 1))‖) := by
  simp_rw [norm_neg, norm_pow, pow_succ]
  have hs : Summable (fun j : ℕ => ‖q‖ ^ (j + d)) :=
    (summable_nat_add_iff d).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)
  exact hs.mul_right ‖q‖

private theorem eulerTail_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) :
    (∏' j : ℕ, (1 - q ^ (j + d + 1))) ≠ 0 := by
  have hsum := summable_eulerTailPerturbation hq d
  have hne (j : ℕ) : 1 + -(q ^ (j + d + 1)) ≠ 0 := by
    intro hz
    have he : q ^ (j + d + 1) = 1 := by rw [← sub_eq_add_neg, sub_eq_zero, eq_comm] at hz; exact hz
    have hnorm : ‖q ^ (j + d + 1)‖ < 1 := by
      rw [norm_pow, pow_succ]
      exact (mul_le_of_le_one_left (norm_nonneg q)
        (pow_le_one₀ (norm_nonneg q) hq.le)).trans_lt hq
    simp [he] at hnorm
  simpa only [← sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable hne hsum

/-- The tail of the Euler product starting with size d+1. -/
def outerEulerTail (q : ℂ) (d : ℕ) : ℂ :=
  ∏' j : ℕ, (1 - q ^ (j + d + 1))

/-- The two-colour generating series times the squared tail is the restricted generating
function at index d. -/
theorem twoColourGenerating_mul_eulerTail_sq {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) :
    twoColourGenerating q * (outerEulerTail q d) ^ 2 = (qPochhammer q q d)⁻¹ ^ 2 := by
  let T := outerEulerTail q d
  let P := qPochhammer q q d
  have heq : P * T = ∏' j : ℕ, (1 - q ^ (j + 1)) := by
    change qPochhammer q q d * _ = _
    rw [qPochhammer_self_eq_prod]
    have hTail : Multipliable (fun j : ℕ => 1 - q ^ (j + d + 1)) := by
      simpa only [← sub_eq_add_neg] using
        multipliable_one_add_of_summable (summable_eulerTailPerturbation hq d)
    have hProd := HasProd.prod_range_mul (f := fun j : ℕ => 1 - q ^ (j + 1)) (k := d)
      hTail.hasProd
    exact hProd.tprod_eq.symm
  have hT : T ≠ 0 := by
    unfold T outerEulerTail
    exact eulerTail_ne_zero (q := q) hq d
  change twoColourGenerating q * T ^ 2 = P⁻¹ ^ 2
  rw [twoColourGenerating, ← heq, ← mul_pow]
  have H : (P * T)⁻¹ * T = P⁻¹ := by
    rw [mul_inv_rev, mul_comm T⁻¹, mul_assoc, inv_mul_cancel₀ hT, mul_one]
  rw [H]

/-- The nonnegative shift γ used for the Bessel kernels attached to the triple (a,b,j). -/
def outerGamma (a b j : ℕ) : ℝ :=
  (j : ℝ) + ((a : ℝ) - b) ^ 2 / 4 + ((a : ℝ) + b) / 2

theorem outerGamma_lower (a b j : ℕ) : (j : ℝ) + ((a : ℝ) + b) / 2 ≤ outerGamma a b j := by
  unfold outerGamma
  linarith [sq_nonneg ((a : ℝ) - b)]

private theorem choose_succ_two_cast (a : ℕ) :
    ((a + 1).choose 2 : ℝ) = (a : ℝ) * ((a : ℝ) + 1) / 2 := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [show (a + 1 + 1).choose 2 = (a + 1).choose 1 + (a + 1).choose 2 from
      Nat.choose_succ_succ (a + 1) 1, Nat.choose_one_right]
    push_cast
    rw [ih]
    ring

/-- Completing the square leaves exactly the shift γ, and the combined exponent is integral. -/
theorem outerGamma_complete_square (d a b j : ℕ) :
    ((d ^ 2 + outerTailPower d a + outerTailPower d b + j : ℕ) : ℝ) =
      ((d : ℝ) + ((a : ℝ) + b) / 2) ^ 2 + outerGamma a b j := by
  simp only [outerTailPower, outerGamma, Nat.cast_add, Nat.cast_pow, Nat.cast_mul, choose_succ_two_cast]
  ring

/-- Every nonzero triple has positive shifted size. -/
theorem outerGamma_lt_shiftedSize {n d a b j : ℕ} (hd : 0 < d)
    (hs : d ^ 2 + outerTailPower d a + outerTailPower d b + j ≤ n) :
    outerGamma a b j < (n : ℝ) - 1 / 12 := by
  have hs' : ((d ^ 2 + outerTailPower d a + outerTailPower d b + j : ℕ) : ℝ) ≤ n :=
    by exact_mod_cast hs
  rw [outerGamma_complete_square] at hs'
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : (1 : ℝ) ≤ (d : ℝ) + ((a : ℝ) + b) / 2 := by
    linarith only [hd', Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  have ht₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht 2
  linarith only [hs', ht₂]

end DurfeeCCS.Step10
