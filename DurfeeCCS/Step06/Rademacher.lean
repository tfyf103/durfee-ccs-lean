module

public import DurfeeCCS.Step06.BesselSeries
public import DurfeeCCS.Step06.Dedekind
public import DurfeeCCS.Step06.TwoColour
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Equation (14): the summand and its unconditional absolute convergence. -/

@[expose] public section
namespace DurfeeCCS.Step06

/-- The defining series gives a quadratic bound near zero, with an explicit entire majorant. -/
theorem norm_besselI_two_le (z : ℂ) :
    ‖besselI 2 z‖ ≤ (‖z‖ / 2) ^ 2 * Real.exp ((‖z‖ / 2) ^ 2) := by
  let α : ℝ := (‖z‖ / 2) ^ 2
  have hExp : HasSum (fun k : ℕ => α ^ k / (k.factorial : ℝ)) (Real.exp α) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp α
  change ‖∑' k : ℕ, besselITerm 2 k z‖ ≤ α * Real.exp α
  refine (summable_besselITerm 2 z).hasSum.norm_le_of_bounded (hExp.mul_left α) (fun k => ?_)
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hfac' : (1 : ℝ) ≤ (k + 2).factorial := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 2))
  have hnorm : ‖z / 2‖ = ‖z‖ / 2 := by simp
  rw [besselITerm, norm_div, norm_pow, norm_mul, hnorm, Complex.norm_natCast,
    Complex.norm_natCast, pow_add]
  rw [pow_mul]
  change α ^ k * α / ((k.factorial : ℝ) * ((k + 2).factorial : ℝ)) ≤ α * (α ^ k / k.factorial)
  rw [mul_div_assoc', mul_comm (α ^ k) α]
  exact div_le_div_of_nonneg_left (by positivity) hfac
    (le_mul_of_one_le_right hfac.le hfac')

/-- The constant in the normalized Bessel argument `π √(12n−1)/(3ℓ)`. -/
noncomputable def twoColourBesselScale (n : ℕ) : ℝ :=
  Real.pi * Real.sqrt (12 * (n : ℝ) - 1) / 3

/-- The unscaled summand in (14), indexed by the positive denominator `ℓ`. -/
noncomputable def twoColourRademacherTerm (n ℓ : ℕ) : ℂ :=
  twoColourKloosterman n ℓ / (ℓ : ℂ) * besselI 2 ((twoColourBesselScale n / ℓ : ℝ) : ℂ)

/-- An explicit comparison constant for the series over denominators. -/
noncomputable def twoColourMajorant (n : ℕ) : ℝ :=
  (|twoColourBesselScale n| / 2) ^ 2 * Real.exp ((|twoColourBesselScale n| / 2) ^ 2)

/-- An explicit version of the `Oₙ(ℓ⁻²)` estimate in (14). -/
theorem norm_twoColourRademacherTerm_le {n ℓ : ℕ} (hℓ : 0 < ℓ) :
    ‖twoColourRademacherTerm n ℓ‖ ≤ twoColourMajorant n / (ℓ : ℝ) ^ 2 := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hℓone : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  let z : ℂ := ((twoColourBesselScale n / ℓ : ℝ) : ℂ)
  let s : ℝ := |twoColourBesselScale n| / 2
  have hz : ‖z‖ / 2 = s / ℓ := by
    simp only [z, s, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg hℓpos.le]
    ring
  have hsmall : (‖z‖ / 2) ^ 2 ≤ s ^ 2 := by
    rw [hz]
    exact pow_le_pow_left₀ (by positivity) (div_le_self (by positivity) hℓone) 2
  change ‖twoColourKloosterman n ℓ / (ℓ : ℂ) * besselI 2 z‖ ≤
    (s ^ 2 * Real.exp (s ^ 2)) / (ℓ : ℝ) ^ 2
  calc
    _ = (‖twoColourKloosterman n ℓ‖ / (ℓ : ℝ)) * ‖besselI 2 z‖ := by
      rw [norm_mul, norm_div, Complex.norm_natCast]
    _ ≤ 1 * ‖besselI 2 z‖ := by
      exact mul_le_mul_of_nonneg_right ((div_le_one hℓpos).2 (norm_twoColourKloosterman_le n ℓ))
        (norm_nonneg _)
    _ ≤ (‖z‖ / 2) ^ 2 * Real.exp ((‖z‖ / 2) ^ 2) := by
      simpa only [one_mul] using norm_besselI_two_le z
    _ ≤ (‖z‖ / 2) ^ 2 * Real.exp (s ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsmall) (sq_nonneg _)
    _ = _ := by rw [hz, div_pow]; ring

/-- The series of norms in (14) is summable over all the positive denominators. -/
theorem summable_norm_twoColourRademacherTerm (n : ℕ) :
    Summable (fun k : ℕ => ‖twoColourRademacherTerm n (k + 1)‖) := by
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hc := (hs.comp_injective Nat.succ_injective).mul_left (twoColourMajorant n)
  refine hc.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
  simpa only [Function.comp_apply, Nat.succ_eq_add_one, mul_one_div] using
    norm_twoColourRademacherTerm_le (n := n) (ℓ := k + 1) (Nat.succ_pos k)

/-- In particular, the complex series in (14) has a sum. -/
theorem summable_twoColourRademacherTerm (n : ℕ) :
    Summable (fun k : ℕ => twoColourRademacherTerm n (k + 1)) :=
  (summable_norm_twoColourRademacherTerm n).of_norm

/-- The complete analytic right hand side of (14). -/
noncomputable def twoColourRademacherRHS (n : ℕ) : ℂ :=
  ((2 * Real.pi / (12 * (n : ℝ) - 1) : ℝ) : ℂ) *
    ∑' k : ℕ, twoColourRademacherTerm n (k + 1)

/-- The coefficient identity asserted by (14) for positive coefficients. -/
def TwoColourRademacherIdentity : Prop :=
  ∀ n : ℕ, 0 < n → (twoColourPartitionCount n : ℂ) = twoColourRademacherRHS n

/-- The normalized right hand side agrees with the α=2, m=0 right hand side of
1907.03026v3 (1.8). At α=2 the range of the polar index consists of `m = 0` alone,
whose coefficient is `twoColourPartitionCount_zero`. -/
theorem twoColourRademacherRHS_eq_IJT {n : ℕ} (hn : 0 < n) :
    twoColourRademacherRHS n =
      (((Real.sqrt (1 / 12)) ^ 2 / (Real.sqrt ((n : ℝ) - 1 / 12)) ^ 2 * (2 * Real.pi) : ℝ) : ℂ) *
        ∑' k : ℕ,
          (∑ h ∈ (Finset.range (k + 1)).filter (fun h => Nat.Coprime h (k + 1)),
            Complex.exp (2 * Real.pi * Complex.I * (dedekindSumIJT h (k + 1) : ℂ) -
              2 * Real.pi * Complex.I * n * h / ((k + 1 : ℕ) : ℂ))) / ((k + 1 : ℕ) : ℂ) *
          besselI 2 ((((4 * Real.pi / ((k + 1 : ℕ) : ℝ)) * Real.sqrt ((n : ℝ) - 1 / 12) *
            Real.sqrt (1 / 12)) : ℝ) : ℂ) := by
  unfold twoColourRademacherRHS
  rw [ijtTwoColour_prefactor hn]
  congr 1
  apply tsum_congr
  intro k
  unfold twoColourRademacherTerm
  rw [twoColourKloosterman_eq_IJT n (Nat.succ_pos k), ijtTwoColour_argument hn (k + 1)]
  have hscale : twoColourBesselScale n / ((k + 1 : ℕ) : ℝ) =
      Real.pi * Real.sqrt (12 * (n : ℝ) - 1) / (3 * ((k + 1 : ℕ) : ℝ)) := by
    rw [twoColourBesselScale, div_div]
  rw [hscale]

end DurfeeCCS.Step06
