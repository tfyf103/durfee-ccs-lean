module

public import DurfeeCCS.Step06.AngleCoefficients
public import DurfeeCCS.Step06.GeneratingAnalytic
public import DurfeeCCS.Step06.Theta
public import DurfeeCCS.Step06.TwoColour
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! The analytic two-colour partition series and its exact coefficient integral. -/

@[expose] public section
namespace DurfeeCCS.Step06

open Filter Finset PowerSeries
open scoped Topology

/-- The reciprocal square of the Euler product on the open unit disc. -/
noncomputable def twoColourGenerating (q : ℂ) : ℂ :=
  (∏' j : ℕ, (1 - q ^ (j + 1)))⁻¹ ^ 2

private theorem coeff_restrictedPair_nonneg (d n : ℕ) :
    0 ≤ coeff n (restrictedPairSeries d) := by
  rw [coeff_restrictedPairSeries]
  positivity

private theorem coeff_restrictedPair_le_twoColour (d n : ℕ) :
    coeff n (restrictedPairSeries d) ≤ twoColourPartitionCount n := by
  rw [coeff_restrictedPairSeries, twoColourPartitionCount_eq_convolution]
  refine Finset.sum_le_sum fun ab _ => ?_
  have hcard (k : ℕ) : ((Nat.Partition.restricted k (· ≤ d)).card : ℤ) ≤
      (Fintype.card (Nat.Partition k) : ℤ) := by
    exact_mod_cast Finset.card_le_univ (Nat.Partition.restricted k (· ≤ d))
  exact mul_le_mul (hcard _) (hcard _) (by positivity) (by positivity)

private theorem twoColourCount_nonneg (n : ℕ) : 0 ≤ twoColourPartitionCount n := by
  rw [twoColourPartitionCount_eq_convolution]
  positivity

private theorem norm_int_mul_pow (q : ℂ) (n : ℕ) {a : ℤ} (ha : 0 ≤ a) :
    ‖(a : ℂ) * q ^ n‖ = (a : ℝ) * ‖q‖ ^ n := by
  have hreal : 0 ≤ (a : ℝ) := by exact_mod_cast ha
  rw [norm_mul, norm_pow, Complex.norm_intCast, abs_of_nonneg hreal]

private theorem tendsto_restrictedPairValue {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun d => (qPochhammer q q d)⁻¹ ^ 2) atTop (𝓝 (twoColourGenerating q)) := by
  have hsum : Summable (fun j : ℕ => ‖q ^ (j + 1)‖) := by
    simpa only [norm_pow] using
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)
  have hne (j : ℕ) : 1 - q ^ (j + 1) ≠ 0 := by
    intro h
    have heq : q ^ (j + 1) = 1 := (sub_eq_zero.mp h).symm
    have hlt : ‖q ^ (j + 1)‖ < 1 := by
      rw [norm_pow, pow_succ]
      exact (mul_le_of_le_one_left (norm_nonneg q)
        (pow_le_one₀ (norm_nonneg q) hq.le)).trans_lt hq
    simp [heq] at hlt
  have hprod_ne : (∏' j : ℕ, (1 - q ^ (j + 1))) ≠ 0 := by
    simpa only [← sub_eq_add_neg] using
      (tprod_one_add_ne_zero_of_summable (f := fun j : ℕ => -(q ^ (j + 1)))
        (by simpa only [← sub_eq_add_neg] using hne) (by simpa only [norm_neg] using hsum))
  have hprod := (ModularForm.multipliable_one_sub_pow hq).hasProd.tendsto_prod_nat
  simpa only [qPochhammer_self_eq_prod, twoColourGenerating] using (hprod.inv₀ hprod_ne).pow 2

/-- The two-colour partition expansion is absolutely convergent on the open q-disc. -/
theorem summable_norm_twoColourGenerating {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖(twoColourPartitionCount n : ℂ) * q ^ n‖) := by
  let r : ℂ := (‖q‖ : ℝ)
  have hr : ‖r‖ < 1 := by simpa [r] using hq
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ (tendsto_restrictedPairValue hr))
  refine summable_of_sum_range_le (c := C) (fun _ => norm_nonneg _) (fun d => ?_)
  have hre (n : ℕ) :
      ‖((coeff n (restrictedPairSeries d) : ℤ) : ℂ) * q ^ n‖ =
        (((coeff n (restrictedPairSeries d) : ℤ) : ℂ) * r ^ n).re := by
    rw [norm_int_mul_pow q n (coeff_restrictedPair_nonneg d n)]
    simp only [r, ← Complex.ofReal_pow, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hsum := Complex.hasSum_re (hasSum_coeff_restrictedPairSeries hr d)
  calc
    _ = ∑ n ∈ range d, (((coeff n (restrictedPairSeries d) : ℤ) : ℂ) * r ^ n).re := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [twoColourPartitionCount_eq_coeff_restricted n d (mem_range.mp hn).le, hre]
    _ ≤ ((qPochhammer r r d)⁻¹ ^ 2).re := by
      rw [← hsum.tsum_eq]
      exact hsum.summable.sum_le_tsum _ (fun n _ => by rw [← hre]; exact norm_nonneg _)
    _ ≤ ‖(qPochhammer r r d)⁻¹ ^ 2‖ := Complex.re_le_norm _
    _ ≤ C := hC _ ⟨d, rfl⟩

/-- The square of the partition generating function is given by its Euler product. -/
theorem twoColourGenerating_eq_tsum {q : ℂ} (hq : ‖q‖ < 1) :
    twoColourGenerating q = ∑' n, (twoColourPartitionCount n : ℂ) * q ^ n := by
  let f : ℕ → ℕ → ℂ := fun d n => ((coeff n (restrictedPairSeries d) : ℤ) : ℂ) * q ^ n
  have hlim (n : ℕ) : Tendsto (f · n) atTop (𝓝 ((twoColourPartitionCount n : ℂ) * q ^ n)) := by
    apply tendsto_atTop_of_eventually_const (i₀ := n)
    intro d hd
    simp only [f, twoColourPartitionCount_eq_coeff_restricted n d hd]
  have hbound (d n : ℕ) : ‖f d n‖ ≤ ‖(twoColourPartitionCount n : ℂ) * q ^ n‖ := by
    dsimp [f]
    rw [norm_int_mul_pow q n (coeff_restrictedPair_nonneg d n),
      norm_int_mul_pow q n (twoColourCount_nonneg n)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast coeff_restrictedPair_le_twoColour d n)
      (pow_nonneg (norm_nonneg _) _)
  have ht := tendsto_tsum_of_dominated_convergence (summable_norm_twoColourGenerating hq)
    hlim (Eventually.of_forall hbound)
  have heq (d : ℕ) : (∑' n, f d n) = (qPochhammer q q d)⁻¹ ^ 2 :=
    (hasSum_coeff_restrictedPairSeries hq d).tsum_eq
  simp_rw [heq] at ht
  exact tendsto_nhds_unique (tendsto_restrictedPairValue hq) ht

/-- The normalized generating series after removing its constant coefficient. -/
theorem hasSum_twoColourGenerating_sub_one {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (twoColourPartitionCount (n + 1) : ℂ) * q ^ (n + 1))
      (twoColourGenerating q - 1) := by
  have hs := (summable_norm_twoColourGenerating hq).of_norm
  rw [twoColourGenerating_eq_tsum hq, hs.tsum_eq_zero_add]
  simp only [twoColourPartitionCount_zero, Int.cast_one, pow_zero, mul_one, add_sub_cancel_left]
  exact (hs.comp_injective Nat.succ_injective).hasSum

/-- A uniform disc bound for the remainder after the constant (polar) coefficient. -/
theorem norm_twoColourGenerating_sub_one_le {q : ℂ} {r : ℝ}
    (hr : 0 < r) (hr' : r < 1) (hq : ‖q‖ ≤ r) :
    ‖twoColourGenerating q - 1‖ ≤ (‖q‖ / r) * ((twoColourGenerating (r : ℂ)).re - 1) := by
  have hs := hasSum_twoColourGenerating_sub_one (hq.trans_lt hr')
  have hrq : ‖(r : ℂ)‖ < 1 := by simpa [abs_of_pos hr] using hr'
  have ht := Complex.hasSum_re (hasSum_twoColourGenerating_sub_one hrq)
  rw [Complex.sub_re, Complex.one_re] at ht
  refine hs.norm_le_of_bounded (ht.mul_left (‖q‖ / r)) (fun n => ?_)
  rw [norm_int_mul_pow q (n + 1) (twoColourCount_nonneg _)]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
    Complex.ofReal_re, pow_succ]
  have hc : (0 : ℝ) ≤ twoColourPartitionCount (n + 1) := by
    exact_mod_cast twoColourCount_nonneg (n + 1)
  have hpow := pow_le_pow_left₀ (norm_nonneg q) hq n
  calc
    _ ≤ (twoColourPartitionCount (n + 1) : ℝ) * (r ^ n * ‖q‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (norm_nonneg q)) hc
    _ = _ := by field_simp

/-- The analytic generating product at `q = exp (-ζ)` in manuscript notation. -/
theorem twoColourGenerating_exp_neg (ζ : ℂ) :
    twoColourGenerating (Complex.exp (-ζ)) = (eulerProduct ζ)⁻¹ ^ 2 := by
  unfold twoColourGenerating eulerProduct
  congr 2
  apply tprod_congr
  intro j
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- Exact extraction of `p₂(n)` on any circle of radius `exp (-u)` with `u > 0`. -/
theorem twoColourPartitionCount_eq_angular_integral (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (twoColourPartitionCount n : ℂ) = (2 * Real.pi : ℂ)⁻¹ *
      ∫ v : ℝ in -Real.pi..Real.pi,
        Complex.exp ((n : ℂ) * ((u : ℂ) + v * Complex.I)) *
          (eulerProduct ((u : ℂ) + v * Complex.I))⁻¹ ^ 2 := by
  have hq (v : ℝ) : ‖Complex.exp (-((u : ℂ) + v * Complex.I))‖ < 1 := by
    rw [Complex.norm_exp]
    simp [Real.exp_lt_one_iff, hu]
  have hs := summable_norm_twoColourGenerating (hq 0)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hs
  have h := angular_coefficient_of_summable (fun n => (twoColourPartitionCount n : ℂ)) n u hs
  simpa only [← twoColourGenerating_eq_tsum (hq _), twoColourGenerating_exp_neg] using h

/-- The eta prefactor for the two-colour series gives the shift `1/12` in the exponent. -/
theorem twoColourGenerating_exp_neg_eq_eta (ζ : ℂ) :
    twoColourGenerating (Complex.exp (-ζ)) = Complex.exp (-ζ / 12) *
      (ModularForm.eta (Complex.I * ζ / (2 * Real.pi)))⁻¹ ^ 2 := by
  rw [twoColourGenerating_exp_neg, eta_rightHalfPlane, mul_inv_rev, mul_pow,
    ← Complex.exp_neg, ← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
  have hzero : -ζ / 12 + (2 : ℕ) * -(-ζ / 24) = 0 := by push_cast; ring
  rw [hzero, Complex.exp_zero, mul_one]

/-- The exact reciprocal-square transformation at the reduced fraction `0/1`. -/
theorem twoColourGenerating_modular_cusp_zero {ζ : ℂ} (hζ : 0 < ζ.re) :
    twoColourGenerating (Complex.exp (-ζ)) =
      (ζ / (2 * Real.pi)) * Complex.exp (-ζ / 12 + (Real.pi : ℂ) ^ 2 / (3 * ζ)) *
        twoColourGenerating (Complex.exp (-(4 * (Real.pi : ℂ) ^ 2 / ζ))) := by
  rw [twoColourGenerating_exp_neg, twoColourGenerating_exp_neg, eulerProduct_modular hζ,
    mul_inv_rev, mul_inv_rev, mul_pow, mul_pow]
  have hroot : (Complex.sqrt (2 * (Real.pi : ℂ) / ζ))⁻¹ ^ 2 = ζ / (2 * Real.pi) := by
    rw [inv_pow, Complex.sqrt, ← Complex.cpow_nat_mul]
    rw [show ((2 : ℕ) : ℂ) * (2 : ℂ)⁻¹ = 1 by norm_num, Complex.cpow_one, inv_div]
  have hexp : (Complex.exp (ζ / 24 - (Real.pi : ℂ) ^ 2 / (6 * ζ)))⁻¹ ^ 2 =
      Complex.exp (-ζ / 12 + (Real.pi : ℂ) ^ 2 / (3 * ζ)) := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hroot, hexp]
  ring

/-- The exact contour integral of the inverse squared eta function for `p₂(n)`. -/
theorem twoColourPartitionCount_eq_eta_angular_integral (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (twoColourPartitionCount n : ℂ) = (2 * Real.pi : ℂ)⁻¹ *
      ∫ v : ℝ in -Real.pi..Real.pi,
        Complex.exp (((n : ℂ) - 1 / 12) * ((u : ℂ) + v * Complex.I)) *
          (ModularForm.eta (Complex.I * ((u : ℂ) + v * Complex.I) / (2 * Real.pi)))⁻¹ ^ 2 := by
  rw [twoColourPartitionCount_eq_angular_integral n hu]
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [← twoColourGenerating_exp_neg, twoColourGenerating_exp_neg_eq_eta, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

end DurfeeCCS.Step06
