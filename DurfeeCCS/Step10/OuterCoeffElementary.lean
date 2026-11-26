module

public import DurfeeCCS.Step06.RademacherGenerating
public import DurfeeCCS.Step10.OuterFarCoefficients
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-! The two-colour coefficient bounds of (66) and (67). -/

@[expose] public section

namespace DurfeeCCS.Step10

open Step06 PowerSeries Finset

private theorem exp_product_log_bound {u : ℝ} (hu : 0 < u) (d : ℕ) :
    (∏ j ∈ range d, (1 - (Real.exp (-u)) ^ (j + 1)))⁻¹ ^ (2 : ℕ) ≤
      Real.exp (Real.pi ^ 2 / (3 * u)) := by
  let q := Real.exp (-u)
  have hq₀ : 0 < q := Real.exp_pos _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let a j : ℝ := 1 - q ^ (j + 1 : ℕ)
  have ha (j : ℕ) : 0 < a j := by
    dsimp [a]
    apply sub_pos.mpr
    exact pow_lt_one₀ hq₀.le hq₁ (Nat.succ_ne_zero j)
  let term (j k : ℕ) : ℝ := (q ^ (j + 1)) ^ (k + 1) / (k + 1 : ℝ)
  have ht (j : ℕ) : HasSum (term j) (-Real.log (a j)) := by
    apply Real.hasSum_pow_div_log_of_abs_lt_one
    rw [abs_of_nonneg (by positivity)]
    exact pow_lt_one₀ hq₀.le hq₁ (Nat.succ_ne_zero j)
  have hterm (k : ℕ) : (∑ j ∈ range d, term j k) ≤
      (1 / u) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    let v := (k + 1 : ℝ) * u
    have hv : 0 < v := by dsimp [v]; positivity
    let w := Real.exp (-v)
    have hw₀ : 0 < w := Real.exp_pos _
    have hw₁ : w < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have he (j : ℕ) : term j k = w / (k + 1 : ℝ) * w ^ j := by
      dsimp [term, q, w, v]
      rw [← pow_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      push_cast
      ring
    have hs := (summable_geometric_of_lt_one hw₀.le hw₁).mul_left (w / (k + 1 : ℝ))
    have hd : 0 < Real.exp v - 1 := by linarith [Real.one_lt_exp_iff.mpr hv]
    have hn : 0 < (k + 1 : ℝ) := by positivity
    calc
      _ = ∑ j ∈ range d, w / (k + 1 : ℝ) * w ^ j := sum_congr rfl (fun j _ => he j)
      _ ≤ ∑' j : ℕ, w / (k + 1 : ℝ) * w ^ j := hs.sum_le_tsum _ (fun j _ => by positivity)
      _ = 1 / ((k + 1 : ℝ) * (Real.exp v - 1)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hw₀.le hw₁]
        dsimp [w]
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero, (sub_pos.mpr hw₁).ne', hd.ne', hn.ne']
      _ ≤ 1 / ((k + 1 : ℝ) * v) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp v]) hn.le
      _ = _ := by dsimp [v]; push_cast; field_simp [hu.ne', hn.ne']
  have zetaSucc : HasSum (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := hasSum_zeta_two.summable.tsum_eq_zero_add
    rw [hasSum_zeta_two.tsum_eq] at h
    have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ)^2 = 0 := by norm_num
    change Real.pi ^ 2 / 6 = 1 / ((0 : ℕ) : ℝ)^2 +
      ∑' k : ℕ, (1 : ℝ) / ((k + 1 : ℕ) : ℝ)^2 at h
    rw [h0, zero_add] at h
    rw [h]
    exact (hasSum_zeta_two.summable.comp_injective Nat.succ_injective).hasSum
  have hh : HasSum (fun k => ∑ j ∈ range d, term j k) (∑ j ∈ range d, -Real.log (a j)) :=
    hasSum_sum fun j _ => ht j
  have hh' := (zetaSucc.mul_left (1 / u))
  have hlog : (∑ j ∈ range d, -Real.log (a j)) ≤ 1 / u * (Real.pi ^ 2 / 6) :=
    by rw [← hh.tsum_eq, ← hh'.tsum_eq]; exact hh.summable.tsum_le_tsum hterm hh'.summable
  let p := ∏ j ∈ range d, a j
  have hp : 0 < p := Finset.prod_pos fun j _ => ha j
  change p⁻¹ ^ (2 : ℕ) ≤ _
  apply (Real.log_le_log_iff (by positivity) (Real.exp_pos _)).mp
  rw [Real.log_pow, Real.log_inv, show p = ∏ j ∈ range d, a j by rfl, Real.log_prod (fun j _ => (ha j).ne'),
    ← Finset.sum_neg_distrib, Real.log_exp]
  push_cast
  calc
    _ ≤ 2 * (1 / u * (Real.pi ^ 2 / 6)) := by linarith
    _ = _ := by ring

private theorem restrictedPair_coeff_nonneg (d i : ℕ) : 0 ≤ coeff i (restrictedPairSeries d) := by
  rw [coeff_restrictedPairSeries]
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))

set_option maxHeartbeats 700000 in
private theorem twoColour_exp_bound_param (t : ℕ) {u : ℝ} (hu : 0 < u) :
    (twoColourPartitionCount t : ℝ) ≤ Real.exp (u * t + Real.pi ^ 2 / (3 * u)) := by
  let q := Real.exp (-u)
  have hq₀ : 0 < q := Real.exp_pos _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq : ‖(q : ℂ)‖ < 1 := by simpa [abs_of_pos hq₀] using hq₁
  have hs := Complex.hasSum_re (hasSum_coeff_restrictedPairSeries hq t)
  have hE (i : ℕ) : (((coeff i (restrictedPairSeries t) : ℤ) : ℂ) * (q : ℂ) ^ i).re =
      ((coeff i (restrictedPairSeries t) : ℤ) : ℝ) * q ^ i := by
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [hE] at hs
  have hsum := hs.summable.le_tsum t (fun i _ => mul_nonneg
    (by exact_mod_cast restrictedPair_coeff_nonneg t i) (pow_nonneg hq₀.le _))
  rw [hs.tsum_eq, ← twoColourPartitionCount_eq_coeff_restricted t t le_rfl] at hsum
  have hprod : ((qPochhammer (q : ℂ) (q : ℂ) t)⁻¹ ^ (2 : ℕ)).re =
      (∏ j ∈ range t, (1 - q ^ (j + 1)))⁻¹ ^ (2 : ℕ) := by
    rw [qPochhammer_self_eq_prod]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_prod, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [hprod] at hsum
  have hb := hsum.trans (exp_product_log_bound hu t)
  have hqe : q ^ t = Real.exp (-u * t) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hqe, ← le_div_iff₀ (Real.exp_pos _), ← Real.exp_sub] at hb
  convert hb using 2
  ring

/-- The elementary coefficient envelope of (66). -/
theorem twoColour_exp_bound (t : ℕ) :
    (twoColourPartitionCount t : ℝ) ≤ Real.exp (2 * Real.pi * Real.sqrt ((t : ℝ) / 3)) := by
  by_cases ht : t = 0
  · simp [ht]
  have hn : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
  let u := Real.pi / Real.sqrt (3 * (t : ℝ))
  have hu : 0 < u := by dsimp [u]; positivity
  have hu₂ : u ^ 2 * (3 * (t : ℝ)) = Real.pi ^ 2 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have h₁ : Real.pi ^ 2 / (3 * u) = u * (t : ℝ) := by
    apply (div_eq_iff (by positivity)).mpr
    linear_combination -hu₂
  have h₂ : (u * (t : ℝ)) ^ 2 = (Real.pi * Real.sqrt ((t : ℝ) / 3)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    linear_combination (t : ℝ) / 3 * hu₂
  have he : u * (t : ℝ) = Real.pi * Real.sqrt ((t : ℝ) / 3) := by
    apply (pow_left_inj₀ (by positivity) (by positivity) (by decide : (2 : ℕ) ≠ 0)).mp
    exact h₂
  have h := twoColour_exp_bound_param t hu
  rwa [h₁, he, ← two_mul, ← mul_assoc] at h

/-- Both inequalities in (67), with the pointwise bound for every omitted size. -/
theorem twoColour_restricted_error {k t : ℕ} (hkt : k + 1 ≤ t) :
    0 ≤ (twoColourPartitionCount t : ℝ) - ((coeff t (restrictedPairSeries k) : ℤ) : ℝ) ∧
      (twoColourPartitionCount t : ℝ) - ((coeff t (restrictedPairSeries k) : ℤ) : ℝ) ≤
        2 * (t : ℝ) * Real.exp (2 * Real.pi * Real.sqrt (((t - k - 1 : ℕ) : ℝ) / 3)) := by
  constructor
  · exact sub_nonneg.mpr (by exact_mod_cast restrictedPair_le_twoColour k t)
  · have hs : (twoColourPartitionCount t : ℝ) - ((coeff t (restrictedPairSeries k) : ℤ) : ℝ) ≤
        2 * ∑ j ∈ range (t - k), (twoColourPartitionCount j : ℝ) := by
        exact_mod_cast (twoColour_sub_restrictedPair_le t k).2
    refine hs.trans ?_
    let E := Real.exp (2 * Real.pi * Real.sqrt (((t - k - 1 : ℕ) : ℝ) / 3))
    have hE : (∑ j ∈ range (t - k), (twoColourPartitionCount j : ℝ)) ≤
        ((range (t - k)).card : ℝ) * E := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro j hj
      refine (twoColour_exp_bound j).trans ?_
      dsimp [E]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast (by have := Finset.mem_range.mp hj; omega : j ≤ t - k - 1)
    have hc : ((range (t - k)).card : ℝ) ≤ t := by
      exact_mod_cast (by rw [Finset.card_range]; omega : (range (t - k)).card ≤ t)
    exact (mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le))
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by dsimp [E]; ring)

end DurfeeCCS.Step10
