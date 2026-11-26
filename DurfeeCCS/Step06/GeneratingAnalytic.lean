module

public import DurfeeCCS.CoefficientDP
public import DurfeeCCS.Scalars
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed

/-! The absolutely convergent Durfee generating function on the open q-disc. -/

@[expose] public section

namespace DurfeeCCS

open Finset Filter PowerSeries
open scoped BigOperators Topology

/-- The finite factor `(a;q)_d`. -/
noncomputable def qPochhammer (a q : ℂ) (d : ℕ) : ℂ :=
  ∏ j ∈ range d, (1 - a * q ^ j)

@[simp] theorem qPochhammer_zero (a q : ℂ) : qPochhammer a q 0 = 1 := by
  simp [qPochhammer]

theorem qPochhammer_succ (a q : ℂ) (d : ℕ) :
    qPochhammer a q (d + 1) = qPochhammer a q d * (1 - a * q ^ d) := by
  rw [qPochhammer, prod_range_succ, qPochhammer]

theorem qPochhammer_self_eq_prod (q : ℂ) (d : ℕ) :
    qPochhammer q q d = ∏ j ∈ range d, (1 - q ^ (j + 1)) := by
  simp only [qPochhammer, pow_succ']

/-- The analytic version of the Durfee generating function, using the polynomial coefficients. -/
noncomputable def durfeeAnalyticF (x q : ℂ) : ℂ :=
  ∑' n : ℕ, (durfeePolynomialComplex n).eval x * q ^ n

private noncomputable def seriesTerm (A : ℤ⟦X⟧) (q : ℂ) (n : ℕ) : ℂ :=
  ((coeff n A : ℤ) : ℂ) * q ^ n

private def AbsSum (f : ℕ → ℂ) (l : ℂ) : Prop :=
  HasSum f l ∧ Summable (fun n => ‖f n‖)

private theorem coeff_geometricFactor (j k : ℕ) (hj : 0 < j) :
    coeff k (durfeeGeometricFactor j) = if j ∣ k then 1 else 0 := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have h := coeff_mul_geometric (1 : ℤ⟦X⟧) j k hj
    simp only [one_mul, coeff_one] at h
    rw [h]
    rcases eq_or_ne k 0 with rfl | hk
    · simp [not_le.mpr hj]
    · simp only [hk, ite_false, zero_add]
      by_cases h : j ≤ k
      · rw [ite_eq_left h, ih (k - j) (by omega)]
        have hd : j ∣ k - j ↔ j ∣ k := by
          constructor
          · intro hd
            have he := Nat.dvd_add hd (dvd_refl j)
            rwa [Nat.sub_add_cancel h] at he
          · intro hd
            exact Nat.dvd_sub hd (dvd_refl j)
        simp [hd]
      · have hd : ¬j ∣ k := fun hdiv => h (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hdiv)
        simp [h, hd]

private theorem absSum_seriesTerm_one (q : ℂ) : AbsSum (seriesTerm 1 q) 1 := by
  classical
  have hz (n : ℕ) (hn : n ≠ 0) : seriesTerm 1 q n = 0 := by
    simp [seriesTerm, coeff_one, hn]
  refine ⟨?_, (hasSum_single 0 (fun n hn => by rw [hz n hn, norm_zero])).summable⟩
  simpa [seriesTerm] using hasSum_single 0 hz

private theorem absSum_seriesTerm_geometric (q : ℂ) (hq : ‖q‖ < 1) (j : ℕ) (hj : 0 < j) :
    AbsSum (seriesTerm (durfeeGeometricFactor j) q) (1 - q ^ j)⁻¹ := by
  classical
  let g : ℕ → ℕ := fun k => j * k
  have hg : Function.Injective g := fun a b hab => Nat.eq_of_mul_eq_mul_left hj hab
  have hz (k : ℕ) (hk : k ∉ Set.range g) : seriesTerm (durfeeGeometricFactor j) q k = 0 := by
    have hd : ¬ j ∣ k := fun ⟨l, hl⟩ => hk ⟨l, hl.symm⟩
    simp [seriesTerm, coeff_geometricFactor _ _ hj, hd]
  have ht (k : ℕ) : seriesTerm (durfeeGeometricFactor j) q (g k) = (q ^ j) ^ k := by
    dsimp [g]
    simp [seriesTerm, coeff_geometricFactor _ _ hj, pow_mul]
  have hqj : ‖q ^ j‖ < 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    rw [norm_pow, pow_succ]
    exact (mul_le_of_le_one_left (norm_nonneg q) (pow_le_one₀ (norm_nonneg q) hq.le)).trans_lt hq
  refine ⟨(hg.hasSum_iff hz).mp ?_, (hg.summable_iff (fun k hk => by simp [hz k hk])).mp ?_⟩
  · exact (hasSum_geometric_of_norm_lt_one hqj).congr_fun ht
  · exact (summable_geometric_of_lt_one (norm_nonneg (q ^ j)) hqj).congr
      (fun k => by simp only [Function.comp_apply, ht, norm_pow])

private theorem absSum_seriesTerm_mul {A B : ℤ⟦X⟧} {q a b : ℂ}
    (ha : AbsSum (seriesTerm A q) a) (hb : AbsSum (seriesTerm B q) b) :
    AbsSum (seriesTerm (A * B) q) (a * b) := by
  have h (n : ℕ) : seriesTerm (A * B) q n =
      ∑ kl ∈ antidiagonal n, seriesTerm A q kl.1 * seriesTerm B q kl.2 := by
    simp only [seriesTerm, coeff_mul, Int.cast_sum, sum_mul, Int.cast_mul]
    refine sum_congr rfl fun kl hkl => ?_
    rw [← mem_antidiagonal.mp hkl, pow_add]
    ac_rfl
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm ha.2 hb.2
  refine ⟨?_, hs.congr (fun n => by rw [h])⟩
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha.2 hb.2
  rw [ha.1.tsum_eq, hb.1.tsum_eq] at heq
  exact (heq ▸ hs.of_norm.hasSum).congr_fun h

private theorem absSum_restrictedPairSeries (q : ℂ) (hq : ‖q‖ < 1) (d : ℕ) :
    AbsSum (seriesTerm (restrictedPairSeries d) q) ((qPochhammer q q d)⁻¹ ^ 2) := by
  induction d with
  | zero => simpa [restrictedPairSeries] using absSum_seriesTerm_one q
  | succ d ih =>
    have hgeom := absSum_seriesTerm_geometric q hq (d + 1) (Nat.succ_pos _)
    have h := absSum_seriesTerm_mul (absSum_seriesTerm_mul ih hgeom) hgeom
    have hp : qPochhammer q q (d + 1) = qPochhammer q q d * (1 - q ^ (d + 1)) := by
      rw [qPochhammer_succ, pow_succ']
    rw [restrictedPairSeries_succ_eq_twice, hp, mul_inv_rev]
    convert h using 1
    simp only [pow_two]
    ac_rfl

/-- Analytic evaluation of the finite product for partitions of two colours. -/
theorem hasSum_coeff_restrictedPairSeries {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) :
    HasSum (fun n => ((coeff n (restrictedPairSeries d) : ℤ) : ℂ) * q ^ n)
      ((qPochhammer q q d)⁻¹ ^ 2) :=
  (absSum_restrictedPairSeries q hq d).1

theorem summable_norm_coeff_restrictedPairSeries {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) :
    Summable (fun n => ‖((coeff n (restrictedPairSeries d) : ℤ) : ℂ) * q ^ n‖) :=
  (absSum_restrictedPairSeries q hq d).2


private theorem absSum_restrictedPartitionSeries (q : ℂ) (hq : ‖q‖ < 1) (d : ℕ) :
    AbsSum (seriesTerm (restrictedPartitionSeries d) q) (qPochhammer q q d)⁻¹ := by
  induction d with
  | zero => simpa [restrictedPartitionSeries_eq_prod] using absSum_seriesTerm_one q
  | succ d ih =>
    rw [restrictedPartitionSeries_eq_prod, Finset.prod_range_succ, ← restrictedPartitionSeries_eq_prod,
      qPochhammer_succ, mul_inv_rev, ← pow_succ']
    rw [mul_comm ((1 - q ^ (d + 1))⁻¹)]
    exact absSum_seriesTerm_mul ih (absSum_seriesTerm_geometric q hq (d + 1) (Nat.succ_pos _))

/-- Analytic evaluation of a product with separate cutoffs for the two colours. -/
theorem hasSum_coeff_restrictedMixedSeries {q : ℂ} (hq : ‖q‖ < 1) (a b : ℕ) :
    HasSum (fun n => ((coeff n (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℂ) *
      q ^ n) ((qPochhammer q q a)⁻¹ * (qPochhammer q q b)⁻¹) ∧
    Summable (fun n =>
      ‖((coeff n (restrictedPartitionSeries a * restrictedPartitionSeries b) : ℤ) : ℂ) * q ^ n‖) :=
  absSum_seriesTerm_mul (absSum_restrictedPartitionSeries q hq a)
    (absSum_restrictedPartitionSeries q hq b)

/-- Multiply two absolutely convergent coefficient series. -/
theorem hasSum_coeff_mul_of_summable_norm {A B : ℤ⟦X⟧} {q a b : ℂ}
    (ha : HasSum (fun n => ((coeff n A : ℤ) : ℂ) * q ^ n) a)
    (ham : Summable (fun n => ‖((coeff n A : ℤ) : ℂ) * q ^ n‖))
    (hb : HasSum (fun n => ((coeff n B : ℤ) : ℂ) * q ^ n) b)
    (hbm : Summable (fun n => ‖((coeff n B : ℤ) : ℂ) * q ^ n‖)) :
    HasSum (fun n => ((coeff n (A * B) : ℤ) : ℂ) * q ^ n) (a * b) ∧
    Summable (fun n => ‖((coeff n (A * B) : ℤ) : ℂ) * q ^ n‖) :=
  absSum_seriesTerm_mul ⟨ha, ham⟩ ⟨hb, hbm⟩


private theorem norm_pow_succ_le_norm {q : ℂ} (hq : ‖q‖ ≤ 1) (d : ℕ) :
    ‖q ^ (d + 1)‖ ≤ ‖q‖ := by
  rw [norm_pow, pow_succ]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq)

theorem norm_inv_qPochhammer_self_le {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) :
    ‖(qPochhammer q q d)⁻¹‖ ≤ ((1 - ‖q‖)⁻¹) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hs : 1 - ‖q‖ ≤ ‖1 - q ^ (d + 1)‖ := calc
      1 - ‖q‖ ≤ 1 - ‖q ^ (d + 1)‖ := sub_le_sub_left (norm_pow_succ_le_norm hq.le _) _
      _ ≤ ‖1 - q ^ (d + 1)‖ := by simpa using norm_sub_norm_le (1 : ℂ) (q ^ (d + 1))
    have hInv : ‖(1 - q ^ (d + 1))⁻¹‖ ≤ (1 - ‖q‖)⁻¹ := by
      rw [norm_inv]
      exact inv_anti₀ (sub_pos.mpr hq) hs
    calc
      ‖(qPochhammer q q (d + 1))⁻¹‖ = ‖(1 - q ^ (d + 1))⁻¹‖ * ‖(qPochhammer q q d)⁻¹‖ := by
        rw [qPochhammer_succ, ← pow_succ', mul_inv_rev, norm_mul]
      _ ≤ (1 - ‖q‖)⁻¹ * ((1 - ‖q‖)⁻¹) ^ d :=
        mul_le_mul hInv ih (norm_nonneg _) (by positivity)
      _ = ((1 - ‖q‖)⁻¹) ^ (d + 1) := (pow_succ' _ _).symm

private theorem summable_polynomial_geometric {r c : ℝ} (hr : r < 1) (hr₀ : 0 ≤ r)
    (hc : 0 ≤ c) : Summable (fun n : ℕ => r ^ (n * n) * c ^ n) := by
  have hlim : Tendsto (fun n : ℕ => r ^ n * c) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr).mul_const c
  refine (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).of_norm_bounded_eventually_nat ?_
  filter_upwards [hlim.eventually_le_const (by norm_num : 0 < (1 / 2 : ℝ))] with n hn
  rw [pow_mul, ← mul_pow, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (mul_nonneg (pow_nonneg hr₀ _) hc) _)]
  exact pow_le_pow_left₀ (mul_nonneg (pow_nonneg hr₀ _) hc) hn _

/-- The bivariate summand of the Durfee generating function, with natural indices `n,d`. -/
private noncomputable def durfeeAnalyticTerm (x q : ℂ) (n d : ℕ) : ℂ :=
  (p n d : ℂ) * x ^ d * q ^ n

private theorem absSum_durfeeAnalyticTerm_d (x q : ℂ) (hq : ‖q‖ < 1) (d : ℕ) :
    AbsSum (fun n => durfeeAnalyticTerm x q n d)
      (q ^ (d * d) * x ^ d * (qPochhammer q q d)⁻¹ ^ 2) := by
  let g : ℕ → ℕ := fun k => d * d + k
  have hg : Function.Injective g := fun a b h => Nat.add_left_cancel h
  have hz (n : ℕ) (hn : n ∉ Set.range g) : durfeeAnalyticTerm x q n d = 0 := by
    have hs : n < d * d := by
      by_contra! he
      exact hn ⟨n - d * d, Nat.add_sub_of_le he⟩
    simp [durfeeAnalyticTerm, p_eq_zero_of_sq_gt hs]
  have hf := absSum_restrictedPairSeries q hq d
  have ht (k : ℕ) : durfeeAnalyticTerm x q (g k) d =
      (q ^ (d * d) * x ^ d) * seriesTerm (restrictedPairSeries d) q k := by
    have h : (p (g k) d : ℤ) = coeff k (restrictedPairSeries d) := by
      simpa [g] using (p_eq_coeff_restrictedPairSeries (n := g k) (d := d) (by dsimp [g]; omega))
    calc
      durfeeAnalyticTerm x q (g k) d = ((p (g k) d : ℤ) : ℂ) * x ^ d * q ^ (d * d + k) := by
        simp [durfeeAnalyticTerm, g]
      _ = _ := by rw [h, pow_add]; unfold seriesTerm; ac_rfl
  refine ⟨(hg.hasSum_iff hz).mp ?_, (hg.summable_iff (fun n hn => by simp [hz n hn])).mp ?_⟩
  · exact (hf.1.mul_left (q ^ (d * d) * x ^ d)).congr_fun ht
  · exact (hf.2.mul_left ‖q ^ (d * d) * x ^ d‖).congr
      (fun k => by simp only [Function.comp_apply, ht, norm_mul])

private theorem summable_norm_durfeeAnalyticTerm (x : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ × ℕ => ‖durfeeAnalyticTerm x q m.2 m.1‖) := by
  refine (summable_prod_of_nonneg (fun m => norm_nonneg _)).mpr
    ⟨fun d => (absSum_durfeeAnalyticTerm_d x q hq d).2, ?_⟩
  let r := ‖q‖
  let c := ‖x‖ * ((1 - r)⁻¹) ^ 2
  refine (summable_polynomial_geometric (c := c) hq (norm_nonneg q) (by positivity)).of_nonneg_of_le
    (fun _ => tsum_nonneg (fun _ => norm_nonneg _)) (fun d => ?_)
  let q' : ℂ := (r : ℂ)
  let x' : ℂ := (‖x‖ : ℂ)
  have hq' : ‖q'‖ < 1 := by simpa [q', r] using hq
  have hv (n : ℕ) : ‖durfeeAnalyticTerm x q n d‖ = (durfeeAnalyticTerm x' q' n d).re := by
    simp only [durfeeAnalyticTerm, norm_mul, norm_pow, Complex.norm_natCast, x', q', r]
    norm_cast
  calc
    (∑' n, ‖durfeeAnalyticTerm x q n d‖) =
        (q' ^ (d * d) * x' ^ d * (qPochhammer q' q' d)⁻¹ ^ 2).re := by
      simp_rw [hv]
      exact (Complex.hasSum_re (absSum_durfeeAnalyticTerm_d x' q' hq' d).1).tsum_eq
    _ ≤ ‖q' ^ (d * d) * x' ^ d * (qPochhammer q' q' d)⁻¹ ^ 2‖ := Complex.re_le_norm _
    _ = r ^ (d * d) * ‖x‖ ^ d * ‖(qPochhammer q' q' d)⁻¹‖ ^ 2 := by
      have hqnorm : ‖q'‖ = r := by simp [q', r]
      have hxnorm : ‖x'‖ = ‖x‖ := by simp [x']
      simp only [norm_mul, norm_pow, hqnorm, hxnorm]
    _ ≤ r ^ (d * d) * ‖x‖ ^ d * (((1 - r)⁻¹) ^ d) ^ 2 := by
      have hqnorm : ‖q'‖ = r := by simp [q', r]
      have hnorm := norm_inv_qPochhammer_self_le hq' d
      rw [hqnorm] at hnorm
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (by positivity)
    _ = r ^ (d * d) * c ^ d := by
      dsimp [c]
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 d, mul_assoc]

private theorem tsum_durfeeAnalyticTerm (x q : ℂ) (n : ℕ) :
    (∑' d : ℕ, durfeeAnalyticTerm x q n d) = (durfeePolynomialComplex n).eval x * q ^ n := by
  classical
  have hn : (durfeePolynomialComplex n).natDegree = n.sqrt := by
    rw [durfeePolynomialComplex, Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
      natDegree_durfeePolynomial]
  rw [tsum_eq_sum (s := range (n.sqrt + 1)), Polynomial.eval_eq_sum_range, hn, sum_mul]
  · simp [durfeeAnalyticTerm]
  · intro d hd
    have hds : n.sqrt < d := by
      simp only [mem_range, not_lt] at hd
      omega
    have hn := Nat.sqrt_lt.mp hds
    simp [durfeeAnalyticTerm, p_eq_zero_of_sq_gt hn]

/-- Absolute convergence of the polynomial expansion in (1), throughout the open q-disc. -/
theorem summable_norm_durfeeAnalyticF (x : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖(durfeePolynomialComplex n).eval x * q ^ n‖) := by
  have hs := (summable_norm_durfeeAnalyticTerm x hq).prod_symm
  have hrs := (summable_prod_of_nonneg (fun m : ℕ × ℕ => norm_nonneg (durfeeAnalyticTerm x q m.1 m.2))).mp hs
  refine hrs.2.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  rw [← tsum_durfeeAnalyticTerm]
  exact norm_tsum_le_tsum_norm (hrs.1 n)

theorem summable_durfeeAnalyticF (x : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => (durfeePolynomialComplex n).eval x * q ^ n) :=
  (summable_norm_durfeeAnalyticF x hq).of_norm

/-- Absolute convergence of the Durfee-square expansion in (1). -/
theorem summable_norm_durfeeAnalyticDiagonal (x : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun d : ℕ => ‖q ^ (d * d) * x ^ d * (qPochhammer q q d)⁻¹ ^ 2‖) := by
  have hs := (summable_prod_of_nonneg
    (fun m : ℕ × ℕ => norm_nonneg (durfeeAnalyticTerm x q m.2 m.1))).mp
      (summable_norm_durfeeAnalyticTerm x hq)
  refine hs.2.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ?_)
  rw [← (absSum_durfeeAnalyticTerm_d x q hq d).1.tsum_eq]
  exact norm_tsum_le_tsum_norm (hs.1 d)

/-- Equation (1) as an equality between absolutely convergent analytic sums. -/
theorem durfeeAnalyticF_eq_diagonal (x : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    durfeeAnalyticF x q = ∑' d : ℕ, q ^ (d * d) * x ^ d * (qPochhammer q q d)⁻¹ ^ 2 := by
  have hs := (summable_norm_durfeeAnalyticTerm x hq).of_norm
  unfold durfeeAnalyticF
  simp_rw [← tsum_durfeeAnalyticTerm]
  calc
    (∑' n : ℕ, ∑' d : ℕ, durfeeAnalyticTerm x q n d) =
        ∑' d : ℕ, ∑' n : ℕ, durfeeAnalyticTerm x q n d :=
      Summable.tsum_comm (f := fun d n => durfeeAnalyticTerm x q n d) hs
    _ = _ := tsum_congr (fun d => (absSum_durfeeAnalyticTerm_d x q hq d).1.tsum_eq)

end DurfeeCCS
