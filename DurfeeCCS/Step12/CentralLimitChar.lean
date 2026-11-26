module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Central limit theorem for finite Bernoulli rows

Taylor's bound is weighted by the variance of each summand. This gives an error
controlled by the sum of the variances, allowing the Bernoulli parameters to vary
both within a row and across rows.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter

namespace DurfeeCCS

/-- Total variance of a row of independent Bernoulli variables. -/
noncomputable def bernoulliVariance {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, p i * (1 - p i)

lemma bernoulliVariance_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ bernoulliVariance p :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i).1 (sub_nonneg.mpr (hp i).2)

/-- Characteristic function of a Bernoulli variable with its mean subtracted. -/
noncomputable def centeredBernoulliChar (p t : ℝ) : ℂ :=
  ((1 - p : ℝ) : ℂ) * Complex.exp (↑(-p * t : ℝ) * Complex.I) +
  (p : ℂ) * Complex.exp (↑((1 - p) * t : ℝ) * Complex.I)

theorem centeredBernoulliChar_eq (p t : ℝ) :
    centeredBernoulliChar p t =
      Complex.exp (↑(-p * t : ℝ) * Complex.I) *
        ((1 - (p : ℂ)) + (p : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) := by
  have harg : (↑((1 - p) * t : ℝ) : ℂ) * Complex.I =
      ↑(-p * t : ℝ) * Complex.I + (t : ℂ) * Complex.I := by
    push_cast
    ring
  rw [centeredBernoulliChar, harg, Complex.exp_add]
  push_cast
  ring

theorem prod_centeredBernoulliChar_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) (t : ℝ) :
    (∏ i, centeredBernoulliChar (p i) t) =
      Complex.exp (↑(-(∑ i, p i) * t : ℝ) * Complex.I) *
        ∏ i, ((1 - (p i : ℂ)) + (p i : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) := by
  simp only [centeredBernoulliChar_eq, Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  push_cast
  simp only [Finset.sum_neg_distrib, Finset.sum_mul, neg_mul]

theorem norm_centeredBernoulliChar_le_one {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) : ‖centeredBernoulliChar p t‖ ≤ 1 := by
  unfold centeredBernoulliChar
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hp.1, abs_of_nonneg (sub_nonneg.mpr hp.2)]
  linarith

private lemma norm_exp_sub_quadratic_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - (1 + z + z ^ 2 / 2)‖ ≤ ‖z‖ ^ 3 := by
  calc
    _ ≤ ‖z‖ ^ 3 * (4 / 18) := by
      have h := Complex.exp_bound (n := 3) hz (by decide)
      norm_num [Finset.sum_range_succ, Nat.factorial, div_eq_mul_inv] at h ⊢
      exact h
    _ ≤ ‖z‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg z) 3]

private noncomputable def expRemainder (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)

private lemma norm_expRemainder_le {x : ℝ} (hx : |x| ≤ 1) :
    ‖expRemainder x‖ ≤ |x| ^ 3 := by
  have hz : ‖(x : ℂ) * Complex.I‖ = |x| := by simp [Real.norm_eq_abs]
  have hsq : ((x : ℂ) * Complex.I) ^ 2 = -(x : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq, mul_neg_one]
  simpa only [expRemainder, hsq, neg_div, ← sub_eq_add_neg, hz] using
    norm_exp_sub_quadratic_le (z := (x : ℂ) * Complex.I) (hz ▸ hx)

private lemma centeredBernoulliChar_quadratic (p t : ℝ) :
    centeredBernoulliChar p t - (1 - ↑(p * (1 - p) * t ^ 2 / 2 : ℝ)) =
      ((1 - p : ℝ) : ℂ) * expRemainder (-p * t) +
        (p : ℂ) * expRemainder ((1 - p) * t) := by
  simp only [centeredBernoulliChar, expRemainder]
  push_cast
  ring

private lemma norm_centeredBernoulliChar_sub_exp_le {p t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (ht : |t| ≤ 1) :
    ‖centeredBernoulliChar p t - Complex.exp (↑(-(p * (1 - p) * t ^ 2 / 2) : ℝ))‖ ≤
      3 * (p * (1 - p)) * |t| ^ 3 := by
  have hp0 : 0 ≤ p := hp.1
  have hp1 : p ≤ 1 := hp.2
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  let v := p * (1 - p)
  have hv0 : 0 ≤ v := mul_nonneg hp0 hq0
  have hv1 : v ≤ 1 := by
    calc
      v ≤ 1 * 1 := mul_le_mul hp1 hq1 hq0 zero_le_one
      _ = 1 := one_mul 1
  have htp : |-p * t| = p * |t| := by simp [abs_mul, abs_of_nonneg hp0]
  have htq : |(1 - p) * t| = (1 - p) * |t| := by simp [abs_mul, abs_of_nonneg hq0]
  have harm : ‖centeredBernoulliChar p t - (1 - ↑(v * t ^ 2 / 2 : ℝ))‖ ≤
      2 * v * |t| ^ 3 := by
    rw [centeredBernoulliChar_quadratic]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0,
      abs_of_nonneg hq0]
    calc
      _ ≤ (1 - p) * (p * |t|) ^ 3 + p * ((1 - p) * |t|) ^ 3 := by
        gcongr
        · have hb : |-p * t| ≤ 1 := by rw [htp]; nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (abs_nonneg t)]
          simpa only [htp] using norm_expRemainder_le hb
        · have hb : |(1 - p) * t| ≤ 1 := by rw [htq]; nlinarith [mul_nonneg hp0 (abs_nonneg t)]
          simpa only [htq] using norm_expRemainder_le hb
      _ = v * |t| ^ 3 * (p ^ 2 + (1 - p) ^ 2) := by dsimp [v]; ring
      _ ≤ 2 * v * |t| ^ 3 := by
        have hsp : p ^ 2 ≤ 1 := pow_le_one₀ hp0 hp1
        have hsq : (1 - p) ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
        linarith [mul_le_mul_of_nonneg_left (add_le_add hsp hsq)
          (mul_nonneg hv0 (pow_nonneg (abs_nonneg t) 3))]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hsq : |t| ^ 2 ≤ |t| := by
    nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
  let a := v * t ^ 2 / 2
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha_le_vt2 : a ≤ v * |t| ^ 2 := by
    rw [← ht2]
    dsimp [a]
    nlinarith [mul_nonneg hv0 (sq_nonneg t)]
  have ha_le_t : a ≤ |t| := by
    refine ha_le_vt2.trans ?_
    exact (mul_le_of_le_one_left (sq_nonneg _) hv1).trans hsq
  have ha1 : a ≤ 1 := ha_le_t.trans ht
  have hnorma : ‖-(a : ℂ)‖ = a := by simp [Real.norm_eq_abs, abs_of_nonneg ha0]
  have hgauss : ‖(1 - (a : ℂ)) - Complex.exp (↑(-a : ℝ))‖ ≤ v * |t| ^ 3 := by
    have h₁ : ‖Complex.exp (-(a : ℂ)) - 1 - (-(a : ℂ))‖ ≤ a ^ 2 := by
      simpa only [hnorma] using
        (Complex.norm_exp_sub_one_sub_id_le (x := -(a : ℂ)) (by simpa [hnorma] using ha1))
    have h₂ : ‖(1 - (a : ℂ)) - Complex.exp (↑(-a : ℝ))‖ ≤ a ^ 2 := by
      rw [norm_sub_rev, Complex.ofReal_neg]
      convert h₁ using 2
      ring
    refine h₂.trans ?_
    calc
      a ^ 2 = a * a := sq a
      _ ≤ (v * |t| ^ 2) * |t| := mul_le_mul ha_le_vt2 ha_le_t ha0 (by positivity)
      _ = v * |t| ^ 3 := by ring
  calc
    _ ≤ ‖centeredBernoulliChar p t - (1 - (a : ℂ))‖ +
        ‖(1 - (a : ℂ)) - Complex.exp (↑(-a : ℝ))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * v * |t| ^ 3 + v * |t| ^ 3 := add_le_add harm hgauss
    _ = 3 * v * |t| ^ 3 := by ring

private lemma norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hprod : ‖∏ j ∈ s, g j‖ ≤ 1 := by
      rw [Complex.norm_prod]
      exact Finset.prod_le_one₀ (fun j _ ↦ norm_nonneg _) (fun j _ ↦ hg j)
    calc
      _ = ‖(f i - g i) * (∏ j ∈ s, g j) +
          f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)‖ := by
        congr 1
        ring
      _ ≤ ‖f i - g i‖ * ‖∏ j ∈ s, g j‖ +
            ‖f i‖ * ‖(∏ j ∈ s, f j) - ∏ j ∈ s, g j‖ := by
        rw [← norm_mul, ← norm_mul]
        exact norm_add_le _ _
      _ ≤ ‖f i - g i‖ + ∑ j ∈ s, ‖f j - g j‖ := by
        exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) hprod)
          ((mul_le_of_le_one_left (norm_nonneg _) (hf i)).trans ih)

private lemma norm_prod_centeredBernoulliChar_sub_exp_le {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : |t| ≤ 1) :
    ‖(∏ i, centeredBernoulliChar (p i) t) -
      Complex.exp (↑(-(bernoulliVariance p * t ^ 2 / 2) : ℝ))‖ ≤
      3 * bernoulliVariance p * |t| ^ 3 := by
  let g : ι → ℂ := fun i ↦ Complex.exp (↑(-(p i * (1 - p i) * t ^ 2 / 2) : ℝ))
  have hg : ∀ i, ‖g i‖ ≤ 1 := by
    intro i
    dsimp only [g]
    rw [Complex.norm_exp_ofReal, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (div_nonneg
      (mul_nonneg (mul_nonneg (hp i).1 (sub_nonneg.mpr (hp i).2)) (sq_nonneg t))
      (by norm_num))
  have heq : (∏ i, g i) = Complex.exp (↑(-(bernoulliVariance p * t ^ 2 / 2) : ℝ)) := by
    unfold g bernoulliVariance
    rw [← Complex.exp_sum]
    congr 1
    rw [← Complex.ofReal_sum]
    congr 1
    simp [Finset.sum_neg_distrib, div_eq_mul_inv, ← Finset.sum_mul]
  rw [← heq]
  calc
    _ ≤ ∑ i, ‖centeredBernoulliChar (p i) t - g i‖ :=
      norm_prod_sub_prod_le _ _ _ (fun i ↦ norm_centeredBernoulliChar_le_one (hp i) t) hg
    _ ≤ ∑ i, 3 * (p i * (1 - p i)) * |t| ^ 3 :=
      Finset.sum_le_sum fun i _ ↦ norm_centeredBernoulliChar_sub_exp_le (hp i) ht
    _ = _ := by rw [bernoulliVariance, Finset.mul_sum, Finset.sum_mul]

/-- Characteristic functions of centered and standardized independent Bernoulli
sums converge to the standard Gaussian characteristic function when the row
variances diverge. The size of the finite index set may depend on the row. -/
theorem tendsto_prod_centeredBernoulliChar {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (p : ∀ n, ι n → ℝ) (hp : ∀ n i, p n i ∈ Set.Icc (0 : ℝ) 1)
    (hV : Tendsto (fun n ↦ bernoulliVariance (p n)) atTop atTop) (t : ℝ) :
    Tendsto (fun n ↦ ∏ i, centeredBernoulliChar (p n i) (t / Real.sqrt (bernoulliVariance (p n))))
      atTop (𝓝 (Complex.exp (↑(-(t ^ 2) / 2 : ℝ)))) := by
  let V : ℕ → ℝ := fun n ↦ bernoulliVariance (p n)
  let s : ℕ → ℝ := fun n ↦ Real.sqrt (V n)
  have hs : Tendsto s atTop atTop := Real.tendsto_sqrt_atTop.comp hV
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using (tendsto_inv_atTop_zero.comp hs).const_mul (3 * |t| ^ 3))
  filter_upwards [hs.eventually (eventually_ge_atTop (max 1 |t|))] with n hn
  have hpos : 0 < s n := zero_lt_one.trans_le ((le_max_left _ _).trans hn)
  have hn' : |t| ≤ s n := (le_max_right _ _).trans hn
  have hsn : s n ^ 2 = V n := Real.sq_sqrt (bernoulliVariance_nonneg (hp n))
  have ht : |t / s n| ≤ 1 := by
    simpa [abs_div, abs_of_pos hpos, div_le_one hpos] using hn'
  have hexp : -(V n * (t / s n) ^ 2 / 2) = -(t ^ 2) / 2 := by
    rw [← hsn]
    field_simp [hpos.ne']
  have hbound : 3 * V n * |t / s n| ^ 3 = (3 * |t| ^ 3) * (s n)⁻¹ := by
    rw [← hsn, abs_div, abs_of_pos hpos]
    field_simp [hpos.ne']
  have h := norm_prod_centeredBernoulliChar_sub_exp_le (hp n) ht
  change ‖(∏ i, centeredBernoulliChar (p n i) (t / s n)) -
    Complex.exp (↑(-(V n * (t / s n) ^ 2 / 2) : ℝ))‖ ≤ 3 * V n * |t / s n| ^ 3 at h
  rw [hexp, hbound] at h
  exact h

end DurfeeCCS
