module

public import DurfeeCCS.Step08.NearOriginDefs
public import DurfeeCCS.Step08.NearOriginSinh
public import DurfeeCCS.Step08.ExpRemainder

/-! Pointwise logarithm and exponential errors in the regions of (18). -/

@[expose] public noncomputable section

open Complex

namespace DurfeeCCS.Step08

theorem norm_pairedLogCoeff_le_power (r : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) (k : ℕ) :
    ‖pairedLogCoeff r ζ k‖ ≤ 2 * |r| ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 2 * ζ.re) := by
  have hk := re_mul_nat_le_norm_sinh hζ.le (k + 1)
  rw [pairedLogCoeff, norm_div, norm_mul, norm_mul, norm_pow, norm_mul, norm_neg, norm_neg,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  norm_num only [Complex.norm_ofNat]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc
    _ = ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * ζ.re) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (by positivity)

theorem norm_pairedLogMode_le_power (r θ : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) (k : ℕ) :
    ‖pairedLogMode r θ ζ k‖ ≤ 2 * |r| ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 2 * ζ.re) := by
  rw [pairedLogMode, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)).trans
    (norm_pairedLogCoeff_le_power r hζ k)

def pairedLogTail (r θ : ℝ) (ζ : ℂ) (k : ℕ) : ℂ :=
  ∑' m : ℕ, pairedLogMode r θ ζ (m + k)

theorem norm_pairedLogTail_series_bounds {r : ℝ} (θ : ℝ) {ζ : ℂ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hζ : 0 < ζ.re) (k : ℕ) :
    let S := 2 / ζ.re * ∑' m : ℕ, r ^ (m + k + 1) / (((m + k + 1 : ℕ) : ℝ) ^ 2)
    ‖pairedLogTail r θ ζ k‖ ≤ S ∧
      S ≤ 2 * r ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 2 * ζ.re * (1 - r)) := by
  let C := r ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 2)
  let a (m : ℕ) := r ^ (m + k + 1) / (((m + k + 1 : ℕ) : ℝ) ^ 2)
  have h : Summable (fun m : ℕ => ‖pairedLogMode r θ ζ (m + k)‖) :=
    (summable_nat_add_iff k).2 (summable_norm_pairedLogMode r θ
      (by rw [abs_of_nonneg hr₀]; exact hr₁.le) hζ)
  have hg := (summable_geometric_of_lt_one hr₀ hr₁).mul_left C
  have hb (m : ℕ) : a m ≤ C * r ^ m := by
    have hm : ((k + 1 : ℕ) : ℝ) ≤ ((m + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega :
      k + 1 ≤ m + k + 1)
    dsimp only [a, C]
    rw [show m + k + 1 = (k + 1) + m by omega, pow_add,
      show (r ^ (k + 1) * r ^ m) / (((k + 1 + m : ℕ) : ℝ) ^ 2) =
        (r ^ (k + 1) / (((k + 1 + m : ℕ) : ℝ) ^ 2)) * r ^ m by ring]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr₀ _)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by
      simpa only [show (k + 1 + m : ℕ) = m + k + 1 by omega] using hm) 2
  have ha : Summable a := hg.of_nonneg_of_le (fun _ => by dsimp [a]; positivity) hb
  have hm (m : ℕ) : ‖pairedLogMode r θ ζ (m + k)‖ ≤ (2 / ζ.re) * a m := by
    refine (norm_pairedLogMode_le_power r θ hζ (m + k)).trans_eq ?_
    dsimp only [a]
    rw [abs_of_nonneg hr₀]
    simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  dsimp only
  change ‖pairedLogTail r θ ζ k‖ ≤ (2 / ζ.re) * (∑' m, a m) ∧ _
  constructor
  · rw [← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm h).trans (h.tsum_le_tsum hm (ha.mul_left _))
  · have hs := mul_le_mul_of_nonneg_left (ha.tsum_le_tsum hb hg)
      (by positivity : 0 ≤ 2 / ζ.re)
    refine hs.trans_eq ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr₁]
    dsimp only [C]
    simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

theorem norm_pairedLogTail_le {r : ℝ} (θ : ℝ) {ζ : ℂ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hζ : 0 < ζ.re) (k : ℕ) :
    ‖pairedLogTail r θ ζ k‖ ≤ 2 * r ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 2 * ζ.re * (1 - r)) :=
  (norm_pairedLogTail_series_bounds θ hr₀ hr₁ hζ k).1.trans
    (norm_pairedLogTail_series_bounds θ hr₀ hr₁ hζ k).2

theorem pairedLog_split (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) (k : ℕ) :
    pairedLog r θ ζ = (∑ j ∈ Finset.range k, pairedLogMode r θ ζ j) + pairedLogTail r θ ζ k := by
  rw [pairedLog_eq_tsum_mode r θ hr hζ]
  exact ((summable_norm_pairedLogMode r θ hr hζ).of_norm.sum_add_tsum_nat_add k).symm

theorem pairedLogMode_zero (r θ : ℝ) (ζ : ℂ) :
    pairedLogMode r θ ζ 0 = 2 * I * (r : ℂ) * (Real.cos θ : ℂ) / (2 * sinh (ζ / 2)) := by
  simp only [pairedLogMode, pairedLogCoeff, zero_add, Nat.cast_one, pow_one, one_mul]
  ring

theorem pairedLogMode_one (r θ : ℝ) (ζ : ℂ) :
    pairedLogMode r θ ζ 1 = (r : ℂ) ^ 2 * (Real.cos (2 * θ) : ℂ) / (2 * sinh ζ) := by
  norm_num only [pairedLogMode, pairedLogCoeff, Nat.reduceAdd, Nat.cast_ofNat]
  rw [show (2 : ℂ) * ζ / 2 = ζ by ring, mul_pow, Complex.I_sq, neg_sq]
  rw [show -(2 : ℂ) * ((r : ℂ) ^ 2 * -1) = 2 * (r : ℂ) ^ 2 by ring,
    mul_div_mul_left _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  ring

private theorem norm_inv_sub_inv_le_of_norm_sub_le {a b : ℂ} {K : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : ‖a - b‖ ≤ K) :
    ‖a⁻¹ - b⁻¹‖ ≤ K / (‖a‖ * ‖b‖) := by
  rw [show a⁻¹ - b⁻¹ = -(a - b) / (a * b) by field_simp; ring,
    norm_div, norm_neg, norm_mul]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem norm_sinh_half_inv_sub_inv_le {ζ : ℂ} (hζ : 0 < ζ.re)
    (him : |ζ.im| ≤ Real.pi) (hsq : ‖ζ‖ ^ 2 < 10) :
    ‖(2 * sinh (ζ / 2))⁻¹ - ζ⁻¹‖ ≤ 0.08 * ‖ζ‖ := by
  have hz : 0 < ‖ζ‖ := by
    apply norm_pos_iff.mpr
    intro h
    simp [h] at hζ
  have hl := norm_two_sinh_half_ge hζ.le him
  have ha : 0 < ‖2 * sinh (ζ / 2)‖ := (by positivity : 0 < 2 * ‖ζ‖ / Real.pi).trans_le hl
  have hu := norm_two_sinh_half_sub_self_le (z := ζ) (by linarith)
  have hDen : 0 < 24 * (1 - ‖ζ‖ ^ 2 / 80) := by linarith
  have hsmall : 0 ≤ 10 - ‖ζ‖ ^ 2 := by linarith
  have hcub : 0 ≤ ‖ζ‖ ^ 3 := by positivity
  have hu' : ‖2 * sinh (ζ / 2) - ζ‖ ≤ 0.05 * ‖ζ‖ ^ 3 := hu.trans
    ((div_le_iff₀ hDen).2 (by nlinarith only [hcub, mul_nonneg hsmall hcub]))
  refine (norm_inv_sub_inv_le_of_norm_sub_le (norm_pos_iff.mp ha) (norm_pos_iff.mp hz) hu').trans ?_
  refine (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right hl hz.le)).trans ?_
  have hπ := Real.pi_lt_d2
  rw [show 0.05 * ‖ζ‖ ^ 3 / (2 * ‖ζ‖ / Real.pi * ‖ζ‖) = (0.025 * Real.pi) * ‖ζ‖ by
    field_simp [ne_of_gt hz, Real.pi_ne_zero]; ring]
  exact mul_le_mul_of_nonneg_right (by linarith) hz.le

theorem norm_sinh_inv_sub_inv_lt {ζ : ℂ} (hζ : 0 < ζ.re) (hs : ‖ζ‖ ≤ 0.104) :
    ‖(2 * sinh ζ)⁻¹ - (2 * ζ)⁻¹‖ < 0.084 * ‖ζ‖ := by
  have hz : 0 < ‖ζ‖ := by
    apply norm_pos_iff.mpr
    intro h
    simp [h] at hζ
  have hsq : ‖ζ‖ ^ 2 ≤ 0.104 ^ 2 := pow_le_pow_left₀ hz.le hs 2
  have hu := norm_sinh_sub_self_le (z := ζ) (by linarith)
  have hDen : 0 < 6 * (1 - ‖ζ‖ ^ 2 / 20) := by linarith
  have hcub : 0 ≤ ‖ζ‖ ^ 3 := by positivity
  have hu' : ‖sinh ζ - ζ‖ ≤ 0.167 * ‖ζ‖ ^ 3 := hu.trans
    ((div_le_iff₀ hDen).2 (by nlinarith only [hcub, mul_nonneg (sub_nonneg.mpr hsq) hcub]))
  have hdiff : ‖sinh ζ - ζ‖ ≤ 0.002 * ‖ζ‖ := hu'.trans (by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hz.le])
  have hl : 0.998 * ‖ζ‖ ≤ ‖sinh ζ‖ := by
    have h := norm_sub_norm_le ζ (sinh ζ)
    rw [norm_sub_rev] at h
    linarith
  have ha : 0 < ‖sinh ζ‖ := (by positivity : 0 < 0.998 * ‖ζ‖).trans_le hl
  rw [mul_inv_rev, mul_inv_rev, ← sub_mul, norm_mul, norm_inv, Complex.norm_ofNat]
  refine (mul_le_mul_of_nonneg_right (norm_inv_sub_inv_le_of_norm_sub_le
    (norm_pos_iff.mp ha) (norm_pos_iff.mp hz) hu') (by positivity)).trans_lt ?_
  have hden : 0 < 0.998 * ‖ζ‖ * ‖ζ‖ := by positivity
  refine (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hden
    (mul_le_mul_of_nonneg_right hl hz.le)) (by positivity)).trans_lt ?_
  rw [show 0.167 * ‖ζ‖ ^ 3 / (0.998 * ‖ζ‖ * ‖ζ‖) * 2⁻¹ = (0.167 / (2 * 0.998)) * ‖ζ‖ by
    field_simp [ne_of_gt hz]]
  exact mul_lt_mul_of_pos_right (by norm_num) hz

theorem norm_sinh_inv_sub_inv_le {ζ : ℂ} (hζ : 0 < ζ.re) (hs : ‖ζ‖ ≤ 0.104) :
    ‖(2 * sinh ζ)⁻¹ - (2 * ζ)⁻¹‖ ≤ 0.084 * ‖ζ‖ :=
  (norm_sinh_inv_sub_inv_lt hζ hs).le

/-- The first logarithmic remainder in (19), including its angular weight. -/
theorem norm_pairedLogMode_zero_sub_main_le {r : ℝ} (θ : ℝ) {ζ : ℂ}
    (hr : 0 ≤ r) (hζ : 0 < ζ.re) (him : |ζ.im| ≤ Real.pi) (hsq : ‖ζ‖ ^ 2 < 10) :
    ‖pairedLogMode r θ ζ 0 - nearOriginMainLog r θ ζ‖ ≤ 0.16 * r * ‖ζ‖ * |Real.cos θ| := by
  rw [pairedLogMode_zero, nearOriginMainLog, div_eq_mul_inv _ (2 * sinh (ζ / 2)), div_eq_mul_inv _ ζ, ← mul_sub,
    norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, Complex.norm_real, Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_left (norm_sinh_half_inv_sub_inv_le hζ him hsq) (by positivity)).trans_eq ?_
  ring

theorem norm_pairedLogMode_one_sub_correction_le (r θ : ℝ) {ζ : ℂ}
    (hζ : 0 < ζ.re) (hs : ‖ζ‖ ≤ 0.104) :
    ‖pairedLogMode r θ ζ 1 - nearOriginCorrection r θ ζ‖ ≤ 0.084 * r ^ 2 * ‖ζ‖ := by
  rw [pairedLogMode_one, nearOriginCorrection, div_eq_mul_inv _ (2 * sinh ζ), div_eq_mul_inv _ (2 * ζ), ← mul_sub,
    norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Complex.norm_real, Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (sq_nonneg r)
    (Real.abs_cos_le_one _)) (norm_nonneg _)).trans ?_
  refine (mul_le_mul_of_nonneg_left (norm_sinh_inv_sub_inv_le hζ hs) (sq_nonneg r)).trans_eq ?_
  ring

theorem norm_pairedLogTail_one_le {r : ℝ} (θ : ℝ) {ζ : ℂ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1 / 40) (hζ : 0 < ζ.re) :
    ‖pairedLogTail r θ ζ 1‖ ≤ 0.513 * (r ^ 2 / ζ.re) := by
  refine (norm_pairedLogTail_le θ hr₀ (by linarith) hζ 1).trans ?_
  change 2 * r ^ 2 / (2 ^ 2 * ζ.re * (1 - r)) ≤ 0.513 * (r ^ 2 / ζ.re)
  have hs : 0 < 1 - r := by linarith
  rw [show (0.513 : ℝ) * (r ^ 2 / ζ.re) = r ^ 2 * (0.513 / ζ.re) by ring]
  rw [show 2 * r ^ 2 / (2 ^ 2 * ζ.re * (1 - r)) = r ^ 2 * (1 / (2 * ζ.re * (1 - r))) by
    field_simp [hζ.ne', hs.ne']]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
  have hden : 0 < 2 * ζ.re * (1 - r) := by positivity
  apply (div_le_iff₀ hden).2
  rw [show (0.513 / ζ.re : ℝ) * (2 * ζ.re * (1 - r)) =
      1.026 * (1 - r) by field_simp [hζ.ne']; ring]
  linarith

theorem pairedLogTail_one_geometric_lt {r u : ℝ} (hr₀ : 0 < r)
    (hr₁ : r ≤ 1 / 40) (hu : 0 < u) :
    r ^ 2 / (2 * u * (1 - r)) < 0.513 * (r ^ 2 / u) := by
  have hs : 0 < 1 - r := by linarith
  rw [show (0.513 : ℝ) * (r ^ 2 / u) = r ^ 2 * (0.513 / u) by ring,
    show r ^ 2 / (2 * u * (1 - r)) = r ^ 2 * (1 / (2 * u * (1 - r))) by ring]
  apply mul_lt_mul_of_pos_left _ (sq_pos_of_pos hr₀)
  apply (div_lt_iff₀ (by positivity)).2
  rw [show (0.513 / u : ℝ) * (2 * u * (1 - r)) =
      1.026 * (1 - r) by field_simp [hu.ne']; ring]
  linarith

private theorem norm_sq_expand (ζ : ℂ) : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem norm_le_for_nearOrigin_strip {ζ : ℂ} (hζ : 0 ≤ ζ.re) (hu : ζ.re ≤ 1 / 40)
    (hv : |ζ.im| ≤ Real.pi) : ‖ζ‖ ≤ 3.142 := by
  have hre := pow_le_pow_left₀ hζ hu 2
  have him := pow_le_pow_left₀ (abs_nonneg ζ.im) (hv.trans Real.pi_lt_d6.le) 2
  rw [sq_abs] at him
  have he := norm_sq_expand ζ
  nlinarith [norm_nonneg ζ]

theorem norm_le_for_nearOrigin_center {ζ : ℂ} (hζ : 0 ≤ ζ.re)
    (hv : |ζ.im| ≤ 4 * ζ.re) : ‖ζ‖ ≤ 4.124 * ζ.re := by
  have him := pow_le_pow_left₀ (abs_nonneg ζ.im) hv 2
  rw [sq_abs] at him
  have he := norm_sq_expand ζ
  apply (sq_le_sq₀ (norm_nonneg ζ) (by positivity)).mp
  nlinarith [sq_nonneg ζ.re]

/-- The uniform bound on the full first logarithmic remainder in (19). -/
theorem norm_pairedLog_sub_main_lt {r : ℝ} (θ : ℝ) {ζ : ℂ}
    (hζ : 0 < ζ.re) (hu : ζ.re ≤ r) (hr : r ≤ 1 / 40) (hv : |ζ.im| ≤ Real.pi) :
    ‖pairedLog r θ ζ - nearOriginMainLog r θ ζ‖ < 1.02 * (r ^ 2 / ζ.re) := by
  have hrPos := hζ.trans_le hu
  have hr₀ := hrPos.le
  have ha : |r| ≤ 1 := by rw [abs_of_nonneg hr₀]; linarith
  have hn := norm_le_for_nearOrigin_strip hζ.le (hu.trans hr) hv
  have hsq : ‖ζ‖ ^ 2 < 10 :=
    (pow_le_pow_left₀ (norm_nonneg ζ) hn 2).trans_lt (by norm_num)
  have h0 := norm_pairedLogMode_zero_sub_main_le θ hr₀ hζ hv hsq
  have h1 := norm_pairedLogTail_one_le θ hr₀ hr hζ
  rw [pairedLog_split r θ ha hζ 1, Finset.sum_range_one, add_sub_right_comm]
  refine (norm_add_le _ _).trans_lt (add_le_add h0 h1 |>.trans_lt ?_)
  have hnr : r ≤ r ^ 2 / ζ.re := (le_div_iff₀ hζ).2
    (by simpa only [pow_two] using mul_le_mul_of_nonneg_left hu hr₀)
  have hθ := Real.abs_cos_le_one θ
  have hb : 0.16 * r * ‖ζ‖ * |Real.cos θ| ≤ (0.16 * 3.142) * (r ^ 2 / ζ.re) := by
    calc
      _ ≤ 0.16 * r * ‖ζ‖ := mul_le_of_le_one_right (by positivity) hθ
      _ ≤ 0.16 * r * 3.142 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = (0.16 * 3.142) * r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnr (by norm_num)
  linarith only [hb, show 0 < r ^ 2 / ζ.re by positivity]

theorem norm_pairedLog_sub_main_le {r : ℝ} (θ : ℝ) {ζ : ℂ}
    (hζ : 0 < ζ.re) (hu : ζ.re ≤ r) (hr : r ≤ 1 / 40) (hv : |ζ.im| ≤ Real.pi) :
    ‖pairedLog r θ ζ - nearOriginMainLog r θ ζ‖ ≤ 1.02 * (r ^ 2 / ζ.re) :=
  (norm_pairedLog_sub_main_lt θ hζ hu hr hv).le

theorem norm_pairedLogTail_two_le {r : ℝ} (θ : ℝ) {ζ : ℂ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1 / 40) (hζ : 0 < ζ.re) :
    ‖pairedLogTail r θ ζ 2‖ ≤ 0.228 * r * (r ^ 2 / ζ.re) := by
  refine (norm_pairedLogTail_le θ hr₀ (by linarith) hζ 2).trans ?_
  change 2 * r ^ 3 / (3 ^ 2 * ζ.re * (1 - r)) ≤ 0.228 * r * (r ^ 2 / ζ.re)
  have hs : 0 < 1 - r := by linarith
  rw [show 2 * r ^ 3 / (3 ^ 2 * ζ.re * (1 - r)) =
      (r ^ 3 / ζ.re) * (2 / (9 * (1 - r))) by field_simp [hζ.ne', hs.ne']; ring,
    show 0.228 * r * (r ^ 2 / ζ.re) = (r ^ 3 / ζ.re) * 0.228 by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (div_le_iff₀ (by positivity)).2 (by linarith)

theorem norm_nearOriginCorrection_le (r θ : ℝ) {ζ : ℂ} (hζ : 0 < ζ.re) :
    ‖nearOriginCorrection r θ ζ‖ ≤ (r ^ 2 / ζ.re) / 2 := by
  have hnorm := Complex.abs_re_le_norm ζ
  rw [abs_of_pos hζ] at hnorm
  rw [nearOriginCorrection, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
  have h := div_le_div₀ (by positivity)
    (mul_le_of_le_one_right (sq_nonneg r) (Real.abs_cos_le_one (2 * θ)))
    (by positivity : 0 < 2 * ζ.re) (mul_le_mul_of_nonneg_left hnorm (by norm_num : 0 ≤ (2 : ℝ)))
  refine h.trans_eq ?_
  ring

/-- The refined logarithmic remainder on the inner interval, in the variables `r` and `u`. -/
theorem norm_pairedLog_sub_main_sub_correction_le {r : ℝ} (θ : ℝ) {ζ : ℂ}
    (hζ : 0 < ζ.re) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1 / 40) (hu : ζ.re ≤ 1 / 40)
    (hv : |ζ.im| ≤ 4 * ζ.re) :
    ‖pairedLog r θ ζ - nearOriginMainLog r θ ζ - nearOriginCorrection r θ ζ‖ ≤
      0.66 * r * ζ.re + 0.228 * r * (r ^ 2 / ζ.re) + 0.35 * r ^ 2 * ζ.re := by
  have ha : |r| ≤ 1 := by rw [abs_of_nonneg hr₀]; linarith
  have hn := norm_le_for_nearOrigin_center hζ.le hv
  have hn' : ‖ζ‖ ≤ 0.104 := by linarith
  have hπ : |ζ.im| ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hsq : ‖ζ‖ ^ 2 < 10 :=
    (pow_le_pow_left₀ (norm_nonneg ζ) hn' 2).trans_lt (by norm_num)
  have h0 := norm_pairedLogMode_zero_sub_main_le θ hr₀ hζ hπ hsq
  have h1 := norm_pairedLogMode_one_sub_correction_le r θ hζ hn'
  have h2 := norm_pairedLogTail_two_le θ hr₀ hr₁ hζ
  have h0' : ‖pairedLogMode r θ ζ 0 - nearOriginMainLog r θ ζ‖ ≤ 0.66 * r * ζ.re := by
    refine h0.trans ((mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one θ)).trans ?_)
    refine (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 0.16 * r)).trans ?_
    nlinarith [mul_nonneg hr₀ hζ.le]
  have h1' : ‖pairedLogMode r θ ζ 1 - nearOriginCorrection r θ ζ‖ ≤ 0.35 * r ^ 2 * ζ.re := by
    refine h1.trans ((mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 0.084 * r ^ 2)).trans ?_)
    nlinarith [mul_nonneg (sq_nonneg r) hζ.le]
  rw [pairedLog_split r θ ha hζ 2, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show pairedLogMode r θ ζ 0 + pairedLogMode r θ ζ 1 + pairedLogTail r θ ζ 2 -
      nearOriginMainLog r θ ζ - nearOriginCorrection r θ ζ =
      (pairedLogMode r θ ζ 0 - nearOriginMainLog r θ ζ) +
      (pairedLogMode r θ ζ 1 - nearOriginCorrection r θ ζ) + pairedLogTail r θ ζ 2 by ring]
  refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add h0' h1')) h2).trans_eq ?_)
  ring

theorem nearOrigin_pointwise_exp_remainder {L L₀ S : ℂ} {Δ ε : ℝ}
    (hS : ‖S‖ ≤ Δ / 2) (hε : ‖L - L₀ - S‖ ≤ ε) :
    ‖exp L - exp L₀ * (1 + S)‖ ≤ Real.exp L₀.re *
      (ε * Real.exp (Δ / 2 + ε) + Δ ^ 2 / 8 * Real.exp (Δ / 2)) := by
  let R := L - L₀ - S
  have hL : L = L₀ + S + R := by dsimp only [R]; ring
  have hsp : 0 ≤ Δ / 2 := (norm_nonneg S).trans hS
  have hep : 0 ≤ ε := (norm_nonneg R).trans hε
  have hmax (z : ℂ) {c : ℝ} (hz : ‖z‖ ≤ c) : max 0 z.re ≤ c :=
    max_le ((norm_nonneg z).trans hz) ((Complex.re_le_norm z).trans hz)
  have hSB := Real.exp_le_exp.mpr (hmax S hS)
  have hRB := Real.exp_le_exp.mpr (hmax R hε)
  have hRR : ‖exp R - 1‖ ≤ ε * Real.exp ε :=
    (norm_exp_sub_one_le R).trans
      (mul_le_mul hε hRB (Real.exp_nonneg _) hep)
  have hSS : ‖exp S - 1 - S‖ ≤ Δ ^ 2 / 8 * Real.exp (Δ / 2) := by
    refine (norm_exp_sub_one_sub_le S).trans (mul_le_mul ?_ hSB (Real.exp_nonneg _) (by positivity))
    have h := pow_le_pow_left₀ (norm_nonneg S) hS 2
    linarith
  have heq : exp L - exp L₀ * (1 + S) =
      exp L₀ * (exp S * (exp R - 1) + (exp S - 1 - S)) := by
    nth_rw 1 [hL]
    rw [exp_add, exp_add]
    ring
  rw [heq, norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  refine (norm_add_le _ _).trans (add_le_add ?_ hSS)
  rw [norm_mul, Complex.norm_exp]
  refine (mul_le_mul (Real.exp_le_exp.mpr ((Complex.re_le_norm S).trans hS)) hRR
    (norm_nonneg _) (Real.exp_nonneg _)).trans_eq ?_
  rw [Real.exp_add]
  ring

end DurfeeCCS.Step08
