module

public import DurfeeCCS.Step08.NearOriginArcBasics

/-! Squared angular and vertical means of the two logarithmic remainders. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex Set MeasureTheory

def nearOriginFirstRemainder (r θ : ℝ) (ζ : ℂ) : ℂ :=
  pairedLogMode r θ ζ 0 - nearOriginMainLog r θ ζ

def nearOriginTailRemainder (r θ : ℝ) (ζ : ℂ) : ℂ :=
  pairedLogTail r θ ζ 1

theorem pairedLog_sub_main_eq_remainders (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    pairedLog r θ ζ - nearOriginMainLog r θ ζ =
      nearOriginFirstRemainder r θ ζ + nearOriginTailRemainder r θ ζ := by
  rw [nearOriginFirstRemainder, nearOriginTailRemainder, pairedLog_split r θ hr hζ 1,
    Finset.sum_range_one, add_sub_right_comm]

theorem continuous_nearOriginFirstRemainder (r : ℝ) {u : ℝ} (hu : 0 < u) :
    Continuous (fun p : ℝ × ℝ => nearOriginFirstRemainder r p.2 (verticalPoint u p.1)) := by
  unfold nearOriginFirstRemainder pairedLogMode
  exact (((continuous_pairedLogCoeff_vertical r hu 0).comp continuous_fst).mul
    (by fun_prop : Continuous (fun p : ℝ × ℝ => (Real.cos (((0 + 1 : ℕ) : ℝ) * p.2) : ℂ)))).sub
    (continuous_nearOriginMainLog r hu)

theorem continuous_nearOriginTailRemainder (r : ℝ) (hr : |r| ≤ 1) {u : ℝ} (hu : 0 < u) :
    Continuous (fun p : ℝ × ℝ => nearOriginTailRemainder r p.2 (verticalPoint u p.1)) := by
  have h (p : ℝ × ℝ) : nearOriginTailRemainder r p.2 (verticalPoint u p.1) =
      pairedLog r p.2 (verticalPoint u p.1) - pairedLogMode r p.2 (verticalPoint u p.1) 0 := by
    rw [nearOriginTailRemainder, pairedLog_split r p.2 hr (by simpa only [verticalPoint_re] using hu) 1,
      Finset.sum_range_one]
    ring
  simp_rw [h]
  exact (continuous_pairedLog_vertical r hr hu).sub
    (((continuous_pairedLogCoeff_vertical r hu 0).comp continuous_fst).mul
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (Real.cos (((0 + 1 : ℕ) : ℝ) * p.2) : ℂ))))

private theorem norm_nearOriginMainLog_vertical (r θ u v : ℝ) :
    ‖nearOriginMainLog r θ (verticalPoint u v)‖ =
      2 * |r| * |Real.cos θ| / ‖verticalPoint u v‖ := by
  rw [nearOriginMainLog, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs]

theorem norm_nearOriginMainLog_mul_first_le {r u v : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hu' : u ≤ 1 / 40) (hv : |v| ≤ Real.pi) (θ : ℝ) :
    ‖nearOriginMainLog r θ (verticalPoint u v) * nearOriginFirstRemainder r θ (verticalPoint u v)‖ ≤
      0.32 * r ^ 2 * (Real.cos θ) ^ 2 := by
  have hζ : 0 < (verticalPoint u v).re := by simpa only [verticalPoint_re] using hu
  have hζn := norm_le_for_nearOrigin_strip hζ.le (by simpa only [verticalPoint_re] using hu')
    (by simpa only [verticalPoint_im] using hv)
  have hζsq : ‖verticalPoint u v‖ ^ 2 < 10 :=
    (pow_le_pow_left₀ (norm_nonneg _) hζn 2).trans_lt (by norm_num)
  have h := norm_pairedLogMode_zero_sub_main_le θ hr hζ (by simpa only [verticalPoint_im] using hv) hζsq
  rw [norm_mul, norm_nearOriginMainLog_vertical, abs_of_nonneg hr, nearOriginFirstRemainder]
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
  have hnz : ‖verticalPoint u v‖ ≠ 0 := norm_ne_zero_iff.mpr (verticalPoint_ne_zero hu v)
  field_simp [hnz]
  rw [sq_abs]
  ring

private theorem angularMean_sq_id : angularMean (fun v : ℝ => v ^ 2) = Real.pi ^ 2 / 3 := by
  unfold angularMean
  rw [integral_pow]
  norm_num [Real.pi_ne_zero]
  field_simp [Real.pi_ne_zero]
  ring

theorem angularMean_const_real (c : ℝ) : angularMean (fun _ => c) = c := by
  unfold angularMean
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add, ← two_mul,
    ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]

private theorem angularMean_add_real {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    angularMean (fun t => f t + g t) = angularMean f + angularMean g := by
  simp only [angularMean, intervalIntegral.integral_add (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), mul_add]

private theorem angularMean_mono {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ v ∈ Icc (-Real.pi) Real.pi, f v ≤ g v) : angularMean f ≤ angularMean g :=
  angularMean_mono_on hf hg h

private theorem continuous_angularMean {F : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry F)) : Continuous (fun v => angularMean (F v)) := by
  unfold angularMean
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf _ _).const_mul _

theorem angularMean_abs_main_mul_first_le {r u v : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hu' : u ≤ 1 / 40) (hv : |v| ≤ Real.pi) :
    angularMean (fun θ => ‖nearOriginMainLog r θ (verticalPoint u v) *
      nearOriginFirstRemainder r θ (verticalPoint u v)‖) ≤ 0.16 * r ^ 2 := by
  have hp : Continuous (fun θ : ℝ => (v, θ)) := continuous_const.prodMk continuous_id
  have hF := (((continuous_nearOriginMainLog r hu).mul (continuous_nearOriginFirstRemainder r hu)).norm).comp hp
  have hG : Continuous (fun θ : ℝ => (0.32 * r ^ 2) * (Real.cos θ) ^ 2) := by fun_prop
  refine (angularMean_mono hF hG (fun θ _ => norm_nearOriginMainLog_mul_first_le hr hu hu' hv θ)).trans_eq ?_
  rw [angularMean_const_mul, show (fun θ : ℝ => Real.cos θ ^ 2) =
    (fun θ : ℝ => Real.cos (((0 + 1 : ℕ) : ℝ) * θ) ^ 2) by simp only [zero_add, Nat.cast_one, one_mul],
    angularMean_sq_cosine]
  ring

theorem angularMean_sq_first_remainder_le {r u v : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hu' : u ≤ 1 / 40) (hv : |v| ≤ Real.pi) :
    angularMean (fun θ => ‖nearOriginFirstRemainder r θ (verticalPoint u v)‖ ^ 2) ≤
      0.16 ^ 2 * r ^ 2 * (u ^ 2 + v ^ 2) / 2 := by
  have hζ : 0 < (verticalPoint u v).re := by simpa only [verticalPoint_re] using hu
  have hζn := norm_le_for_nearOrigin_strip hζ.le (by simpa only [verticalPoint_re] using hu')
    (by simpa only [verticalPoint_im] using hv)
  have hζsq : ‖verticalPoint u v‖ ^ 2 < 10 :=
    (pow_le_pow_left₀ (norm_nonneg _) hζn 2).trans_lt (by norm_num)
  let C := (0.16 * r * ‖verticalPoint u v‖) ^ 2
  have hp : Continuous (fun θ : ℝ => (v, θ)) := continuous_const.prodMk continuous_id
  have hF := ((continuous_nearOriginFirstRemainder r hu).norm.pow 2).comp hp
  have hG : Continuous (fun θ : ℝ => C * (Real.cos θ) ^ 2) := by fun_prop
  refine (angularMean_mono hF hG (fun θ _ => ?_)).trans_eq ?_
  · have h := norm_pairedLogMode_zero_sub_main_le θ hr hζ (by simpa only [verticalPoint_im] using hv) hζsq
    have hp' := pow_le_pow_left₀ (norm_nonneg _) h 2
    dsimp only [C, nearOriginFirstRemainder]
    rwa [mul_pow, sq_abs] at hp'
  · rw [angularMean_const_mul, show (fun θ : ℝ => Real.cos θ ^ 2) =
      (fun θ : ℝ => Real.cos (((0 + 1 : ℕ) : ℝ) * θ) ^ 2) by simp only [zero_add, Nat.cast_one, one_mul],
      angularMean_sq_cosine]
    dsimp only [C]
    rw [mul_pow, norm_verticalPoint_sq]
    ring

private theorem double_angularMean_sq_first_remainder_le_sharp {r u : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hu' : u ≤ 1 / 40) :
    angularMean (fun v => angularMean (fun θ =>
      ‖nearOriginFirstRemainder r θ (verticalPoint u v)‖ ^ 2)) ≤ 0.2059 ^ 2 * r ^ 2 := by
  let C := 0.16 ^ 2 * r ^ 2 / 2
  have hF : Continuous (fun v => angularMean (fun θ =>
      ‖nearOriginFirstRemainder r θ (verticalPoint u v)‖ ^ 2)) :=
    continuous_angularMean ((continuous_nearOriginFirstRemainder r hu).norm.pow 2)
  have hG : Continuous (fun v : ℝ => C * (u ^ 2 + v ^ 2)) := by fun_prop
  refine (angularMean_mono hF hG (fun v hv => ?_)).trans ?_
  · refine (angularMean_sq_first_remainder_le hr hu hu' (abs_le.mpr hv)).trans_eq ?_
    dsimp only [C]
    ring
  · have hsq : Continuous (fun v : ℝ => v ^ 2) := continuous_id.pow 2
    rw [angularMean_const_mul, angularMean_add_real (continuous_const (y := u ^ 2)) hsq,
      angularMean_sq_id, angularMean_const_real]
    have hU := pow_le_pow_left₀ hu.le hu' 2
    have hP := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
    have hi : (0.16 : ℝ) ^ 2 / 2 * (u ^ 2 + Real.pi ^ 2 / 3) ≤ 0.2059 ^ 2 := by linarith
    have h := mul_le_mul_of_nonneg_right hi (sq_nonneg r)
    dsimp only [C]
    convert h using 1
    ring

theorem double_angularMean_sq_first_remainder_le {r u : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (hu' : u ≤ 1 / 40) :
    angularMean (fun v => angularMean (fun θ =>
      ‖nearOriginFirstRemainder r θ (verticalPoint u v)‖ ^ 2)) ≤ 0.206 ^ 2 * r ^ 2 :=
  (double_angularMean_sq_first_remainder_le_sharp hr hu hu').trans
    (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg r))

theorem double_angularMean_sq_first_remainder_lt {r u : ℝ}
    (hr : 0 < r) (hu : 0 < u) (hu' : u ≤ 1 / 40) :
    angularMean (fun v => angularMean (fun θ =>
      ‖nearOriginFirstRemainder r θ (verticalPoint u v)‖ ^ 2)) < 0.206 ^ 2 * r ^ 2 :=
  (double_angularMean_sq_first_remainder_le_sharp hr.le hu hu').trans_lt
    (mul_lt_mul_of_pos_right (by norm_num) (sq_pos_of_pos hr))

theorem double_angularMean_nearOriginMainLog_sq_le {r u : ℝ} (hu : 0 < u) :
    angularMean (fun v => angularMean (fun θ =>
      ‖nearOriginMainLog r θ (verticalPoint u v)‖ ^ 2)) ≤ r ^ 2 / u := by
  simp_rw [angularMean_nearOriginMainLog_sq, div_eq_mul_inv]
  rw [angularMean_const_mul, angularMean]
  have hi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hInt := integrable_cauchy_density hu
  rw [intervalIntegral.integral_of_le hi]
  have h := setIntegral_le_integral (s := Ioc (-Real.pi) Real.pi) hInt (ae_of_all _ fun v => by positivity :
    0 ≤ᵐ[volume] fun v : ℝ => (u ^ 2 + v ^ 2)⁻¹)
  rw [integral_cauchy_density hu] at h
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity)).trans_eq ?_
  field_simp [hu.ne', Real.pi_ne_zero]

private theorem angularMean_sq_tail_remainder (r : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (hζ : 0 < ζ.re) :
    angularMean (fun θ => ‖nearOriginTailRemainder r θ ζ‖ ^ 2) =
      (1 / 2) * ∑' m : ℕ, ‖pairedLogCoeff r ζ (m + 1)‖ ^ 2 := by
  let a (n : ℕ) : ℂ := if n = 0 then 0 else pairedLogCoeff r ζ n
  have ha : Summable (fun n => ‖a n‖) := by
    refine (summable_norm_pairedLogCoeff r hr hζ).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    by_cases h : n = 0 <;> simp [a,h]
  have ha' (m : ℕ) : a (m + 1) = pairedLogCoeff r ζ (m + 1) := by simp [a]
  have hfirst : a 0 = 0 := by simp [a]
  have hp (θ : ℝ) :
      (∑' n : ℕ, a n * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ)) = nearOriginTailRemainder r θ ζ := by
    have hs : Summable (fun n : ℕ => a n * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ)) := by
      apply Summable.of_norm
      refine ha.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
    rw [← hs.sum_add_tsum_nat_add 1, Finset.sum_range_one, hfirst, zero_mul, zero_add]
    simp only [nearOriginTailRemainder, pairedLogTail, pairedLogMode, ha']
  have hs : Summable (fun n : ℕ => ‖a n‖ ^ 2) := by
    apply (ha.mul_left (∑' n, ‖a n‖)).of_nonneg_of_le (fun n => sq_nonneg _)
    intro n
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (ha.le_tsum n (fun k _ => norm_nonneg _)) (norm_nonneg _)
  have hsum : (∑' n : ℕ, ‖a n‖ ^ 2) = ∑' n : ℕ, ‖pairedLogCoeff r ζ (n + 1)‖ ^ 2 := by
    rw [← hs.sum_add_tsum_nat_add 1, Finset.sum_range_one, hfirst, norm_zero, zero_pow (by decide),
      zero_add]
    simp_rw [ha']
  simpa only [hp, hsum] using angularMean_norm_sq_cosineSeries a ha

theorem double_angularMean_sq_tail_remainder (r : ℝ) (hr : |r| ≤ 1) {u : ℝ} (hu : 0 < u) :
    angularMean (fun v => angularMean (fun θ => ‖nearOriginTailRemainder r θ (verticalPoint u v)‖ ^ 2)) =
      ∑' m : ℕ, r ^ (2 * (m + 2)) /
        ((((m + 2 : ℕ) : ℝ) ^ 2) * Real.sinh (((m + 2 : ℕ) : ℝ) * u)) := by
  have hv (v : ℝ) : 0 < (verticalPoint u v).re := by simpa only [verticalPoint_re] using hu
  simp_rw [angularMean_sq_tail_remainder r hr (hv _)]
  rw [angularMean_const_mul]
  have hs := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) 2).2
    hasSum_zeta_four.summable
  have hb : Summable (fun m : ℕ => (4 / u ^ 2) / (((m + 2 : ℕ) : ℝ) ^ 4)) := by
    simpa only [mul_one_div] using hs.mul_left (4 / u ^ 2)
  rw [angularMean_tsum_uniform (F := fun m v => ‖pairedLogCoeff r (verticalPoint u v) (m + 1)‖ ^ 2)
    (fun m => (continuous_pairedLogCoeff_vertical r hu (m + 1)).norm.pow 2) hb]
  · simp_rw [integral_sq_pairedLogCoeff r hu, mul_div_assoc, tsum_mul_left]
    ring
  · intro m v
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := norm_pairedLogCoeff_le r hr (hv v) (m + 1)
    rw [verticalPoint_re] at h
    calc
      _ ≤ (2 / (u * (((m + 2 : ℕ) : ℝ) ^ 2))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := by field_simp; ring

private theorem double_angularMean_sq_tail_remainder_le_sharp {r u : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1 / 40) (hu : 0 < u) :
    angularMean (fun v => angularMean (fun θ => ‖nearOriginTailRemainder r θ (verticalPoint u v)‖ ^ 2))
      ≤ 0.3539 ^ 2 * (r ^ 4 / u) := by
  have hr : |r| ≤ 1 := by rw [abs_of_nonneg hr₀]; linarith
  rw [double_angularMean_sq_tail_remainder r hr hu]
  have hr2 : r ^ 2 ≤ (1 / 40 : ℝ) ^ 2 := pow_le_pow_left₀ hr₀ hr₁ 2
  have hR : r ^ 2 < 1 := by linarith
  let f (m : ℕ) : ℝ := r ^ (2 * (m + 2)) /
    ((((m + 2 : ℕ) : ℝ) ^ 2) * Real.sinh (((m + 2 : ℕ) : ℝ) * u))
  let C := r ^ 4 / (8 * u)
  have hg : Summable (fun m : ℕ => C * (r ^ 2) ^ m) :=
    (summable_geometric_of_lt_one (sq_nonneg _) hR).mul_left C
  have hf (m : ℕ) : 0 ≤ f m := by
    have hK : 0 ≤ ((m + 2 : ℕ) : ℝ) * u := by positivity
    have hs : 0 ≤ Real.sinh (((m + 2 : ℕ) : ℝ) * u) := hK.trans (Real.self_le_sinh_iff.mpr hK)
    unfold f
    positivity
  have hb (m : ℕ) : f m ≤ C * (r ^ 2) ^ m := by
    have hge : (2 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ m + 2)
    have hs : 2 * u ≤ Real.sinh (((m + 2 : ℕ) : ℝ) * u) :=
      (mul_le_mul_of_nonneg_right hge hu.le).trans (Real.self_le_sinh_iff.mpr (by positivity))
    have hs' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hge 2
    have hd := mul_le_mul hs' hs (by positivity) (by positivity : 0 ≤ ((m + 2 : ℕ) : ℝ) ^ 2)
    unfold f C
    calc
      _ ≤ r ^ (2 * (m + 2)) / (8 * u) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_num at hd ⊢; linarith)
      _ = _ := by rw [pow_mul, pow_add]; ring
  have hfs := hg.of_nonneg_of_le hf hb
  change (∑' m, f m) ≤ _
  refine (hfs.tsum_le_tsum hb hg).trans ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg _) hR]
  have hD : 0 < 8 * (1 - r ^ 2) := by linarith
  have hc : 1 / (8 * (1 - r ^ 2)) ≤ (0.3539 : ℝ) ^ 2 :=
    (div_le_iff₀ hD).2 (by linarith)
  dsimp only [C]
  calc
    _ = (r ^ 4 / u) * (1 / (8 * (1 - r ^ 2))) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ _ := by
      rw [mul_comm (0.3539 ^ 2)]
      exact mul_le_mul_of_nonneg_left hc (by positivity)

theorem double_angularMean_sq_tail_remainder_le {r u : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1 / 40) (hu : 0 < u) :
    angularMean (fun v => angularMean (fun θ => ‖nearOriginTailRemainder r θ (verticalPoint u v)‖ ^ 2))
      ≤ 0.354 ^ 2 * (r ^ 4 / u) :=
  (double_angularMean_sq_tail_remainder_le_sharp hr₀ hr₁ hu).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))

theorem double_angularMean_sq_tail_remainder_lt {r u : ℝ}
    (hr₀ : 0 < r) (hr₁ : r ≤ 1 / 40) (hu : 0 < u) :
    angularMean (fun v => angularMean (fun θ => ‖nearOriginTailRemainder r θ (verticalPoint u v)‖ ^ 2))
      < 0.354 ^ 2 * (r ^ 4 / u) :=
  (double_angularMean_sq_tail_remainder_le_sharp hr₀.le hr₁ hu).trans_lt
    (mul_lt_mul_of_pos_right (by norm_num) (by positivity))

end DurfeeCCS.Step08
