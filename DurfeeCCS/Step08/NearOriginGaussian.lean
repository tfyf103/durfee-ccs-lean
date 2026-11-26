module

public import DurfeeCCS.Step08.NearOriginErrors
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The inner Gaussian integral used to bound the first term of (18). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Set MeasureTheory intervalIntegral

private theorem two_mul_sq_div_pi_sq_le_one_sub_cos {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    2 * θ ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos θ := by
  have hs := Real.mul_abs_le_abs_sin (x := θ / 2) (by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  have hs' : |θ| / Real.pi ≤ |Real.sin (θ / 2)| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
    convert hs using 1
    ring
  have h := pow_le_pow_left₀ (by positivity) hs' 2
  rw [div_pow, sq_abs, sq_abs] at h
  have hc := Real.sin_sq_eq_half_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hc
  rw [mul_div_assoc]
  linarith

def nearOriginInnerWeight (σ η θ : ℝ) : ℝ :=
  Real.exp (σ * (2 * η * Real.cos θ / (1 + η ^ 2)))

def nearOriginInnerAverage (σ η : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi, nearOriginInnerWeight σ η θ

private theorem continuous_nearOriginInnerWeight (σ : ℝ) :
    Continuous (Function.uncurry (nearOriginInnerWeight σ)) := by
  unfold nearOriginInnerWeight Function.uncurry
  exact Real.continuous_exp.comp (continuous_const.mul
    ((continuous_const.mul continuous_fst |>.mul (Real.continuous_cos.comp continuous_snd)).div
      (continuous_const.add (continuous_fst.pow 2)) (fun x => by positivity : ∀ x : ℝ × ℝ, _)))

theorem continuous_nearOriginInnerAverage (σ : ℝ) :
    Continuous (nearOriginInnerAverage σ) := by
  unfold nearOriginInnerAverage
  exact (continuous_parametric_intervalIntegral_of_continuous'
    (continuous_nearOriginInnerWeight σ) _ _).const_mul _

private theorem nearOriginInnerAverage_neg (σ η : ℝ) :
    nearOriginInnerAverage σ (-η) = nearOriginInnerAverage σ η := by
  unfold nearOriginInnerAverage
  congr 1
  have h (θ : ℝ) : nearOriginInnerWeight σ (-η) θ =
      nearOriginInnerWeight σ η (θ + Real.pi) := by
    rw [nearOriginInnerWeight, nearOriginInnerWeight, Real.cos_add_pi, neg_sq]
    ring_nf
  simp_rw [h]
  rw [integral_comp_add_right]
  have hp : Function.Periodic (nearOriginInnerWeight σ η) (2 * Real.pi) := fun θ => by
    unfold nearOriginInnerWeight
    rw [Real.cos_add_two_pi]
  simpa only [neg_add_cancel, zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring,
    show -Real.pi + 2 * Real.pi = Real.pi by ring] using hp.intervalIntegral_add_eq 0 (-Real.pi)

private theorem Gaussian_exponent_domination {η θ : ℝ} (hη₁ : 1 / 2 ≤ η) (hη₂ : η ≤ 2)
    (hθ : |θ| ≤ Real.pi) :
    2 * η * Real.cos θ / (1 + η ^ 2) ≤
      1 - (η - 1) ^ 2 / 5 - 8 * θ ^ 2 / (5 * Real.pi ^ 2) := by
  let D := 1 + η ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hD₁ : D ≤ 5 := by
    dsimp [D]
    nlinarith [mul_nonneg (sub_nonneg.mpr hη₂) (show 0 ≤ 2 + η by linarith)]
  have hηD : 4 / 5 ≤ 2 * η / D := (le_div_iff₀ hD).2 (by
    dsimp [D]
    nlinarith [mul_nonneg (sub_nonneg.mpr hη₁) (sub_nonneg.mpr hη₂)])
  have ha : (η - 1) ^ 2 / 5 ≤ (η - 1) ^ 2 / D :=
    div_le_div_of_nonneg_left (sq_nonneg _) hD hD₁
  have hb : 8 * θ ^ 2 / (5 * Real.pi ^ 2) ≤
      (2 * η / D) * (1 - Real.cos θ) := by
    rw [show 8 * θ ^ 2 / (5 * Real.pi ^ 2) = (4 / 5) * (2 * θ ^ 2 / Real.pi ^ 2) by ring]
    exact mul_le_mul hηD (two_mul_sq_div_pi_sq_le_one_sub_cos hθ) (by positivity)
      (by positivity)
  have he : 1 - 2 * η * Real.cos θ / D =
      (η - 1) ^ 2 / D + (2 * η / D) * (1 - Real.cos θ) := by
    field_simp [hD.ne']; dsimp [D]; ring
  dsimp only [D] at ha hb he
  linarith

private theorem Gaussian_weight_domination {σ η θ : ℝ} (hσ : 0 ≤ σ) (hη₁ : 1 / 2 ≤ η)
    (hη₂ : η ≤ 2) (hθ : |θ| ≤ Real.pi) :
    nearOriginInnerWeight σ η θ ≤
      (Real.exp σ * Real.exp (-(σ / 5) * (η - 1) ^ 2)) *
        Real.exp (-(8 * σ / (5 * Real.pi ^ 2)) * θ ^ 2) := by
  rw [nearOriginInnerWeight, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (Gaussian_exponent_domination hη₁ hη₂ hθ) hσ
  convert h using 1
  ring

private theorem integral_gaussian_interval_le {b a c : ℝ} (hb : 0 < b) (hac : a ≤ c) :
    (∫ t in a..c, Real.exp (-b * t ^ 2)) ≤ √(Real.pi / b) := by
  rw [integral_of_le hac, ← integral_gaussian]
  exact setIntegral_le_integral (integrable_exp_neg_mul_sq hb) (ae_of_all _ fun _ => Real.exp_nonneg _)

private theorem nearOriginInnerAverage_le_gaussian {σ η : ℝ}
    (hσ : 0 < σ) (hη₁ : 1 / 2 ≤ η) (hη₂ : η ≤ 2) :
    nearOriginInnerAverage σ η ≤
      ((2 * Real.pi)⁻¹ * Real.exp σ * √(Real.pi / (8 * σ / (5 * Real.pi ^ 2)))) *
        Real.exp (-(σ / 5) * (η - 1) ^ 2) := by
  let C := Real.exp σ * Real.exp (-(σ / 5) * (η - 1) ^ 2)
  let b := 8 * σ / (5 * Real.pi ^ 2)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hc : Continuous (nearOriginInnerWeight σ η) :=
    (continuous_nearOriginInnerWeight σ).comp (continuous_const.prodMk continuous_id)
  have hg : Continuous (fun θ : ℝ => C * Real.exp (-b * θ ^ 2)) := by fun_prop
  unfold nearOriginInnerAverage
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi, C * Real.exp (-b * θ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono_on hπ (hc.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
      intro θ hθ
      exact Gaussian_weight_domination hσ.le hη₁ hη₂ (abs_le.mpr hθ)
    _ ≤ (2 * Real.pi)⁻¹ * (C * √(Real.pi / b)) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (integral_gaussian_interval_le hb hπ)
        (by dsimp only [C]; positivity)) (by positivity)
    _ = _ := by dsimp only [C, b]; ring

private theorem nearOriginInnerAverage_le_outer {σ η : ℝ}
    (hσ : 0 < σ) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 2 ∨ 2 ≤ η) :
    nearOriginInnerAverage σ η ≤ Real.exp (4 * σ / 5) := by
  have hd : 0 < 1 + η ^ 2 := by positivity
  have hq : 2 * η / (1 + η ^ 2) ≤ 4 / 5 := (div_le_iff₀ hd).2 (by
    rcases hη with hη | hη
    · nlinarith [mul_nonneg (sub_nonneg.mpr hη) (show 0 ≤ 2 - η by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ η - 1 / 2 by linarith) (sub_nonneg.mpr hη)])
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hc : Continuous (nearOriginInnerWeight σ η) :=
    (continuous_nearOriginInnerWeight σ).comp (continuous_const.prodMk continuous_id)
  unfold nearOriginInnerAverage
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ∫ _θ in -Real.pi..Real.pi, Real.exp (4 * σ / 5) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono_on hπ (hc.intervalIntegrable _ _) (intervalIntegrable_const)
      intro θ _
      rw [nearOriginInnerWeight]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left
        ((mul_le_of_le_one_right (show 0 ≤ 2 * η / (1 + η ^ 2) by positivity)
          (Real.cos_le_one θ)).trans hq) hσ.le
      convert h using 1 <;> ring
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]
                field_simp [Real.pi_ne_zero]; ring

private theorem nearOrigin_two_gaussians_le {σ : ℝ} (hσ : 0 < σ) :
    (2 * Real.pi)⁻¹ * √(Real.pi / (8 * σ / (5 * Real.pi ^ 2))) *
       √(Real.pi / (σ / 5)) ≤ 2.8 / σ := by
  have hπ := Real.pi_pos
  have hh := pow_le_pow_left₀ hπ.le Real.pi_lt_d2.le 2
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have he : ((2 * Real.pi)⁻¹) ^ 2 * (Real.pi / (8 * σ / (5 * Real.pi ^ 2))) *
      (Real.pi / (σ / 5)) = (25 * Real.pi ^ 2 / 32) / σ ^ 2 := by
    field_simp [hπ.ne', hσ.ne']; ring
  rw [he, div_pow]
  exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg σ)

private theorem nearOrigin_inner_positive_middle {σ : ℝ} (hσ : 0 < σ) :
    (∫ η in (1 / 2 : ℝ)..2, nearOriginInnerAverage σ η) ≤ 2.8 * Real.exp σ / σ := by
  let C := (2 * Real.pi)⁻¹ * Real.exp σ * √(Real.pi / (8 * σ / (5 * Real.pi ^ 2)))
  let g := fun η : ℝ => Real.exp (-(σ / 5) * η ^ 2)
  have hcg : Continuous (fun η : ℝ => C * g (η - 1)) := by unfold g; fun_prop
  calc
    _ ≤ ∫ η in (1 / 2 : ℝ)..2, C * g (η - 1) := by
      apply integral_mono_on (by norm_num) ((continuous_nearOriginInnerAverage σ).intervalIntegrable _ _)
        (hcg.intervalIntegrable _ _)
      intro η hη
      exact nearOriginInnerAverage_le_gaussian hσ hη.1 hη.2
    _ ≤ C * √(Real.pi / (σ / 5)) := by
      rw [intervalIntegral.integral_const_mul, integral_comp_sub_right]
      exact mul_le_mul_of_nonneg_left (integral_gaussian_interval_le (by positivity) (by norm_num))
        (by dsimp only [C]; positivity)
    _ ≤ _ := by
      dsimp only [C]
      convert mul_le_mul_of_nonneg_left (nearOrigin_two_gaussians_le hσ) (Real.exp_nonneg σ) using 1 <;> ring

private theorem nearOrigin_exp_loss {σ : ℝ} (hσ : 0 < σ) :
    5 * Real.exp (4 * σ / 5) ≤ 9.3 * Real.exp σ / σ := by
  have h := Real.add_one_le_exp (σ / 5 - 1)
  have h' : σ / 5 ≤ Real.exp (σ / 5 - 1) := by linarith
  have he : σ * Real.exp (-σ / 5) ≤ 5 * Real.exp (-1) := by
    have ht := mul_le_mul_of_nonneg_right h' (Real.exp_nonneg (-σ / 5))
    rw [← Real.exp_add, show σ / 5 - 1 + -σ / 5 = -1 by ring] at ht
    linarith
  have ht : 25 * Real.exp (-1) ≤ 9.3 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos 1)).2 (by linarith [Real.exp_one_gt_d9])
  have h'₁ : (5 * Real.exp (4 * σ / 5)) * σ ≤ 9.3 * Real.exp σ := by
    rw [show 4 * σ / 5 = σ + (-σ / 5) by ring, Real.exp_add]
    convert mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 5)).trans
      (by convert ht using 1; ring)) (Real.exp_nonneg σ) using 1 <;> ring
  exact (le_div_iff₀ hσ).2 h'₁

/-- The averaged inner exponential mass is at most the constant used in (18). -/
theorem nearOrigin_inner_average_integral_le {σ : ℝ} (hσ : 0 < σ) :
    (∫ η in (-4 : ℝ)..4, nearOriginInnerAverage σ η) ≤ 15 * Real.exp σ / σ := by
  let f := nearOriginInnerAverage σ
  have hc (a b : ℝ) : IntervalIntegrable f volume a b :=
    (continuous_nearOriginInnerAverage σ).intervalIntegrable _ _
  have hs₁ := integral_add_adjacent_intervals (hc 0 (1 / 2)) (hc (1 / 2) 2)
  have hs₂ := integral_add_adjacent_intervals (hc 0 2) (hc 2 4)
  have hs₃ := integral_add_adjacent_intervals (hc (-4) 0) (hc 0 4)
  have hneg : (∫ η in (-4 : ℝ)..0, f η) = ∫ η in (0 : ℝ)..4, f η := by
    symm
    simpa only [f, nearOriginInnerAverage_neg, neg_zero] using
      (integral_comp_neg (f := f) (a := 0) (b := 4))
  have ha : (∫ η in (0 : ℝ)..(1 / 2), f η) ≤ (1 / 2) * Real.exp (4 * σ / 5) := by
    calc
      _ ≤ ∫ _η in (0 : ℝ)..(1 / 2), Real.exp (4 * σ / 5) := by
        apply integral_mono_on (by norm_num) (hc _ _) intervalIntegrable_const
        intro η hη
        exact nearOriginInnerAverage_le_outer hσ hη.1 (.inl hη.2)
      _ = _ := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  have hb : (∫ η in (2 : ℝ)..4, f η) ≤ 2 * Real.exp (4 * σ / 5) := by
    calc
      _ ≤ ∫ _η in (2 : ℝ)..4, Real.exp (4 * σ / 5) := by
        apply integral_mono_on (by norm_num) (hc _ _) intervalIntegrable_const
        intro η hη
        exact nearOriginInnerAverage_le_outer hσ (by linarith [hη.1]) (.inr hη.1)
      _ = _ := by rw [intervalIntegral.integral_const]; norm_num [smul_eq_mul]
  have hmid := nearOrigin_inner_positive_middle hσ
  have hlose := nearOrigin_exp_loss hσ
  change (∫ η in (-4 : ℝ)..4, f η) ≤ _
  rw [← hs₃, hneg, ← hs₂, ← hs₁]
  dsimp only [f] at *
  simp only [mul_div_assoc] at ha hb hmid hlose ⊢
  linarith [show 0 ≤ Real.exp σ / σ by positivity]

end DurfeeCCS.Step08
