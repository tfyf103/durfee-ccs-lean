module

public import DurfeeCCS.Step07.ThetaFinite

/-! Dominance of the finite-row Gaussian bounds after the turnover point. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open DurfeeCCS.Step06 Real

theorem sqrt_mul_exp_antitoneOn {u c : ℝ} (hu : 0 ≤ u) (hc : 0 ≤ c)
    (hturn : (1 / 2 : ℝ) ≤ c * u) :
    AntitoneOn (fun x : ℝ => √x * exp (-c * x)) (Set.Ici u) := by
  have hcut : (1 : ℝ) ≤ c * 2 * (√u) ^ 2 := by
    rw [Real.sq_sqrt hu]
    nlinarith
  have h := power_mul_exp_antitoneOn (x₀ := √u) (a := c) (b := 0) 1 2
    (by decide) (by decide) (Real.sqrt_nonneg _) hc (by simpa only [Nat.cast_one, Nat.cast_ofNat]
      using hcut)
  intro x hx y hy hxy
  have h' := h (show √x ∈ Set.Ici (√u) from Real.sqrt_le_sqrt hx)
    (show √y ∈ Set.Ici (√u) from Real.sqrt_le_sqrt hy) (Real.sqrt_le_sqrt hxy)
  simpa only [pow_one, add_zero, Real.sq_sqrt (hu.trans hx), Real.sq_sqrt (hu.trans hy)] using h'

/-- Gaussian approximation error (60), with the row's cutoff δ. -/
def theta38GaussianError (a b δ x : ℝ) : ℝ :=
  (2 * a * x)⁻¹ + (1 + (2 * a * x)⁻¹) * exp (-4 * a * x) +
    8 * √(a * x) * (exp (-b ^ 2 * x / a) + exp (-δ * a * x))

/-- Gaussian bound `E_J` printed with the finite-row formulas. -/
def Theta38Row.gaussianBound (row : Theta38Row) : ℝ :=
  let δ := theta38Delta row.aMin row.bMax
  (160 * row.aMin)⁻¹ + (1 + (160 * row.aMin)⁻¹) * exp (-320 * row.aMin) +
    8 * √(80 * row.aMax) * (exp (-80 * row.bMin ^ 2 / row.aMax) + exp (-80 * row.aMin * δ))

theorem theta38_gaussian_error_le (i : Fin 9) {r x : ℝ} (hx : 80 ≤ x)
    (hs : (theta38Row i).encloses r) :
    theta38GaussianError (saddleS r).re (saddleS r).im
      (theta38Delta (theta38Row i).aMin (theta38Row i).bMax) x ≤
      (theta38Row i).gaussianBound := by
  let row := theta38Row i
  let a := (saddleS r).re
  let b := (saddleS r).im
  let δ := theta38Delta row.aMin row.bMax
  obtain ⟨haMin, haMax, _, _, _⟩ := theta38_rows_admissible i
  obtain ⟨hturnB, hturnD⟩ := theta38_row_gaussian_admissible i hs
  obtain ⟨hal, hau, hbl, _⟩ := hs
  have ha : 0 < a := haMin.trans_le hal
  have hx₀ : 0 ≤ x := by linarith
  have hδ : 0 ≤ δ := by unfold δ theta38Delta; positivity
  have hra : 80 * row.aMin ≤ a * x := by
    rw [mul_comm (80 : ℝ) row.aMin]
    exact mul_le_mul_of_nonneg hal hx haMin.le hx₀
  have hrax : 80 * a ≤ a * x := by
    rw [mul_comm (80 : ℝ) a]
    exact mul_le_mul_of_nonneg_left hx ha.le
  have hxaa : √(80 * a) ≤ √(80 * row.aMax) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hau (by norm_num))
  have hrec : (2 * a * x)⁻¹ ≤ (160 * row.aMin)⁻¹ :=
    inv_anti₀ (mul_pos (by norm_num) haMin) (by nlinarith [hra])
  have hrate : row.bMin ^ 2 / row.aMax ≤ b ^ 2 / a :=
    div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (theta38_rows_b_pos i).le hbl 2) ha hau
  have hgb : √(a * x) * exp (-b ^ 2 * x / a) ≤
      √(80 * row.aMax) * exp (-80 * row.bMin ^ 2 / row.aMax) := by
    calc
      _ = √a * (√x * exp (-(b ^ 2 / a) * x)) := by
        rw [Real.sqrt_mul ha.le, show -b ^ 2 * x / a = -(b ^ 2 / a) * x by ring, mul_assoc]
      _ ≤ √a * (√80 * exp (-(b ^ 2 / a) * 80)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact sqrt_mul_exp_antitoneOn (by norm_num) (by positivity) hturnB le_rfl hx hx
      _ = √(80 * a) * exp (-(b ^ 2 / a) * 80) := by
        rw [mul_comm (80 : ℝ) a, Real.sqrt_mul ha.le, mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg hxaa _ (Real.sqrt_nonneg _) (by positivity)
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right hrate (show (0 : ℝ) ≤ 80 by norm_num)
        convert neg_le_neg h using 1 <;> ring
  have hgd : √(a * x) * exp (-δ * a * x) ≤
      √(80 * row.aMax) * exp (-80 * row.aMin * δ) := by
    calc
      _ = √(a * x) * exp (-δ * (a * x)) := by rw [mul_assoc]
      _ ≤ √(80 * a) * exp (-δ * (80 * a)) :=
        sqrt_mul_exp_antitoneOn (by positivity) hδ hturnD le_rfl hrax hrax
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg hxaa _ (Real.sqrt_nonneg _) (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hδ (sub_nonneg.mpr hal)]
  have hga : exp (-4 * a * x) ≤ exp (-320 * row.aMin) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hra]
  change theta38GaussianError a b δ x ≤ row.gaussianBound
  unfold theta38GaussianError Theta38Row.gaussianBound
  dsimp only
  have hmain :
      (1 + (2 * a * x)⁻¹) * exp (-4 * a * x) ≤
        (1 + (160 * row.aMin)⁻¹) * exp (-320 * row.aMin) :=
    mul_le_mul_of_nonneg (add_le_add le_rfl hrec) hga (by positivity) (by positivity)
  calc
    _ = (2 * a * x)⁻¹ + (1 + (2 * a * x)⁻¹) * exp (-4 * a * x) +
        8 * (√(a * x) * exp (-b ^ 2 * x / a) + √(a * x) * exp (-δ * a * x)) := by ring
    _ ≤ (160 * row.aMin)⁻¹ + (1 + (160 * row.aMin)⁻¹) * exp (-320 * row.aMin) +
        8 * (√(80 * row.aMax) * exp (-80 * row.bMin ^ 2 / row.aMax) +
          √(80 * row.aMax) * exp (-80 * row.aMin * δ)) :=
      add_le_add (add_le_add hrec hmain)
        (mul_le_mul_of_nonneg_left (add_le_add hgb hgd) (by norm_num))
    _ = _ := by ring

/-- Use the original saddle-dependent cutoff in (60) before replacing it by the row lower bound. -/
theorem theta38_gaussian_at_actual_cutoff_le (i : Fin 9) {r x : ℝ} (hx : 80 ≤ x)
    (hs : (theta38Row i).encloses r) :
    let a := (saddleS r).re
    let b := (saddleS r).im
    theta38GaussianError a b ((3 - 2 * (b / a)) ^ 2 / 13) x ≤ (theta38Row i).gaussianBound := by
  have hG := theta38_gaussian_error_le i hx hs
  obtain ⟨hal, _, hbl, hbu⟩ := hs
  obtain ⟨ham, _, _, _, _⟩ := theta38_rows_admissible i
  have ha := ham.le.trans hal
  have hb := (theta38_rows_b_pos i).le.trans hbl
  have hx₀ : 0 ≤ x := by linarith
  have hδ := theta38_row_delta_le hal hbu hb
  refine le_trans ?_ hG
  unfold theta38GaussianError
  gcongr

/-- The angular tail before applying the threshold `√n = 80`. -/
def theta38AngularTail (a δ δ₃ x : ℝ) : ℝ :=
  96 * √(a * x) * exp (-δ * a * x) + 57000 * √(a * x) * exp (-δ₃ * a * x)

/-- Angular tail bound `E_η` in (59). -/
def Theta38Row.angularTailBound (row : Theta38Row) : ℝ :=
  theta38AngularTail row.aMin (theta38Delta row.aMin row.bMax)
    (theta38DeltaThree row.aMin row.bMax) 80

theorem theta38_angular_tail_le (i : Fin 9) {r x : ℝ} (hx : 80 ≤ x)
    (hs : (theta38Row i).encloses r) :
    theta38AngularTail (saddleS r).re (theta38Delta (theta38Row i).aMin (theta38Row i).bMax)
      (theta38DeltaThree (theta38Row i).aMin (theta38Row i).bMax) x ≤
      (theta38Row i).angularTailBound := by
  let row := theta38Row i
  let a := (saddleS r).re
  let δ := theta38Delta row.aMin row.bMax
  let δ₃ := theta38DeltaThree row.aMin row.bMax
  obtain ⟨haMin, _, _, hturn, _⟩ := theta38_rows_admissible i
  obtain ⟨hal, _, _, _⟩ := hs
  have hδ : 0 ≤ δ := by unfold δ theta38Delta; positivity
  have hδ₃ : 0 ≤ δ₃ := hδ.trans (theta38_rows_delta_le_three i)
  have hu : 0 ≤ row.aMin * 80 := by positivity
  have hx' : row.aMin * 80 ≤ a * x :=
    mul_le_mul_of_nonneg hal hx haMin.le ((by norm_num : (0 : ℝ) ≤ 80).trans hx)
  have hturn₁ : (1 / 2 : ℝ) ≤ δ * (row.aMin * 80) := hturn.le.trans_eq (by ring)
  have hturn₂ : (1 / 2 : ℝ) ≤ δ₃ * (row.aMin * 80) :=
    hturn₁.trans (mul_le_mul_of_nonneg_right (theta38_rows_delta_le_three i) hu)
  have h₁ := sqrt_mul_exp_antitoneOn hu hδ hturn₁ le_rfl hx' hx'
  have h₂ := sqrt_mul_exp_antitoneOn hu hδ₃ hturn₂ le_rfl hx' hx'
  change theta38AngularTail a δ δ₃ x ≤ theta38AngularTail row.aMin δ δ₃ 80
  unfold theta38AngularTail
  calc
    _ = 96 * (√(a * x) * exp (-δ * (a * x))) +
        57000 * (√(a * x) * exp (-δ₃ * (a * x))) := by simp only [mul_assoc]
    _ ≤ 96 * (√(row.aMin * 80) * exp (-δ * (row.aMin * 80))) +
        57000 * (√(row.aMin * 80) * exp (-δ₃ * (row.aMin * 80))) :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num)) (mul_le_mul_of_nonneg_left h₂ (by norm_num))
    _ = _ := by simp only [mul_assoc]

/-- The row bound remains valid with (59) and (60) evaluated at the varying inputs.
The first three terms are the uniform row bounds from (58). -/
theorem theta38_budget_with_actual_gaussian_tail_lt (i : Fin 9) {r x : ℝ} (hx : 80 ≤ x)
    (hs : (theta38Row i).encloses r) :
    let row := theta38Row i
    let a := (saddleS r).re
    let b := (saddleS r).im
    let δ := theta38Delta row.aMin row.bMax
    let δ₃ := theta38DeltaThree row.aMin row.bMax
    row.error - row.gaussianBound - row.angularTailBound +
      theta38GaussianError a b δ x + theta38AngularTail a δ δ₃ x < row.target := by
  have hG := theta38_gaussian_error_le i hx hs
  have hE := theta38_angular_tail_le i hx hs
  have hR := theta38_error_rows i
  dsimp only
  linarith

end DurfeeCCS.Step07
