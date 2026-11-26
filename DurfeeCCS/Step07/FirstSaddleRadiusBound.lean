module

public import DurfeeCCS.Step06.SaddleComponents
public import DurfeeCCS.Step07.TrigonometricBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The sharpened lower bound for the last radius group on page 22. -/

@[expose] public section

namespace DurfeeCCS.Step07

open MeasureTheory Set

private theorem log_one_add_ge_four_terms {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 ≤ Real.log (1 + x) := by
  let f (t : ℝ) := Real.log (1 + t) - (t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4)
  have hder (t : ℝ) (ht : 0 ≤ t) : HasDerivAt f (t ^ 4 / (1 + t)) t := by
    have hi := hasDerivAt_id t
    have hlog := (Real.hasDerivAt_log (show (1 + t) ≠ 0 by positivity)).comp t
      (hi.const_add 1)
    have hp := ((hi.sub ((hi.pow 2).div_const 2)).add ((hi.pow 3).div_const 3)).sub
      ((hi.pow 4).div_const 4)
    convert hlog.sub hp using 1
    · funext u
      dsimp [f, Function.comp_def]
    · norm_num
      field_simp
      ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht₀ : 0 ≤ t := interior_subset ht
      rw [(hder t ht₀).deriv]
      positivity
  have hh := hmono (show (0 : ℝ) ∈ Ici 0 from le_rfl) hx hx
  simpa [f, sub_nonneg] using hh

private theorem log_ratio_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ Real.log (1 + t ^ 2) / t := by
  exact div_nonneg (Real.log_nonneg (by linarith [sq_nonneg t])) ht.le

private theorem log_ratio_le {t : ℝ} (ht : 0 < t) :
    Real.log (1 + t ^ 2) / t ≤ t := by
  apply (div_le_iff₀ ht).2
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + t ^ 2 by positivity)
  ring_nf at h ⊢
  exact h

private theorem arctan_ratio_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ Real.arctan t / t := by
  exact div_nonneg (Real.arctan_nonneg.mpr ht.le) ht.le

private theorem arctan_ratio_le {t : ℝ} (ht : 0 < t) :
    Real.arctan t / t ≤ 1 := by
  rw [div_le_one ht]
  have h := (arctan_taylor_bounds ht.le 1).1
  simpa [arctanTaylor, Finset.sum_range_succ, sub_nonneg] using h

private theorem intervalIntegrable_ratio {r b : ℝ} (hr : 0 ≤ r) {f : ℝ → ℝ}
    (hf : Measurable f) (hb : ∀ t ∈ Ioc (0 : ℝ) r, 0 ≤ f t ∧ f t ≤ b) :
    IntervalIntegrable f volume 0 r := by
  have hi : IntervalIntegrable (fun _ : ℝ => b) volume 0 r := intervalIntegrable_const
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr]
  refine hi.1.mono' hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := r))]
    with t ht
  simpa [Real.norm_of_nonneg (hb t ht).1] using (hb t ht).2

private theorem integral_log_ratio_bound {r : ℝ} (hr : 0 < r) :
    r ^ 2 / 2 - r ^ 4 / 8 + r ^ 6 / 18 - r ^ 8 / 32 ≤
      (∫ t in (0 : ℝ)..r, Real.log (1 + t ^ 2) / t) ∧
      (∫ t in (0 : ℝ)..r, Real.log (1 + t ^ 2) / t) ≤ r ^ 2 / 2 := by
  let p (t : ℝ) := t - t ^ 3 / 2 + t ^ 5 / 3 - t ^ 7 / 4
  have hf : IntervalIntegrable (fun t => Real.log (1 + t ^ 2) / t) volume 0 r :=
    intervalIntegrable_ratio hr.le (by fun_prop)
      (fun _ ht => ⟨log_ratio_nonneg ht.1, (log_ratio_le ht.1).trans ht.2⟩)
  have hp : IntervalIntegrable p volume 0 r := (by unfold p; fun_prop : Continuous p).intervalIntegrable ..
  have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 r := continuous_id.intervalIntegrable ..
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo hr.le hp hf (fun t ht => by
    apply (le_div_iff₀ ht.1).2
    have hl := log_one_add_ge_four_terms (x := t ^ 2) (sq_nonneg t)
    unfold p
    ring_nf at hl ⊢
    exact hl)
  have hge := intervalIntegral.integral_mono_on_of_le_Ioo hr.le hf hid
    (fun _ ht => log_ratio_le ht.1)
  have hpEval : ∫ t in (0 : ℝ)..r, p t = r ^ 2 / 2 - r ^ 4 / 8 + r ^ 6 / 18 - r ^ 8 / 32 := by
    let P (t : ℝ) := t ^ 2 / 2 - t ^ 4 / 8 + t ^ 6 / 18 - t ^ 8 / 32
    have hder (t : ℝ) : HasDerivAt P (p t) t := by
      have hi := hasDerivAt_id t
      convert ((((hi.pow 2).div_const 2).sub ((hi.pow 4).div_const 8)).add
        ((hi.pow 6).div_const 18)).sub ((hi.pow 8).div_const 32) using 1
      · funext u
        dsimp [P]
      · norm_num [p]
        ring
    simpa [P] using (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hp)
  rw [hpEval] at hle
  have hEval : ∫ t in (0 : ℝ)..r, t = r ^ 2 / 2 := by
    simp
  rw [hEval] at hge
  exact ⟨hle, hge⟩

private theorem integral_arctan_ratio_bound {r : ℝ} (hr : 0 < r) :
    r - r ^ 3 / 9 + r ^ 5 / 25 - r ^ 7 / 49 ≤
      (∫ t in (0 : ℝ)..r, Real.arctan t / t) ∧
      (∫ t in (0 : ℝ)..r, Real.arctan t / t) ≤ r := by
  let p (t : ℝ) := 1 - t ^ 2 / 3 + t ^ 4 / 5 - t ^ 6 / 7
  have hf : IntervalIntegrable (fun t => Real.arctan t / t) volume 0 r :=
    intervalIntegrable_ratio hr.le (by fun_prop)
      (fun _ ht => ⟨arctan_ratio_nonneg ht.1, arctan_ratio_le ht.1⟩)
  have hp : IntervalIntegrable p volume 0 r := (by unfold p; fun_prop : Continuous p).intervalIntegrable ..
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo hr.le hp hf (fun t ht => by
    apply (le_div_iff₀ ht.1).2
    have hl := (arctan_taylor_bounds ht.1.le 4).1
    norm_num [arctanTaylor, Finset.sum_range_succ] at hl
    unfold p
    linarith only [show p t * t =
      t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 by unfold p; ring, hl])
  have hge := intervalIntegral.integral_mono_on_of_le_Ioo hr.le hf
    (intervalIntegrable_const (c := (1 : ℝ))) (fun _ ht => arctan_ratio_le ht.1)
  have hpEval : ∫ t in (0 : ℝ)..r, p t = r - r ^ 3 / 9 + r ^ 5 / 25 - r ^ 7 / 49 := by
    let P (t : ℝ) := t - t ^ 3 / 9 + t ^ 5 / 25 - t ^ 7 / 49
    have hder (t : ℝ) : HasDerivAt P (p t) t := by
      have hi := hasDerivAt_id t
      convert ((hi.sub ((hi.pow 3).div_const 9)).add ((hi.pow 5).div_const 25)).sub
        ((hi.pow 7).div_const 49) using 1
      · funext u
        dsimp [P]
      · norm_num [p]
        ring
    simpa [P] using (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hp)
  rw [hpEval] at hle
  exact ⟨hle, by simpa using hge⟩

/-- For radii up to one, the real part, slope, and norm bounds in equation (23). -/
theorem firstSaddle_coordinates_bounds {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    let s := Step06.saddleS r
    r ≤ s.re ^ 2 ∧ s.re ^ 2 ≤ r * (1 + 0.282 * r) ∧
      1 - 0.282 * r ≤ s.im / s.re ∧ s.im / s.re ≤ 1 ∧ 16 * r / 9 ≤ ‖s‖ ^ 2 := by
  let s := Step06.saddleS r
  let z := Step06.saddlePhaseSquare r
  let a := s.re
  let b := s.im
  let R := z.re
  let I := z.im
  let N := ‖z‖
  have hs : z = s ^ 2 := (Step06.saddleS_sq r).symm
  have ⟨hb, hba⟩ : 0 < b ∧ b < a := Step06.saddleS_components hr
  have ha : 0 < a := hb.trans hba
  have hR : 0 < R := (Step06.saddlePhaseSquare_quadrant hr).1
  have hI : 0 < I := (Step06.saddlePhaseSquare_quadrant hr).2
  have hRN : R = a ^ 2 - b ^ 2 := by
    dsimp [R, a, b]
    rw [hs, pow_two, Complex.mul_re]
    ring
  have hIN : I = 2 * a * b := by
    dsimp [I, a, b]
    rw [hs, pow_two, Complex.mul_im]
    ring
  have hNAB : N = a ^ 2 + b ^ 2 := by
    dsimp [N, a, b]
    rw [hs, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hNs : N = ‖s‖ ^ 2 := by
    change ‖z‖ = ‖s‖ ^ 2
    rw [hs, norm_pow]
  have hNI : I ≤ N := Complex.im_le_norm _
  have hz := Step06.saddlePhaseSquare_integral_components hr
  have hsquare := pow_le_one₀ hr.le hr₁ (n := 2)
  have hRlo : 3 * r ^ 2 / 8 ≤ R := by
    have hlow : r ^ 2 / 2 - r ^ 4 / 8 + r ^ 6 / 18 - r ^ 8 / 32 ≤ R := by
      unfold R z
      rw [hz.1]
      exact (integral_log_ratio_bound hr).1
    nlinarith only [hlow, mul_le_mul_of_nonneg_left hsquare (sq_nonneg r),
      mul_le_mul_of_nonneg_left hsquare (pow_nonneg hr.le 6), pow_nonneg hr.le 6]
  have hRhi : R ≤ r ^ 2 / 2 := by
    unfold R z
    rw [hz.1]
    exact (integral_log_ratio_bound hr).2
  have hIlo : 2 * (r - r ^ 3 / 9) ≤ I := by
    have hlow : 2 * (r - r ^ 3 / 9 + r ^ 5 / 25 - r ^ 7 / 49) ≤ I := by
      unfold I z
      rw [hz.2]
      exact mul_le_mul_of_nonneg_left (integral_arctan_ratio_bound hr).1 (by norm_num)
    nlinarith only [hlow, mul_le_mul_of_nonneg_left hsquare (pow_nonneg hr.le 5), pow_nonneg hr.le 5]
  have hIhi : I ≤ 2 * r := by
    unfold I z
    rw [hz.2]
    exact mul_le_mul_of_nonneg_left (integral_arctan_ratio_bound hr).2 (by norm_num)
  have hr32 : r ^ 3 ≤ r ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hr₁ (sq_nonneg r)]
  have hNhi : N ≤ 2 * r + r ^ 3 / 16 := by
    have hNsquare : N ^ 2 = R ^ 2 + I ^ 2 := by
      dsimp [N, R, I]
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hRsquare := pow_le_pow_left₀ hR.le hRhi 2
    have hIsquare := pow_le_pow_left₀ hI.le hIhi 2
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    nlinarith only [hNsquare, hRsquare, hIsquare, sq_nonneg (r ^ 3)]
  have hIshort : 16 * r / 9 ≤ I := by
    nlinarith only [hIlo, mul_le_mul_of_nonneg_left hsquare hr.le]
  change r ≤ a ^ 2 ∧ a ^ 2 ≤ r * (1 + 0.282 * r) ∧
    1 - 0.282 * r ≤ b / a ∧ b / a ≤ 1 ∧ 16 * r / 9 ≤ ‖s‖ ^ 2
  refine ⟨?_, ?_, ?_, (div_le_one ha).2 hba.le, ?_⟩
  · nlinarith only [hRlo, hIlo, hNI, hRN, hNAB, hr32, sq_nonneg r]
  · nlinarith only [hRhi, hNhi, hRN, hNAB, hr32, sq_nonneg r]
  · apply (le_div_iff₀ ha).2
    have hdiff : (a - b) * I ≤ a * R := by
      rw [hIN, hRN]
      nlinarith only [mul_nonneg ha.le (sq_nonneg (a - b))]
    have h₁ := mul_le_mul_of_nonneg_left hIshort (sub_nonneg.mpr hba.le)
    have h₂ := mul_le_mul_of_nonneg_left hRhi ha.le
    apply (mul_le_mul_iff_of_pos_right (show 0 < 16 * r / 9 by positivity)).mp
    nlinarith only [h₁, h₂, hdiff, mul_nonneg ha.le (sq_nonneg r)]
  · rw [← hNs]
    exact hIshort.trans hNI

private theorem firstSaddleRadius_polynomial {r : ℝ} (hr₀ : 0.9 ≤ r) (hr₁ : r ≤ 1) :
     (31 / 288 : ℝ) ≤ r / 4 - r ^ 2 / 9 - r ^ 3 / 16 + r ^ 4 / 32 ∧
       (1 / 32 : ℝ) ≤ 1 / 25 + r / 36 - r ^ 2 / 49 - r ^ 3 / 64 := by
  let t := 1 - r
  have ht₀ : 0 ≤ t := sub_nonneg.mpr hr₁
  have ht₁ : t ≤ 0.1 := by dsimp [t]; linarith
  have ht₂ : t ^ 2 ≤ (0.1 : ℝ) ^ 2 := pow_le_pow_left₀ ht₀ ht₁ 2
  have ht₃ : 0 ≤ t ^ 3 := pow_nonneg ht₀ _
  have hf : 0 ≤ 5 / 144 - t / 9 - t ^ 2 / 16 + t ^ 3 / 32 := by linarith
  have hg : 0 ≤ -1 / 36 + 2 / 49 + 3 / 64 - t * (1 / 49 + 3 / 64) + t ^ 2 / 64 := by
    linarith [sq_nonneg t]
  constructor
  · have he : r / 4 - r ^ 2 / 9 - r ^ 3 / 16 + r ^ 4 / 32 - 31 / 288 =
        t * (5 / 144 - t / 9 - t ^ 2 / 16 + t ^ 3 / 32) := by dsimp [t]; ring
    rw [← sub_nonneg, he]
    exact mul_nonneg ht₀ hf
  · calc
      _ ≤ (1 / 25 : ℝ) + 1 / 36 - 1 / 49 - 1 / 64 := by norm_num
      _ ≤ _ := by
        have he : 1 / 25 + r / 36 - r ^ 2 / 49 - r ^ 3 / 64 -
            (1 / 25 + 1 / 36 - 1 / 49 - 1 / 64) =
            t * (-1 / 36 + 2 / 49 + 3 / 64 - t * (1 / 49 + 3 / 64) + t ^ 2 / 64) := by
          dsimp [t]
          ring
        rw [← sub_nonneg, he]
        exact mul_nonneg ht₀ hg

/-- The lower bound for `a²/r` in the last row of the page 22 table. -/
theorem firstSaddleRadius_sharp {r : ℝ} (hr₀ : 0.9 ≤ r) (hr₁ : r ≤ 1) :
    (1.12 : ℝ) * r < (Step06.saddleS r).re ^ 2 := by
  have hr : 0 < r := by linarith
  let s := Step06.saddleS r
  let z := Step06.saddlePhaseSquare r
  let R := z.re
  let I := z.im
  let N := ‖z‖
  have hR : 0 < R := (Step06.saddlePhaseSquare_quadrant hr).1
  have hI : 0 < I := (Step06.saddlePhaseSquare_quadrant hr).2
  have hN : 0 ≤ N := norm_nonneg _
  have hz := Step06.saddlePhaseSquare_integral_components hr
  have hR₁ : r ^ 2 / 2 - r ^ 4 / 8 + r ^ 6 / 18 - r ^ 8 / 32 ≤ R := by
    unfold R z
    rw [hz.1]
    exact (integral_log_ratio_bound hr).1
  have hR₂ : R ≤ r ^ 2 / 2 := by
    unfold R z
    rw [hz.1]
    exact (integral_log_ratio_bound hr).2
  have hI₁ : 2 * (r - r ^ 3 / 9 + r ^ 5 / 25 - r ^ 7 / 49) ≤ I := by
    unfold I z
    rw [hz.2]
    exact mul_le_mul_of_nonneg_left (integral_arctan_ratio_bound hr).1 (by norm_num)
  have hI₂ : I ≤ 2 * r := by
    unfold I z
    rw [hz.2]
    exact mul_le_mul_of_nonneg_left (integral_arctan_ratio_bound hr).2 (by norm_num)
  obtain ⟨hf, hg⟩ := firstSaddleRadius_polynomial hr₀ hr₁
  have hsum : 2 * r * (1 + 31 / 288) ≤ R + I := by
    calc
      _ ≤ 2 * r * (1 + (r / 4 - r ^ 2 / 9 - r ^ 3 / 16 + r ^ 4 / 32) +
            r ^ 4 * (1 / 25 + r / 36 - r ^ 2 / 49 - r ^ 3 / 64 - 1 / 32)) := by
        have hnonneg := mul_nonneg (pow_nonneg hr.le 4) (sub_nonneg.mpr hg)
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (r ^ 2 / 2 - r ^ 4 / 8 + r ^ 6 / 18 - r ^ 8 / 32) +
            2 * (r - r ^ 3 / 9 + r ^ 5 / 25 - r ^ 7 / 49) := by ring
      _ ≤ _ := add_le_add hR₁ hI₁
  have hRlo : 3 * r ^ 2 / 8 ≤ R := by
    have hle := pow_le_one₀ hr.le hr₁ (n := 2)
    nlinarith only [hR₁, mul_le_mul_of_nonneg_left hle (sq_nonneg r),
      mul_le_mul_of_nonneg_left hle (pow_nonneg hr.le 6), pow_nonneg hr.le 6]
  have hN_sq : N ^ 2 = R ^ 2 + I ^ 2 := by
    dsimp [N, R, I]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hN_rel : N = s.re ^ 2 + s.im ^ 2 := by
    change ‖z‖ = _
    rw [show z = s ^ 2 from (Step06.saddleS_sq r).symm, norm_pow,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  have hR_rel : R = s.re ^ 2 - s.im ^ 2 := by
    change z.re = _
    rw [show z = s ^ 2 from (Step06.saddleS_sq r).symm, pow_two, Complex.mul_re]
    ring
  have hN_hi : N < 5 * r / 2 := by
    have hs : r ^ 2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hr₁ hr.le]
    have hRpow : R ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ hR.le (by linarith) 2
    have hIpow : I ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ hI.le hI₂ 2
    have hn : N ^ 2 < (5 * r / 2) ^ 2 := by nlinarith only [hN_sq, hRpow, hIpow, sq_pos_of_pos hr]
    exact (sq_lt_sq₀ hN (by positivity)).1 hn
  have hΔ : r ^ 3 / 32 < N - I := by
    have hQ : 0 < N + I := by linarith
    apply (mul_lt_mul_iff_of_pos_right hQ).mp
    have hterm : N + I < 9 * r / 2 := by linarith
    have hRpow := pow_le_pow_left₀ (show 0 ≤ 3 * r ^ 2 / 8 by positivity) hRlo 2
    have hL := mul_lt_mul_of_pos_left hterm (show 0 < r ^ 3 / 32 by positivity)
    nlinarith only [hN_sq, hRpow, hL]
  change 1.12 * r < s.re ^ 2
  have hr2 : (0.9 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num) hr₀ 2
  nlinarith only [hsum, hN_rel, hR_rel, hΔ, mul_le_mul_of_nonneg_right hr2 hr.le, hr]

end DurfeeCCS.Step07
