module

public import DurfeeCCS.SignRoots
public import DurfeeCCS.Step08.NearOriginApproximation
public import DurfeeCCS.Step08.PhaseGapParameters
public import DurfeeCCS.Step11.NearOriginSigned
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! The near-origin endpoint and the seven roots supplied by Corollary 3.2. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step11

open Set Polynomial
open DurfeeCCS.Step06 DurfeeCCS.Step07 DurfeeCCS.Step08

/-- The common endpoint of the near-origin and saddle arguments. -/
def nearOriginRadius (n : ℕ) : ℝ := 16 * Real.pi ^ 2 / (n : ℝ)

theorem nearOriginRadius_pos {n : ℕ} (hn : 6401 ≤ n) : 0 < nearOriginRadius n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold nearOriginRadius
  positivity

theorem nearOriginRadius_lt_small {n : ℕ} (hn : 6401 ≤ n) :
    nearOriginRadius n < 0.025 := by
  have hn' : (6401 : ℝ) ≤ n := by exact_mod_cast hn
  have hπ : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d6]
  have hp : Real.pi ^ 2 ≤ (22 / 7 : ℝ) ^ 2 := by gcongr
  unfold nearOriginRadius
  exact (div_lt_iff₀ (show 0 < (n : ℝ) by linarith)).mpr (by linarith only [hp, hn'])

theorem nearOriginRadius_lt_one {n : ℕ} (hn : 6401 ≤ n) : nearOriginRadius n < 1 :=
  (nearOriginRadius_lt_small hn).trans (by norm_num)

theorem sqrt_mul_nearOriginRadius {n : ℕ} (hn : 6401 ≤ n) :
    Real.sqrt ((n : ℝ) * nearOriginRadius n) = 4 * Real.pi := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [nearOriginRadius, show (n : ℝ) * (16 * Real.pi ^ 2 / n) =
    (4 * Real.pi) ^ 2 by field_simp; ring, Real.sqrt_sq (by positivity)]

/-- The radial component contributes at most half the radius to the relative phase error. -/
private theorem nearOrigin_im_ratio {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    |(saddleS r).im / Real.sqrt r - 1| ≤ r / 2 := by
  let a := (saddleS r).re
  let b := (saddleS r).im
  let c := Real.sqrt r
  have ⟨hb, hba⟩ : 0 < b ∧ b < a := saddleS_components hr
  have hc : 0 < c := Real.sqrt_pos.2 hr
  have hc2 : c ^ 2 = r := Real.sq_sqrt hr.le
  have hA : r ≤ a ^ 2 ∧ a ^ 2 ≤ r * (1 + 0.282 * r) ∧ _ :=
    firstSaddle_coordinates_bounds hr hr₁
  have hRe : (saddlePhaseSquare r).re = a ^ 2 - b ^ 2 := by
    rw [← saddleS_sq, pow_two, Complex.mul_re]
    simp only [a, b, pow_two]
  have hB : r - r ^ 2 / 2 ≤ b ^ 2 ∧ b ^ 2 ≤ r * (1 + 0.282 * r) := by
    have hup := saddlePhaseSquare_re_le_sq_half hr
    have hpos := (saddlePhaseSquare_quadrant hr).1
    rw [hRe] at hup hpos
    exact ⟨by linarith only [hA.1, hup], by linarith only [hA.2.1, hpos]⟩
  have hlow_sq : ((1 - r / 2) * c) ^ 2 ≤ b ^ 2 := by
    rw [mul_pow, hc2]
    have h := mul_nonneg (sq_nonneg r) (show 0 ≤ 2 - r by linarith only [hr₁])
    nlinarith only [hB.1, h]
  have hhigh_sq : b ^ 2 ≤ ((1 + r / 2) * c) ^ 2 := by
    rw [mul_pow, hc2]
    nlinarith only [hB.2, sq_nonneg r, pow_nonneg hr.le 3]
  have hlow : (1 - r / 2) * c ≤ b :=
    (sq_le_sq₀ (mul_nonneg (by linarith only [hr₁]) hc.le) hb.le).mp hlow_sq
  have hhigh : b ≤ (1 + r / 2) * c :=
    (sq_le_sq₀ hb.le (mul_nonneg (by linarith only [hr]) hc.le)).mp hhigh_sq
  change |b / c - 1| ≤ r / 2
  rw [abs_le]
  have hlow' := (le_div_iff₀ hc).mpr hlow
  have hhigh' := (div_le_iff₀ hc).mpr hhigh
  exact ⟨by linarith only [hlow'], by linarith only [hhigh']⟩

/-- The argument correction is strictly smaller than the radius. -/
private theorem nearOrigin_arg_correction {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    |(saddleS r).arg - Real.pi / 4 + Real.arctan r / 2| < r := by
  let a := (saddleS r).re
  let b := (saddleS r).im
  let z := saddlePhaseSquare r
  have ⟨hb, hba⟩ : 0 < b ∧ b < a := saddleS_components hr
  have ha : 0 < a := hb.trans hba
  have ⟨hre, him⟩ : 0 < z.re ∧ 0 < z.im := saddlePhaseSquare_quadrant hr
  have ha_sq : r ≤ a ^ 2 := (firstSaddle_coordinates_bounds hr hr₁).1
  have hratio : 1 - 0.282 * r ≤ b / a := (firstSaddle_coordinates_bounds hr hr₁).2.2.1
  have hB := mul_le_mul_of_nonneg_left ((le_div_iff₀ ha).mp hratio) ha.le
  have hA := mul_le_mul_of_nonneg_left ha_sq (show 0 ≤ 1 - 0.282 * r by linarith only [hr₁])
  have hIm_eq : z.im = 2 * a * b := by
    change (saddlePhaseSquare r).im = _
    rw [← saddleS_sq, pow_two, Complex.mul_im]
    simp only [a, b]
    ring
  have hIm : r < z.im := by
    rw [hIm_eq]
    have h := mul_pos hr (show 0 < 2 * (1 - 0.282 * r) - 1 by linarith only [hr₁])
    nlinarith only [hA, hB, h]
  have hRe := saddlePhaseSquare_re_le_sq_half hr
  have hQ : z.re / z.im < r / 2 := (div_lt_iff₀ him).mpr <|
    hRe.trans_lt (by nlinarith only [mul_lt_mul_of_pos_left hIm (show 0 < r / 2 by positivity)])
  have hArgL := Complex.arg_nonneg_iff.mpr him.le
  have hArgU := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hArg : z.arg = Real.arctan (z.im / z.re) := by
    rw [← Complex.tan_arg, Real.arctan_tan (by linarith only [Real.pi_pos, hArgL]) hArgU]
  have hz : z ≠ 0 := by
    intro hz
    change 0 < z.re at hre
    rw [hz, Complex.zero_re] at hre
    exact (lt_irrefl _ hre)
  have hHalf : (saddleS r).arg = z.arg / 2 := principalSqrt_arg hz
  have hInv := Real.arctan_inv_of_pos (div_pos him hre)
  rw [inv_div] at hInv
  have hGap : Real.pi / 4 - (saddleS r).arg = Real.arctan (z.re / z.im) / 2 := by
    rw [hHalf, hArg, hInv]
    ring
  have hGapL : 0 < Real.pi / 4 - (saddleS r).arg := by
    rw [hGap]
    exact div_pos (Real.arctan_pos.2 (div_pos hre him)) (by norm_num)
  have hGapU : Real.pi / 4 - (saddleS r).arg < r / 4 := by
    rw [hGap]
    linarith only [(Real.arctan_lt_self (div_pos hre him)).trans hQ]
  rw [abs_lt]
  exact ⟨by linarith only [hGapU, Real.arctan_pos.2 hr, hr],
    by linarith only [hGapL, Real.arctan_lt_self hr, hr]⟩

/-- The quantitative inner endpoint phase estimate used in the first-hitting construction. -/
theorem nearOrigin_phase_bound_strong {n : ℕ} (hn : 6401 ≤ n) :
    |saddlePhase n (nearOriginRadius n) - 8 * Real.pi| <
      (4 * Real.pi + 1) * nearOriginRadius n := by
  let r := nearOriginRadius n
  have hr : 0 < r := nearOriginRadius_pos hn
  have hr₁ : r ≤ 1 := (nearOriginRadius_lt_one hn).le
  let b := (saddleS r).im
  let c := Real.sqrt r
  have hc : 0 < c := Real.sqrt_pos.2 hr
  have hscale : 2 * c * Real.sqrt n = 8 * Real.pi := by
    rw [show (2 : ℝ) * c * Real.sqrt n = 2 * Real.sqrt n * c by ring]
    unfold c
    rw [mul_assoc, ← Real.sqrt_mul (Nat.cast_nonneg n), sqrt_mul_nearOriginRadius hn]
    ring
  have hrel : |b / c - 1| ≤ r / 2 := nearOrigin_im_ratio hr hr₁
  have harg := nearOrigin_arg_correction hr hr₁
  change |saddlePhase n r - 8 * Real.pi| < _
  have hPhase : saddlePhase n r - 8 * Real.pi =
      8 * Real.pi * (b / c - 1) + ((saddleS r).arg - Real.pi / 4 + Real.arctan r / 2) := by
    calc
      _ = (2 * c * Real.sqrt n) * (b / c) - 8 * Real.pi +
          ((saddleS r).arg - Real.pi / 4 + Real.arctan r / 2) := by
        unfold saddlePhase
        change 2 * b * Real.sqrt n + _ - Real.pi / 4 + _ - 8 * Real.pi = _
        field_simp [hc.ne']
        ring
      _ = _ := by rw [hscale]; ring
  rw [hPhase]
  have hM := abs_add_le (8 * Real.pi * (b / c - 1))
    ((saddleS r).arg - Real.pi / 4 + Real.arctan r / 2)
  rw [abs_mul, abs_of_pos (show 0 < 8 * Real.pi by positivity)] at hM
  have h := mul_le_mul_of_nonneg_left hrel (show 0 ≤ 8 * Real.pi by positivity)
  change _ < (4 * Real.pi + 1) * r
  linarith only [hM, h, harg,
    show 8 * Real.pi * (r / 2) + r = (4 * Real.pi + 1) * r by ring]

theorem nearOrigin_phase_budget {n : ℕ} (hn : 6401 ≤ n) :
    (4 * Real.pi + 1) * nearOriginRadius n < 0.35 := by
  have h := mul_lt_mul_of_pos_left (nearOriginRadius_lt_small hn)
    (show 0 < 4 * Real.pi + 1 by positivity)
  exact h.trans (by linarith only [Real.pi_lt_d6])

theorem nearOrigin_phase_bound {n : ℕ} (hn : 6401 ≤ n) :
    |saddlePhase n (nearOriginRadius n) - 8 * Real.pi| < 0.35 :=
  (nearOrigin_phase_bound_strong hn).trans (nearOrigin_phase_budget hn)

theorem nearOrigin_phase_lt_nine_pi {n : ℕ} (hn : 6401 ≤ n) :
    saddlePhase n (nearOriginRadius n) < 9 * Real.pi := by
  have h := (abs_lt.mp (nearOrigin_phase_bound hn)).2
  linarith only [h, Real.pi_gt_d2]

theorem nearOrigin_sample_eight {n : ℕ} (hn : 6401 ≤ n) :
    nearOriginSample n 8 = -(nearOriginRadius n) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold nearOriginSample nearOriginRadius
  push_cast
  field_simp [hn']
  ring

theorem nearOrigin_endpoint_pos {n : ℕ} (hn : 6401 ≤ n) :
    0 < (durfeePolynomialReal n).eval (-(nearOriginRadius n) ^ 2) := by
  rw [← nearOrigin_sample_eight hn]
  apply pos_of_sign_one
  have h := nearOrigin_sign_firstEight (k := 8) (by decide) (by decide) (by omega : 6400 ≤ n)
  norm_num at h
  exact h

private theorem nearOrigin_sample_strictAnti {n : ℕ} (hn : 0 < n) :
    StrictAnti (nearOriginSample n) := by
  intro i j hij
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hij' : (i : ℝ) < j := by exact_mod_cast hij
  have hi := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) Real.pi_pos.le
  have hj := mul_lt_mul_of_pos_right hij' Real.pi_pos
  have hp := pow_lt_pow_left₀ hj hi (by decide : 4 ≠ 0)
  unfold nearOriginSample
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_right hp (by positivity)

/-- The first eight samples enclose seven distinct roots strictly between the inner
saddle endpoint and zero. -/
theorem nearOrigin_seven_roots {n : ℕ} (hn : 6401 ≤ n) :
    ∃ e : Fin 7 ↪ ℝ, ∀ i,
      e i ∈ Ioo (-(nearOriginRadius n) ^ 2) 0 ∧ (durfeePolynomialReal n).IsRoot (e i) := by
  let x (i : Fin (7 + 1)) := nearOriginSample n (8 - i.val)
  have hm : StrictMono x := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    exact nearOrigin_sample_strictAnti (by omega : 0 < n) (by omega)
  have hx (i : Fin 8) : x i ≤ 0 := by
    unfold x nearOriginSample
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  have hp (i : Fin 8) :
      Real.sign ((durfeePolynomialReal n).eval (x i)) = (-1 : ℝ) ^ (8 - i.val) := by
    have hi := i.isLt
    exact nearOrigin_sign_firstEight (by omega) (by omega) (by omega)
  have hsign (i : Fin 7) :
      (durfeePolynomialReal n).eval (x i.castSucc) *
        (durfeePolynomialReal n).eval (x i.succ) < 0 := by
    have hindex : 8 - i.castSucc.val = 8 - i.succ.val + 1 := by
      have hi := i.isLt
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    have h := hp i.castSucc
    rw [hindex] at h
    exact mul_neg_of_consecutive_signs h (hp i.succ)
  obtain ⟨e, he⟩ := negativeRoots_of_alternating _ x hm hx hsign
  refine ⟨e, fun i => ⟨⟨?_, (he i).2.2.1⟩, (he i).2.2.2⟩⟩
  have hx0 : x 0 = -(nearOriginRadius n) ^ 2 := nearOrigin_sample_eight hn
  rw [← hx0]
  exact (hm.monotone (Fin.zero_le _)).trans_lt (he i).1

end DurfeeCCS.Step11
