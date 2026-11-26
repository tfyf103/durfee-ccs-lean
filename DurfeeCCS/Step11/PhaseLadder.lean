module

public import DurfeeCCS.Scalars
public import DurfeeCCS.SignRoots
public import DurfeeCCS.Step09.MidRangeOverlap
public import DurfeeCCS.Step10.OuterSamples
public import DurfeeCCS.Step11.NearOriginSigned
import Mathlib.Tactic

/-! First phase crossings and the middle interval in the proof of Theorem 1.2. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step11

open Polynomial Real Set Step06 Step08 Step09 Step10

theorem durfeeNegativeValue_eq_eval (n : ℕ) (r : ℝ) :
    durfeeNegativeValue n r = (durfeePolynomialReal n).eval (-(r ^ 2)) := by
  rw [durfeeNegativeValue, durfeePolynomialReal, Polynomial.eval₂_eq_eval_map]

/-- For a level strictly between the endpoint values, its first hit is in the open interval. -/
theorem firstPhaseHit_mem_Ioo {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (hlevel : c ∈ Ioo (f a) (f b)) :
    firstPhaseHit f a b c ∈ Ioo a b := by
  obtain ⟨r, hr, heq⟩ := intermediate_value_Ioo hab hc hlevel
  have hfirst := firstPhaseHit_spec hab hc hlevel.1.le hlevel.2.le
  have hval : f (firstPhaseHit f a b c) = c := hfirst.1.2
  refine ⟨lt_of_le_of_ne hfirst.1.1.1 ?_, ?_⟩
  · intro he
    exact hlevel.1.ne (by rw [he]; exact hval)
  · exact (hfirst.2 ⟨Ioo_subset_Icc_self hr, heq⟩).trans_lt hr.2

/-- First hits are strictly ordered by their levels. The phase itself only needs continuity. -/
theorem strictMonoOn_firstPhaseHit {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) :
    StrictMonoOn (firstPhaseHit f a b) (Ioo (f a) (f b)) := by
  intro c hc' d hd' hcd
  have hcFirst := firstPhaseHit_spec hab hc hc'.1.le hc'.2.le
  have hdFirst := firstPhaseHit_spec hab hc hd'.1.le hd'.2.le
  have hdf : f (firstPhaseHit f a b d) = d := hdFirst.1.2
  have hcont : ContinuousOn f (Icc a (firstPhaseHit f a b d)) :=
    hc.mono (Icc_subset_Icc le_rfl hdFirst.1.1.2)
  obtain ⟨r, hr, heq⟩ := intermediate_value_Ioo hdFirst.1.1.1 hcont
    ⟨hc'.1, hcd.trans_eq hdf.symm⟩
  exact (hcFirst.2 ⟨⟨hr.1.le, hr.2.le.trans hdFirst.1.1.2⟩, heq⟩).trans_lt hr.2

/-- The first radius at which the saddle phase attains kπ between the two endpoints. -/
def middlePhaseRadius (n : ℕ) (rMinus rPlus : ℝ) (k : ℕ) : ℝ :=
  firstPhaseHit (saddlePhase n) rMinus rPlus ((k : ℝ) * π)

private theorem middle_phase_level {n d₀ k : ℕ} {rMinus rPlus : ℝ}
    (hphaseMinus : saddlePhase n rMinus < 9 * π)
    (hphasePlus : ((d₀ : ℝ) - 1) * π < saddlePhase n rPlus) (hk₁ : 9 ≤ k) (hk₂ : k < d₀) :
    (k : ℝ) * π ∈ Ioo (saddlePhase n rMinus) (saddlePhase n rPlus) := by
  refine ⟨hphaseMinus.trans_le (mul_le_mul_of_nonneg_right ?_ pi_pos.le),
    (mul_le_mul_of_nonneg_right ?_ pi_pos.le).trans_lt hphasePlus⟩
  · exact_mod_cast hk₁
  · have hk' : (k + 1 : ℕ) ≤ d₀ := by omega
    have hk'' : (k : ℝ) + 1 ≤ d₀ := by exact_mod_cast hk'
    linarith only [hk'']

/-- The radius for an interior index is the least phase crossing, strictly inside the interval. -/
theorem middlePhaseRadius_spec {n d₀ k : ℕ} {rMinus rPlus : ℝ}
    (hrMinus : 0 < rMinus) (hr : rMinus ≤ rPlus)
    (hphaseMinus : saddlePhase n rMinus < 9 * π)
    (hphasePlus : ((d₀ : ℝ) - 1) * π < saddlePhase n rPlus) (hk₁ : 9 ≤ k) (hk₂ : k < d₀) :
    IsLeast (Icc rMinus rPlus ∩ saddlePhase n ⁻¹' {((k : ℝ) * π)})
      (middlePhaseRadius n rMinus rPlus k) ∧
    middlePhaseRadius n rMinus rPlus k ∈ Ioo rMinus rPlus := by
  have hc : ContinuousOn (saddlePhase n) (Icc rMinus rPlus) :=
    (continuousOn_saddlePhase n).mono (fun _ hx ↦ hrMinus.trans_le hx.1)
  have hlevel := middle_phase_level hphaseMinus hphasePlus hk₁ hk₂
  exact ⟨firstPhaseHit_spec hr hc hlevel.1.le hlevel.2.le, firstPhaseHit_mem_Ioo hr hc hlevel⟩

theorem strictMonoOn_middlePhaseRadius {n d₀ : ℕ} {rMinus rPlus : ℝ}
    (hrMinus : 0 < rMinus) (hr : rMinus ≤ rPlus)
    (hphaseMinus : saddlePhase n rMinus < 9 * π)
    (hphasePlus : ((d₀ : ℝ) - 1) * π < saddlePhase n rPlus) :
    StrictMonoOn (middlePhaseRadius n rMinus rPlus) (Ico 9 d₀) := by
  intro i hi j hj hij
  have hc : ContinuousOn (saddlePhase n) (Icc rMinus rPlus) :=
    (continuousOn_saddlePhase n).mono (fun _ hx ↦ hrMinus.trans_le hx.1)
  exact strictMonoOn_firstPhaseHit hr hc
    (middle_phase_level hphaseMinus hphasePlus hi.1 hi.2)
    (middle_phase_level hphaseMinus hphasePlus hj.1 hj.2)
    (mul_lt_mul_of_pos_right (by exact_mod_cast hij) pi_pos)

/-- The overlapping saddle estimates give the sign whenever the phase is an integer multiple
of π throughout the full interval. -/
theorem middle_sign_at_phase {n k : ℕ} {rMinus rPlus r : ℝ} (hn : 6400 ≤ n)
    (hrMinus : 0 < rMinus) (hrPlus : rPlus ≤ exp 1 * sqrt (n : ℝ))
    (hscale : 4 * π ≤ sqrt ((n : ℝ) * rMinus)) (hr : r ∈ Icc rMinus rPlus)
    (hphase : saddlePhase n r = (k : ℝ) * π) :
    Real.sign ((durfeePolynomialReal n).eval (-(r ^ 2))) = (-1 : ℝ) ^ k := by
  rw [← durfeeNegativeValue_eq_eval]
  exact saddle_ranges_sign_at_phase hn (hrMinus.trans_le hr.1) (hr.2.trans hrPlus)
    (hscale.trans (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hr.1 (Nat.cast_nonneg n)))) hphase

/-- The sign statement also holds for every integer phase index in the manuscript. -/
theorem middle_sign_at_integer_phase {n : ℕ} {k : ℤ} {rMinus rPlus r : ℝ} (hn : 6400 ≤ n)
    (hrMinus : 0 < rMinus) (hrPlus : rPlus ≤ exp 1 * sqrt (n : ℝ))
    (hscale : 4 * π ≤ sqrt ((n : ℝ) * rMinus)) (hr : r ∈ Icc rMinus rPlus)
    (hphase : saddlePhase n r = (k : ℝ) * π) :
    Real.sign ((durfeePolynomialReal n).eval (-(r ^ 2))) = (-1 : ℝ) ^ k := by
  have hcos : cos (saddlePhase n r) = (-1 : ℝ) ^ k := hphase ▸ cos_int_mul_pi k
  have hext : cos (saddlePhase n r) = 1 ∨ cos (saddlePhase n r) = -1 := by
    rw [← abs_eq (by norm_num : (0 : ℝ) ≤ 1), hphase]
    exact abs_cos_int_mul_pi k
  rw [← durfeeNegativeValue_eq_eval, ← hcos]
  by_cases hunit : r ≤ 1
  · exact firstSaddle_sign_at_cosine_extremum hn (hrMinus.trans_le hr.1) hunit
      (hscale.trans (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hr.1 (Nat.cast_nonneg n)))) hext
  · exact midSaddle_sign_at_cosine_extremum hn (le_of_lt (lt_of_not_ge hunit)) (hr.2.trans hrPlus) hext


/-- The two endpoints and their intervening phase crossings supply one negative root
for every pair of consecutive samples. -/
theorem middleRoots_of_endpoint_phase {n d₀ : ℕ} {rMinus rPlus : ℝ} (hn : 6400 ≤ n)
    (hd : 9 ≤ d₀) (hrMinus : 0 < rMinus) (hr : rMinus < rPlus)
    (hrPlus : rPlus ≤ exp 1 * sqrt (n : ℝ)) (hscale : 4 * π ≤ sqrt ((n : ℝ) * rMinus))
    (hphaseMinus : saddlePhase n rMinus < 9 * π)
    (hphasePlus : ((d₀ : ℝ) - 1) * π < saddlePhase n rPlus)
    (hsignMinus : 0 < (durfeePolynomialReal n).eval (-(rMinus ^ 2)))
    (hsignPlus : Real.sign ((durfeePolynomialReal n).eval (-(rPlus ^ 2))) = (-1 : ℝ) ^ d₀) :
    ∃ roots : Fin (d₀ - 8) ↪ ℝ, ∀ i,
      roots i ∈ Ioo (-(rPlus ^ 2)) (-(rMinus ^ 2)) ∧ (durfeePolynomialReal n).IsRoot (roots i) := by
  let radius (k : ℕ) : ℝ :=
    if k = 8 then rMinus else if k = d₀ then rPlus else middlePhaseRadius n rMinus rPlus k
  have radius_start : radius 8 = rMinus := by simp [radius]
  have radius_end : radius d₀ = rPlus := by simp [radius, show d₀ ≠ 8 by omega]
  have radius_middle {k : ℕ} (hk₁ : 9 ≤ k) (hk₂ : k < d₀) :
      radius k = middlePhaseRadius n rMinus rPlus k := by
    simp [radius, show k ≠ 8 by omega, hk₂.ne]
  have phase_at_middle {k : ℕ} (hk₁ : 9 ≤ k) (hk₂ : k < d₀) :
      saddlePhase n (radius k) = (k : ℝ) * π := by
    rw [radius_middle hk₁ hk₂]
    exact (middlePhaseRadius_spec hrMinus hr.le hphaseMinus hphasePlus hk₁ hk₂).1.1.2
  have radius_open {k : ℕ} (hk₁ : 9 ≤ k) (hk₂ : k < d₀) : radius k ∈ Ioo rMinus rPlus := by
    rw [radius_middle hk₁ hk₂]
    exact (middlePhaseRadius_spec hrMinus hr.le hphaseMinus hphasePlus hk₁ hk₂).2
  have radius_closed {k : ℕ} (hk : k ∈ Icc 8 d₀) : radius k ∈ Icc rMinus rPlus := by
    by_cases h₁ : k = 8
    · simpa only [h₁, radius_start] using left_mem_Icc.mpr hr.le
    by_cases h₂ : k = d₀
    · simpa only [h₂, radius_end] using right_mem_Icc.mpr hr.le
    exact Ioo_subset_Icc_self (radius_open (by have := hk.1; omega) (lt_of_le_of_ne hk.2 h₂))
  have radius_strict : StrictMonoOn radius (Icc 8 d₀) := by
    intro i hi j hj hij
    have hi₁ := hi.1
    have hj₂ := hj.2
    by_cases h₁ : i = 8
    · rw [h₁, radius_start]
      by_cases h₂ : j = d₀
      · rwa [h₂, radius_end]
      · exact (radius_open (by omega) (lt_of_le_of_ne hj₂ h₂)).1
    by_cases h₂ : j = d₀
    · rw [h₂, radius_end]
      exact (radius_open (by omega) (by omega)).2
    have h₁' : i ∈ Ico 9 d₀ := ⟨by omega, by omega⟩
    have h₂' : j ∈ Ico 9 d₀ := ⟨by omega, by omega⟩
    rw [radius_middle h₁'.1 h₁'.2, radius_middle h₂'.1 h₂'.2]
    exact strictMonoOn_middlePhaseRadius hrMinus hr.le hphaseMinus hphasePlus h₁' h₂' hij
  have value_sign {k : ℕ} (hk : k ∈ Icc 8 d₀) :
      Real.sign ((durfeePolynomialReal n).eval (-(radius k ^ 2))) = (-1 : ℝ) ^ k := by
    by_cases h₁ : k = 8
    · rw [h₁, radius_start, Real.sign_of_pos hsignMinus]
      norm_num
    by_cases h₂ : k = d₀
    · simpa only [h₂, radius_end] using hsignPlus
    exact middle_sign_at_phase hn hrMinus hrPlus hscale (radius_closed hk)
      (phase_at_middle (by have := hk.1; omega) (lt_of_le_of_ne hk.2 h₂))
  let m := d₀ - 8
  let index (i : Fin (m + 1)) := d₀ - i.val
  let point (i : Fin (m + 1)) : ℝ := -(radius (index i) ^ 2)
  have index_bounds (i : Fin (m + 1)) : index i ∈ Icc 8 d₀ := by
    have hi := i.isLt
    dsimp only [m] at hi
    dsimp only [index]
    exact ⟨by omega, Nat.sub_le _ _⟩
  have radius_pos (i : Fin (m + 1)) : 0 < radius (index i) :=
    hrMinus.trans_le (radius_closed (index_bounds i)).1
  have point_strict : StrictMono point := by
    intro i j hij
    have hval : i.val < j.val := hij
    have hlt : index j < index i := by
      have hj := j.isLt
      dsimp only [m] at hj
      dsimp only [index]
      omega
    exact neg_lt_neg ((sq_lt_sq₀ (radius_pos j).le (radius_pos i).le).2
      (radius_strict (index_bounds j) (index_bounds i) hlt))
  have point_sign (i : Fin (m + 1)) :
      Real.sign ((durfeePolynomialReal n).eval (point i)) = (-1 : ℝ) ^ index i :=
    value_sign (index_bounds i)
  have consecutive_signs (i : Fin m) :
      (durfeePolynomialReal n).eval (point i.castSucc) *
        (durfeePolynomialReal n).eval (point i.succ) < 0 := by
    have hi := i.isLt
    dsimp only [m] at hi
    have hind : index i.castSucc = index i.succ + 1 := by
      simp only [index, Fin.val_castSucc, Fin.val_succ]
      omega
    exact mul_neg_of_consecutive_signs ((point_sign i.castSucc).trans (by rw [hind])) (point_sign i.succ)
  obtain ⟨roots, hroots⟩ := negativeRoots_of_alternating (durfeePolynomialReal n) point
    point_strict (by intro i; exact neg_nonpos.mpr (sq_nonneg _)) consecutive_signs
  have point_zero : point 0 = -(rPlus ^ 2) := by
    simp only [point, index, Fin.val_zero, Nat.sub_zero, radius_end]
  have point_last : point (Fin.last m) = -(rMinus ^ 2) := by
    have hend : d₀ - m = 8 := by dsimp only [m]; omega
    simp only [point, index, Fin.val_last, hend, radius_start]
  refine ⟨roots, fun i => ⟨⟨?_, ?_⟩, (hroots i).2.2.2⟩⟩
  · rw [← point_zero]
    exact (point_strict.monotone (Fin.zero_le _)).trans_lt (hroots i).1
  · rw [← point_last]
    exact (hroots i).2.1.trans_le (point_strict.monotone (Fin.le_last i.succ))

end DurfeeCCS.Step11
