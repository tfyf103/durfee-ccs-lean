module

public import DurfeeCCS.Step08.MidpointSinh
public import DurfeeCCS.Step08.SaddleFourier
public import DurfeeCCS.Step08.SaddleNormalization
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The uniform midpoint error at the closed-disk endpoint. -/

@[expose] public section
namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06 Filter

private theorem summable_shifted_reciprocal_sq (N : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / (((n + N + 1 : ℕ) : ℝ) ^ 2)) := by
  simpa only [Nat.add_assoc] using ((summable_nat_add_iff (N + 1)).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))))

private theorem tsum_shifted_reciprocal_sq_le {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, (1 : ℝ) / (((n + N + 1 : ℕ) : ℝ) ^ 2)) ≤ 1 / (N : ℝ) := by
  let f (n : ℕ) := (1 : ℝ) / (((n + N + 1 : ℕ) : ℝ) ^ 2)
  let g (n : ℕ) := (1 : ℝ) / ((n + N : ℕ) : ℝ)
  have hfg (n : ℕ) : f n ≤ g n - g (n + 1) := by
    have h : (0 : ℝ) < ((n + N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + N)
    simp only [f, g, Nat.cast_add, Nat.cast_one]
    push_cast at h
    rw [show (n : ℝ) + 1 + N = (n : ℝ) + N + 1 by ring]
    have h₁ : 0 < (n : ℝ) + N + 1 := by positivity
    have he : 1 / ((n : ℝ) + N) - 1 / ((n : ℝ) + N + 1) =
        1 / (((n : ℝ) + N) * ((n : ℝ) + N + 1)) := by
      field_simp [h.ne', h₁.ne']
      ring
    rw [he]
    apply div_le_div₀ (by norm_num) le_rfl (by positivity)
    nlinarith
  have hsum (m : ℕ) : (∑ n ∈ Finset.range m, f n) ≤ g 0 - g m := by
    induction m with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [hfg n]
  have ht := (summable_shifted_reciprocal_sq N).hasSum.tendsto_sum_nat
  refine le_of_tendsto ht (Eventually.of_forall fun m => ?_)
  have hgm : 0 ≤ g m := by dsimp [g]; positivity
  exact (hsum m).trans (by simpa only [g, Nat.zero_add] using (sub_le_self (g 0) hgm))

private noncomputable def midpointErrorMode (r θ : ℝ) (ζ : ℂ) (n : ℕ) : ℂ :=
  pairedLogMode r θ ζ n - saddleGCoeff r n * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ) / ζ

private theorem norm_saddleGMode_div_le (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1) (n : ℕ) :
    ‖saddleGCoeff r n * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ) / ζ‖ ≤
      2 / (((n + 1 : ℕ) : ℝ) ^ 2 * ‖ζ‖) := by
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_saddleGCoeff, ← div_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  refine (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (by norm_num) (pow_le_one₀ (abs_nonneg r) hr)) (by positivity)

private theorem norm_midpointErrorMode_le (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1)
    (hζ : 0 < ζ.re) (n : ℕ) :
    ‖midpointErrorMode r θ ζ n‖ ≤
      (2 * (1 + ‖ζ‖ / ζ.re) / ‖ζ‖) * (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hz₀ : 0 < ‖ζ‖ := lt_of_lt_of_le hζ (Complex.re_le_norm _)
  refine (norm_sub_le _ _).trans ((add_le_add (norm_pairedLogMode_le r θ hr hζ n)
    (norm_saddleGMode_div_le r θ hr n)).trans_eq ?_)
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hζ.ne', hz₀.ne', hn]
  ring

private theorem norm_midpointErrorMode_le_of_small (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1)
    (hζ : 0 < ζ.re) (n : ℕ) (hn : ((n + 1 : ℕ) : ℝ) * ‖ζ‖ ≤ Real.pi) :
    ‖midpointErrorMode r θ ζ n‖ ≤ 0.16 * ‖ζ‖ := by
  let k : ℕ := n + 1
  let z : ℂ := (k : ℂ) * ζ
  have hz : ‖z‖ = (k : ℝ) * ‖ζ‖ := by simp [z]
  have hzr : 0 < z.re := by
    simp only [z, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    have hk : (0 : ℝ) < k := by exact_mod_cast Nat.succ_pos n
    positivity
  have hb := norm_inv_two_mul_sinh_half_sub_inv_le (by rwa [hz]) hzr
  have hfac : midpointErrorMode r θ ζ n =
      (-2 * (-(r : ℂ) * I) ^ k / (k : ℂ) *
        (Real.cos ((k : ℝ) * θ) : ℂ)) *
          ((2 * Complex.sinh (z / 2))⁻¹ - z⁻¹) := by
    simp only [midpointErrorMode, pairedLogMode, pairedLogCoeff, saddleGCoeff, z, k,
      div_eq_mul_inv, mul_inv_rev, mul_sub, pow_two]
    ring
  rw [hfac, norm_mul]
  have hd : ‖-2 * (-(r : ℂ) * I) ^ k / (k : ℂ) * (Real.cos ((k : ℝ) * θ) : ℂ)‖ ≤
      2 / (k : ℝ) := by
    simp only [norm_mul, norm_div, norm_neg, norm_ofNat, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one, Complex.norm_natCast]
    refine (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)).trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (by norm_num) (pow_le_one₀ (abs_nonneg r) hr)) (by positivity)
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.succ_pos n
  refine (mul_le_mul hd hb (norm_nonneg _) (by positivity)).trans_eq ?_
  rw [hz]
  field_simp [hk.ne']
  ring

private theorem pairedLog_sub_saddleG_div_eq_tsum (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1)
    (hζ : 0 < ζ.re) :
    pairedLog r θ ζ - saddleG r θ / ζ = ∑' n : ℕ, midpointErrorMode r θ ζ n := by
  rw [pairedLog_eq_tsum_mode r θ hr hζ, saddleG_eq_cosineSeries r θ hr, ← tsum_div_const]
  have hs : Summable (fun n : ℕ =>
      ‖saddleGCoeff r n * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) : ℂ) / ζ‖) := by
    apply ((summable_shifted_reciprocal_sq 0).mul_left (2 / ‖ζ‖)).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    simpa only [Nat.add_zero, mul_one_div, div_div, mul_comm ‖ζ‖] using norm_saddleGMode_div_le r θ hr n
  exact ((summable_norm_pairedLogMode r θ hr hζ).of_norm.tsum_sub hs.of_norm).symm

/-- Uniform bound with the unrounded tail coefficient, as used on page 27. -/
theorem norm_pairedLog_sub_saddleG_div_le_pi_cutoff (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1)
    (hζ : 0 < ζ.re) (hζ₁ : ‖ζ‖ < Real.pi) :
    ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤
      0.51 + (2 / (Real.pi - ‖ζ‖)) * (1 + ‖ζ‖ / ζ.re) := by
  let N := ⌊Real.pi / ‖ζ‖⌋₊
  let c := 2 * (1 + ‖ζ‖ / ζ.re) / ‖ζ‖
  let f := midpointErrorMode r θ ζ
  have hp := Real.pi_pos
  have hz : 0 < ‖ζ‖ := hζ.trans_le (Complex.re_le_norm _)
  have hπN : (N : ℝ) ≤ Real.pi / ‖ζ‖ := Nat.floor_le (by positivity)
  have hNπ : Real.pi / ‖ζ‖ < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hN : 0 < N := by
    have h : (1 : ℝ) ≤ Real.pi / ‖ζ‖ := (le_div_iff₀ hz).mpr (by simpa using hζ₁.le)
    exact Nat.le_floor (by simpa using h)
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast hN
  have hNζ : Real.pi - ‖ζ‖ < (N : ℝ) * ‖ζ‖ := by
    have h := (div_lt_iff₀ hz).mp hNπ
    linarith [show ((N : ℝ) + 1) * ‖ζ‖ = (N : ℝ) * ‖ζ‖ + ‖ζ‖ by ring]
  have hfn : Summable (fun n : ℕ => ‖f n‖) :=
    ((summable_shifted_reciprocal_sq 0).mul_left c).of_nonneg_of_le (fun _ => norm_nonneg _)
      (by simpa only [Nat.add_zero] using norm_midpointErrorMode_le r θ hr hζ)
  have hfin : ‖∑ n ∈ Finset.range N, f n‖ ≤ 0.51 := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _n ∈ Finset.range N, 0.16 * ‖ζ‖ := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : ((n + 1 : ℕ) : ℝ) ≤ N := by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hn)
        have hz' := (le_div_iff₀ hz).mp (hn'.trans hπN)
        exact norm_midpointErrorMode_le_of_small r θ hr hζ n hz'
      _ = 0.16 * ((N : ℝ) * ‖ζ‖) := by simp; ring
      _ ≤ _ := by
        have h := (le_div_iff₀ hz).mp hπN
        linarith [Real.pi_lt_d2]
  have htail : ‖∑' n : ℕ, f (n + N)‖ ≤
      (2 / (Real.pi - ‖ζ‖)) * (1 + ‖ζ‖ / ζ.re) := by
    have hs := (summable_nat_add_iff N).mpr hfn
    have hg := (summable_shifted_reciprocal_sq N).mul_left c
    refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum
      (fun n => norm_midpointErrorMode_le r θ hr hζ (n + N)) hg).trans ?_)
    simp only [tsum_mul_left]
    refine (mul_le_mul_of_nonneg_left (tsum_shifted_reciprocal_sq_le hN) (by positivity)).trans ?_
    have hNum : (2 : ℝ) / (‖ζ‖ * (N : ℝ)) ≤ 2 / (Real.pi - ‖ζ‖) :=
      div_le_div_of_nonneg_left (by norm_num) (sub_pos.mpr hζ₁)
        (by simpa [mul_comm] using hNζ.le)
    calc
      _ = (2 / (‖ζ‖ * (N : ℝ))) * (1 + ‖ζ‖ / ζ.re) := by
        field_simp [hz.ne', hN₀.ne', hζ.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hNum (by positivity)
  rw [pairedLog_sub_saddleG_div_eq_tsum r θ hr hζ, ← hfn.of_norm.sum_add_tsum_nat_add N]
  exact (norm_add_le _ _).trans (add_le_add hfin htail)

/-- The uniform midpoint bound in equation (45), in terms of the norm and real part of ζ. -/
theorem norm_pairedLog_sub_saddleG_div_le_uniform (r θ : ℝ) {ζ : ℂ} (hr : |r| ≤ 1)
    (hζ : 0 < ζ.re) (hζ₁ : ‖ζ‖ ≤ 0.228) :
    ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤ 0.51 + 0.69 * (1 + ‖ζ‖ / ζ.re) := by
  have hπ := Real.pi_gt_d4
  have hs : ‖ζ‖ < Real.pi := by linarith
  have h : (2 : ℝ) / (Real.pi - ‖ζ‖) ≤ 0.69 := by
    rw [div_le_iff₀ (sub_pos.mpr hs)]
    linarith
  refine (norm_pairedLog_sub_saddleG_div_le_pi_cutoff r θ hr hζ hs).trans ?_
  have h0 : 0 ≤ 1 + ‖ζ‖ / ζ.re :=
    add_nonneg zero_le_one (div_nonneg (norm_nonneg ζ) hζ.le)
  have h' := mul_le_mul_of_nonneg_right h h0
  linarith only [h']

/-- Equation (45) for (ζ=u(1+iη)). -/
theorem norm_pairedLog_sub_saddleG_div_le_45 (r θ u η : ℝ) (hr : |r| ≤ 1) (hu : 0 < u)
    (hsize : ‖(u : ℂ) * (1 + (η : ℂ) * I)‖ ≤ 0.228) :
    let ζ : ℂ := (u : ℂ) * (1 + (η : ℂ) * I)
    ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤ 0.51 + 0.69 * (1 + Real.sqrt (1 + η ^ 2)) := by
  let α := 1 + (η : ℂ) * I
  let ζ := (u : ℂ) * α
  have hζr : ζ.re = u := by simp [ζ, α, Complex.mul_re]
  have hα : ‖α‖ = Real.sqrt (1 + η ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [α, Complex.mul_re, Complex.mul_im, pow_two]
  have hζn : ‖ζ‖ / ζ.re = Real.sqrt (1 + η ^ 2) := by
    rw [hζr, norm_mul, hα, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    field_simp [hu.ne']
  rw [← hζn]
  exact norm_pairedLog_sub_saddleG_div_le_uniform r θ hr (hζr.symm ▸ hu) hsize

/-- The first-saddle radius satisfies the cutoff used in (45) on the full |η| ≤ 16 arc. -/
theorem norm_saddleU_mul_one_add_im_le {n : ℕ} (hn : 6400 ≤ n) {r η : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hη : |η| ≤ 16) :
    ‖(saddleU n r : ℂ) * (1 + (η : ℂ) * I)‖ ≤ 0.228 := by
  let α := 1 + (η : ℂ) * I
  have hn' : 0 < n := by omega
  have hu := saddleU_pos hn' hr
  have hu₁ : saddleU n r ≤ Step07.firstSaddleU0 1 :=
    Step07.firstSaddleRadius_leU0 hn hr hr₁ (by norm_num)
  have hu₂ : saddleU n r ≤ 0.014154 := by
    refine hu₁.trans ?_
    unfold Step07.firstSaddleU0
    exact (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  have hα : ‖α‖ ^ 2 = 1 + η ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [α, Complex.mul_re, Complex.mul_im, pow_two]
  have hα₁ : ‖α‖ ≤ 16.04 := by
    apply le_of_sq_le_sq _ (by norm_num)
    have hb := pow_le_pow_left₀ (abs_nonneg η) hη 2
    rw [sq_abs] at hb
    rw [hα]
    linarith only [hb]
  change ‖(saddleU n r : ℂ) * α‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  exact (mul_le_mul hu₂ hα₁ (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem norm_pairedLog_sub_saddleG_div_le_45_saddle {n : ℕ} (hn : 6400 ≤ n) {r θ η : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hη : |η| ≤ 16) :
    let ζ : ℂ := (saddleU n r : ℂ) * (1 + (η : ℂ) * I)
    ‖pairedLog r θ ζ - saddleG r θ / ζ‖ ≤ 0.51 + 0.69 * (1 + Real.sqrt (1 + η ^ 2)) := by
  have hn' : 0 < n := by omega
  exact norm_pairedLog_sub_saddleG_div_le_45 r θ _ η (by simpa [abs_of_pos hr] using hr₁)
    (saddleU_pos hn' hr) (norm_saddleU_mul_one_add_im_le hn hr hr₁ hη)

end DurfeeCCS.Step08
