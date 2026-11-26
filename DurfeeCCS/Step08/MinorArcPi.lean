module

public import DurfeeCCS.Step08.MinorArcLogBounds
public import DurfeeCCS.Step06.Dilog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The π-centered minor-arc bound from the even and odd frequencies. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06 DurfeeCCS.Step07

private theorem hasSum_piArc_even {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    HasSum (fun k : ℕ => 2 * r ^ (2 * k + 1) / ((2 * k + 2 : ℕ) : ℝ) ^ 2)
      ((principalDilog ((r ^ 2 : ℝ) : ℂ)).re / (2 * r)) := by
  have hSq : ‖((r ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)] using
      pow_le_one₀ hr.le hr₁ (n := 2)
  have h := ((Complex.reCLM.hasSum (principalDilog_hasSum hSq)).div_const (2 * r))
  refine h.congr_fun ?_
  intro k
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    Complex.reCLM_apply, Complex.ofReal_re]
  rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
  push_cast
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  field_simp [hr.ne', hk.ne']
  ring

private theorem summable_piArc_oddTail {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    Summable (fun k : ℕ => 2 * r ^ (2 * k + 32) / (2 * (k : ℝ) + 33) ^ 2) := by
  have hs := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))).comp_injective
    (i := fun k : ℕ => 2 * k + 33) (by intro x y h; change 2 * x + 33 = 2 * y + 33 at h; omega)
  have h₂ : Summable (fun k : ℕ => (2 : ℝ) / (2 * (k : ℝ) + 33) ^ 2) := by
    simpa only [Function.comp_def, mul_one_div, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hs.mul_left (2 : ℝ)
  apply h₂.of_nonneg_of_le (fun _ => by positivity)
  intro k
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ hr hr₁ (n := 2 * k + 32)) (by norm_num : (0 : ℝ) ≤ 2)

/-- The bound (V_{r₀}(u)) on the π-centered minor arc in §3.5. -/
theorem norm_pairedLog_pi_arc {r r₀ u : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀) (hr₁ : r₀ ≤ 1)
    (hu : 0 < u) (θ v : ℝ)
    (hs : ∀ k ∈ Finset.range 16, 0.466 ≤ |Real.sin ((((2 * k + 1 : ℕ) : ℝ) * v) / 2)|) :
    ‖pairedLog r θ (verticalPoint u v)‖ / (r / u) ≤ firstSaddlePiArc r₀ u := by
  let f := logScaledMode r θ u v
  have hr' : r ≤ 1 := hr₀.trans hr₁
  have habs : |r| ≤ 1 := by simpa [abs_of_pos hr] using hr'
  have hr0 : 0 < r₀ := hr.trans_le hr₀
  have hS : Summable f := summable_logScaledMode habs hu θ v
  have hEven : Summable (fun k : ℕ => f (2 * k)) :=
    hS.comp_injective (by intro x y h; change 2 * x = 2 * y at h; omega)
  have hOdd : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hS.comp_injective (by intro x y h; change 2 * x + 1 = 2 * y + 1 at h; omega)
  have hTail : Summable (fun k : ℕ => f (2 * (k + 16))) :=
    hEven.comp_injective (add_left_injective 16)
  have hEv : (∑' k : ℕ, f (2 * k + 1)) ≤ (principalDilog ((r₀ ^ 2 : ℝ) : ℂ)).re / (2 * r₀) := by
    have hsum := hasSum_piArc_even hr0 hr₁
    rw [← hsum.tsum_eq]
    apply hOdd.tsum_le_tsum _ hsum.summable
    intro k
    exact logScaledMode_le_radius hr hr₀ hu θ v (2 * k + 1)
  have hHd : (∑ k ∈ Finset.range 16, f (2 * k)) ≤
      u / 0.466 * (∑ k ∈ Finset.range 16, r₀ ^ (2 * k) / ((2 * k + 1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum
      (fun k hk => logScaledMode_le_sin hr hr₀ hu (by norm_num) θ v (2 * k) (hs k hk))
  have hTl : (∑' k : ℕ, f (2 * (k + 16))) ≤ firstSaddleOddTail r₀ := by
    refine (hTail.tsum_le_tsum ?_ (summable_piArc_oddTail hr0.le hr₁)).trans
      (firstSaddleOddTail_series_le hr0.le hr₁)
    intro k
    have h := logScaledMode_le_radius hr hr₀ hu θ v (2 * (k + 16))
    convert h using 1
    rw [Nat.mul_add]
    push_cast
    ring
  have hParity : (∑' k : ℕ, f (2 * k)) + (∑' k : ℕ, f (2 * k + 1)) = ∑' k : ℕ, f k :=
    tsum_even_add_odd hEven hOdd
  refine (norm_pairedLog_le_logScaledMode hr hr' hu θ v).trans ?_
  change (∑' k : ℕ, f k) ≤ _
  rw [← hParity, ← hEven.sum_add_tsum_nat_add 16]
  unfold firstSaddlePiArc
  exact (add_le_add (add_le_add hHd hTl) hEv).trans_eq (by ac_rfl)

end DurfeeCCS.Step08
