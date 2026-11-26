module

public import DurfeeCCS.Step06.SaddleComponents
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Alternating series for the two real components of the saddle. -/

@[expose] public section

namespace DurfeeCCS.Step07

open Complex Finset Filter Set
open scoped Real Topology
open DurfeeCCS.Step06

private theorem negSquare_mem_dilogCut (r : ℝ) : -(r : ℂ)^2 ∈ dilogCut := by
  apply mem_dilogCut_iff.mpr
  left
  rw [← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re]
  nlinarith

private theorem dilog_negImagCut (r : ℝ) : -(r : ℂ) * I ∈ dilogCut := by
  exact mem_dilogCut_iff.mpr (Or.inl (by simp))

private theorem norm_negImag (r : ℝ) : ‖-(r : ℂ) * I‖ = |r| := by
  simp

private theorem phaseSquare_re (r : ℝ) :
    (saddlePhaseSquare r).re = -(principalDilog (-(r : ℂ)^2)).re / 2 := by
  simp only [saddlePhaseSquare, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.re_ofNat, Complex.im_ofNat, neg_zero, zero_mul, sub_zero]
  rw [principalDilog_negImag_re]
  ring

private theorem phaseSquare_im (r : ℝ) :
    (saddlePhaseSquare r).im = -2 * (principalDilog (-(r : ℂ) * I)).im := by
  simp [saddlePhaseSquare, Complex.mul_im]

/-- A uniform alternating-series coefficient with spacing one or two. -/
noncomputable def saddleCoeff (m : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  x ^ (m * k + 1) / ((m * k + 1 : ℕ) : ℝ)^2

private theorem saddleCoeff_antitone (m : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (saddleCoeff m x) := by
  intro i j hij
  have hm : m * i + 1 ≤ m * j + 1 := by gcongr
  have hcast : (((m * i + 1 : ℕ) : ℝ)) ≤ (((m * j + 1 : ℕ) : ℝ)) := by exact_mod_cast hm
  unfold saddleCoeff
  exact div_le_div₀ (by positivity) (pow_le_pow_of_le_one hx hx1 hm) (by positivity)
    (by gcongr)

private theorem dilog_neg_hasSum {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    HasSum (fun k => (-1) ^ k * saddleCoeff 1 x k)
      (-(principalDilog (-(x : ℂ))).re) := by
  have hn : ‖-(x : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg hx] using hx1
  have h := (Complex.reCLM.hasSum (principalDilog_hasSum hn)).neg
  change HasSum (fun k : ℕ => -((-(x : ℂ)) ^ (k+1) / (((k+1 : ℕ) : ℂ)^2)).re)
    (-(principalDilog (-(x : ℂ))).re) at h
  convert h using 1
  ext k
  simp only [saddleCoeff, one_mul]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_pow, ← Complex.ofReal_div]
  change _ = -(((-x) ^ (k+1)) / ((↑(k+1) : ℝ)^2))
  rw [show -x = (-1) * x by ring, mul_pow, pow_succ (-1 : ℝ), mul_neg_one]
  ring

private theorem negImag_pow_odd (x : ℝ) (k : ℕ) :
    (-(x : ℂ) * I) ^ (2*k+1) =
      ((↑(((-1 : ℝ) ^ k) * x ^ (2*k+1)) : ℂ) * (-I)) := by
  rw [show -(x : ℂ) * I = (x : ℂ) * (-I) by ring, mul_pow]
  rw [pow_succ (-I), pow_mul, neg_sq, Complex.I_sq]
  push_cast
  ring

private theorem negImag_pow_even (x : ℝ) (k : ℕ) :
    ((-(x : ℂ) * I) ^ (2*k+2)).im = 0 := by
  rw [show -(x : ℂ) * I = (x : ℂ) * (-I) by ring, mul_pow]
  rw [show 2*k+2 = 2*(k+1) by omega, pow_mul (-I), neg_sq, Complex.I_sq]
  rw [← Complex.ofReal_pow, show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact Complex.ofReal_im _

private theorem dilog_negImag_hasSum {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    HasSum (fun k => (-1) ^ k * saddleCoeff 2 x k)
      (-(principalDilog (-(x : ℂ) * I)).im) := by
  have hn : ‖-(x : ℂ) * I‖ ≤ 1 := by rw [norm_negImag, abs_of_nonneg hx]; exact hx1
  let f (k : ℕ) : ℝ := -((-(x : ℂ) * I) ^ (k + 1) / (((k + 1 : ℕ) : ℂ)^2)).im
  have hs : HasSum f (-(principalDilog (-(x : ℂ) * I)).im) :=
    (Complex.imCLM.hasSum (principalDilog_hasSum hn)).neg
  have he (k : ℕ) : f (2*k) = (-1)^k * saddleCoeff 2 x k := by
    simp only [f, negImag_pow_odd, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
      Complex.div_ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, Complex.neg_re, Complex.I_im, Complex.I_re, neg_zero, zero_mul, add_zero,
      mul_neg_one, neg_div, neg_neg, saddleCoeff]
    ring
  have ho (k : ℕ) : f (2*k+1) = 0 := by
    simp only [f, show 2*k+1+1 = 2*k+2 by omega, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
      Complex.div_ofReal_im, negImag_pow_even, zero_div, neg_zero]
  have hEven : Summable (fun k => f (2*k)) :=
    hs.summable.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have hOdd : HasSum (fun k => f (2*k+1)) 0 := by simpa only [ho] using hasSum_zero
  have hadd := hEven.hasSum.even_add_odd hOdd
  have heq := hadd.unique hs
  rw [add_zero] at heq
  rw [← heq]
  simpa only [he] using hEven.hasSum

private theorem alternating_bounds (m : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : HasSum (fun k => (-1)^k * saddleCoeff m x k) y) (N : ℕ) :
    (∑ k ∈ range (2*N), (-1)^k * saddleCoeff m x k) ≤ y ∧
    y ≤ (∑ k ∈ range (2*N+1), (-1)^k * saddleCoeff m x k) := by
  have ht := hy.tendsto_sum_nat
  exact ⟨(saddleCoeff_antitone m hx hx1).alternating_series_le_tendsto ht N,
    (saddleCoeff_antitone m hx hx1).tendsto_le_alternating_series ht N⟩

theorem dilog_negImag_le_self {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    -(principalDilog (-(x : ℂ) * I)).im ≤ x := by
  simpa [saddleCoeff] using (alternating_bounds 2 hx h1 (dilog_negImag_hasSum hx h1) 0).2

theorem dilog_neg_real_le_self {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    -(principalDilog (-(x : ℂ))).re ≤ x := by
  simpa [saddleCoeff] using (alternating_bounds 1 hx h1 (dilog_neg_hasSum hx h1) 0).2

theorem dilog_neg_real_re_nonpos {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    (principalDilog (-(x : ℂ))).re ≤ 0 := by
  have h := (alternating_bounds 1 hx h1 (dilog_neg_hasSum hx h1) 0).1
  simp at h
  linarith

private theorem inv_negImag (r : ℝ) (hr : 0 < r) :
    (-(r : ℂ) * I)⁻¹ = (r⁻¹ : ℝ) * I := by
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.ofReal_inv]
  apply inv_eq_of_mul_eq_one_right
  field_simp [hc]
  linear_combination -Complex.I_sq

private theorem dilog_negImag_im_conj {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (principalDilog ((r : ℂ) * I)).im = -(principalDilog (-(r : ℂ) * I)).im := by
  have hn : ‖-(r : ℂ) * I‖ ≤ 1 := by rw [norm_negImag, abs_of_nonneg hr]; exact hr1
  have hn' : ‖(r : ℂ) * I‖ ≤ 1 := by simpa [← neg_mul] using hn
  have h := (RCLike.hasSum_conj' ℂ).2 (principalDilog_hasSum hn)
  have heq : (fun n : ℕ => starRingEnd ℂ ((-(r : ℂ) * I) ^ (n+1) / (((n+1 : ℕ) : ℂ)^2))) =
      fun n : ℕ => ((r : ℂ) * I) ^ (n+1) / (((n+1 : ℕ) : ℂ)^2) := by
    funext n
    simp
  change HasSum (fun n : ℕ => starRingEnd ℂ ((-(r : ℂ) * I) ^ (n+1) / (((n+1 : ℕ) : ℂ)^2))) _ at h
  rw [heq] at h
  simpa using congrArg Complex.im ((principalDilog_hasSum hn').unique h)

/-- Reduce the real component at radius at least one to a negative real argument in the unit disk. -/
theorem phaseSquare_re_exp (t : ℝ) :
    (saddlePhaseSquare (Real.exp t)).re =
      Real.pi^2/12 + t^2 + (principalDilog (-(↑(Real.exp (-2*t)) : ℂ))).re / 2 := by
  let r := Real.exp t
  have hr : 0 < r := Real.exp_pos _
  have hz : -(r : ℂ)^2 ∈ dilogInvCut := by
    apply mem_dilogInvCut_iff.mpr
    left
    rw [← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re]
    exact neg_neg_of_pos (sq_pos_of_pos hr)
  have hl : Complex.log (-(-(r : ℂ)^2)) = (2*t : ℝ) := by
    rw [neg_neg, ← Complex.ofReal_pow, ← Complex.ofReal_log (sq_nonneg r),
      Real.log_pow, show Real.log r = t by exact Real.log_exp t]
    norm_num
  have hi : (-(r : ℂ)^2)⁻¹ = -(↑(Real.exp (-2*t)) : ℂ) := by
    rw [inv_neg, ← inv_pow, ← Complex.ofReal_inv, show r⁻¹ = Real.exp (-t) by exact
      (Real.exp_neg t).symm, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hn := congrArg Complex.re (principalDilog_inversion hz)
  rw [hl, hi] at hn
  rw [phaseSquare_re]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
    ← Complex.ofReal_pow, Complex.ofReal_re] at hn
  change -(principalDilog (-(r : ℂ)^2)).re/2 = _
  rw [← Complex.ofReal_pow]
  ring_nf at hn ⊢
  linarith

/-- Reduce the imaginary component at radius at least one to a positive imaginary argument in the unit disk. -/
theorem phaseSquare_im_exp {t : ℝ} (ht : 0 ≤ t) :
    (saddlePhaseSquare (Real.exp t)).im =
      Real.pi*t - 2*(principalDilog (-(↑(Real.exp (-t)) : ℂ)*I)).im := by
  let r := Real.exp t
  have hr : 0 < r := Real.exp_pos _
  have hz : -(r : ℂ)*I ∈ dilogInvCut :=
    mem_dilogInvCut_iff.mpr (Or.inr (by simpa [Complex.mul_im] using hr.ne'))
  have hl : Complex.log (-(-(r : ℂ)*I)) = (t : ℂ) + (Real.pi / 2)*I := by
    rw [neg_mul, neg_neg, Complex.log_ofReal_mul hr I_ne_zero, Complex.log_I,
      show Real.log r = t by exact Real.log_exp t]
  have hi : (-(r : ℂ)*I)⁻¹ = (↑(Real.exp (-t)) : ℂ)*I := by
    rw [inv_negImag r hr]
    exact congrArg (fun x : ℝ => (x : ℂ)*I) (Real.exp_neg t).symm
  have hconj := dilog_negImag_im_conj (Real.exp_pos (-t)).le
    ((Real.exp_le_one_iff).mpr (neg_nonpos.mpr ht))
  have hn := congrArg Complex.im (principalDilog_inversion hz)
  rw [hl, hi] at hn
  rw [phaseSquare_im]
  have hnorm : (-(Real.pi : ℂ)^2 / 6 -
      ((t : ℂ) + (Real.pi / 2)*I)^2 / 2).im = -Real.pi*t/2 := by
    rw [pow_two, pow_two]
    norm_num [Complex.mul_re, Complex.mul_im]
    ring
  rw [Complex.add_im, hnorm] at hn
  rw [hconj] at hn
  linarith

private theorem alt_sum_even (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ range (2*n), (-1)^k * f k) =
      ∑ k ∈ range n, (f (2*k) - f (2*k+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, show 2*n+2 = (2*n+1)+1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    have h : (-1 : ℝ)^(2*n) = 1 := by rw [pow_mul]; norm_num
    rw [pow_succ (-1 : ℝ), h]
    ring

/-- A rational enclosure of an alternating saddle series using pairs of consecutive terms. -/
def saddlePartial (m n : ℕ) (p q : ℚ) : ℚ :=
  ∑ k ∈ range n, (
    p^(m*(2*k)+1) / (((m*(2*k)+1 : ℕ) : ℚ)^2) -
    q^(m*(2*k+1)+1) / (((m*(2*k+1)+1 : ℕ) : ℚ)^2))

private theorem saddlePartial_cast (m n : ℕ) (p q : ℚ) :
    (saddlePartial m n p q : ℝ) =
      ∑ k ∈ range n, (saddleCoeff m p (2*k) - saddleCoeff m q (2*k+1)) := by
  simp [saddlePartial, saddleCoeff]

def saddlePartialUpper (m n : ℕ) (p q : ℚ) : ℚ :=
  saddlePartial m n q p + q^(m*(2*n)+1) / (((m*(2*n)+1 : ℕ) : ℚ)^2)

private theorem saddlePartialUpper_cast (m n : ℕ) (p q : ℚ) :
    (saddlePartialUpper m n p q : ℝ) =
      (∑ k ∈ range n, (saddleCoeff m q (2*k) - saddleCoeff m p (2*k+1))) +
      saddleCoeff m q (2*n) := by
  rw [saddlePartialUpper, Rat.cast_add, saddlePartial_cast]
  simp [saddleCoeff]

private theorem saddleCoeff_mono (m k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    saddleCoeff m x k ≤ saddleCoeff m y k := by
  unfold saddleCoeff
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy _) (by positivity)

private theorem saddlePartial_bounds (m n : ℕ) {p q : ℚ} {x y : ℝ}
    (hp : 0 ≤ p) (hpx : (p : ℝ) ≤ x) (hxq : x ≤ (q : ℝ)) (hq : q ≤ 1)
    (hy : HasSum (fun k => (-1)^k * saddleCoeff m x k) y) :
    (saddlePartial m n p q : ℝ) ≤ y ∧ y ≤ (saddlePartialUpper m n p q : ℝ) := by
  have hp0 : (0 : ℝ) ≤ p := by exact_mod_cast hp
  have hx0 := hp0.trans hpx
  have hx1 : x ≤ 1 := hxq.trans (by exact_mod_cast hq)
  obtain ⟨hlo, hhi⟩ := alternating_bounds m hx0 hx1 hy n
  rw [sum_range_succ, alt_sum_even] at hhi
  rw [alt_sum_even] at hlo
  rw [saddlePartial_cast, saddlePartialUpper_cast]
  have hsign : (-1 : ℝ)^(2*n) = 1 := by rw [pow_mul]; norm_num
  rw [hsign, one_mul] at hhi
  refine ⟨le_trans ?_ hlo, le_trans hhi ?_⟩
  · exact sum_le_sum (fun k _ => sub_le_sub
      (saddleCoeff_mono m _ hp0 hpx) (saddleCoeff_mono m _ hx0 hxq))
  · exact add_le_add (sum_le_sum (fun k _ => sub_le_sub
      (saddleCoeff_mono m _ hx0 hxq) (saddleCoeff_mono m _ hp0 hpx)))
      (saddleCoeff_mono m _ hx0 hxq)

/-- Rational partial-sum bounds for minus the real dilogarithm at a negative real argument. -/
theorem saddlePartial_bounds_re (n : ℕ) {p q : ℚ} {x : ℝ}
    (hp : 0 ≤ p) (hpx : (p : ℝ) ≤ x) (hxq : x ≤ (q : ℝ)) (hq : q ≤ 1) :
    (saddlePartial 1 n p q : ℝ) ≤ -(principalDilog (-(x : ℂ))).re ∧
      -(principalDilog (-(x : ℂ))).re ≤ (saddlePartialUpper 1 n p q : ℝ) :=
  saddlePartial_bounds 1 n hp hpx hxq hq
    (dilog_neg_hasSum ((by exact_mod_cast hp : (0 : ℝ) ≤ p).trans hpx)
      (hxq.trans (by exact_mod_cast hq)))

/-- Rational partial-sum bounds for minus the imaginary dilogarithm on the imaginary axis. -/
theorem saddlePartial_bounds_im (n : ℕ) {p q : ℚ} {x : ℝ}
    (hp : 0 ≤ p) (hpx : (p : ℝ) ≤ x) (hxq : x ≤ (q : ℝ)) (hq : q ≤ 1) :
    (saddlePartial 2 n p q : ℝ) ≤ -(principalDilog (-(x : ℂ)*I)).im ∧
      -(principalDilog (-(x : ℂ)*I)).im ≤ (saddlePartialUpper 2 n p q : ℝ) :=
  saddlePartial_bounds 2 n hp hpx hxq hq
    (dilog_negImag_hasSum ((by exact_mod_cast hp : (0 : ℝ) ≤ p).trans hpx)
      (hxq.trans (by exact_mod_cast hq)))

theorem phaseSquare_re_one : (saddlePhaseSquare 1).re = Real.pi^2 / 24 := by
  rw [phaseSquare_re]
  push_cast
  rw [one_pow, principalDilog_neg_one]
  simp only [Complex.neg_re, Complex.div_ofNat_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  ring

/-- The squared saddle components are the half-sum and half-difference
of the norm and the real component of the squared saddle. -/
theorem saddle_component_squares (r : ℝ) :
    (saddleS r).re^2 = (‖saddlePhaseSquare r‖ + (saddlePhaseSquare r).re) / 2 ∧
    (saddleS r).im^2 = (‖saddlePhaseSquare r‖ - (saddlePhaseSquare r).re) / 2 := by
  have hre := congrArg Complex.re (saddleS_sq r)
  rw [pow_two, Complex.mul_re, ← pow_two, ← pow_two] at hre
  have hnorm : ‖saddlePhaseSquare r‖ = (saddleS r).re^2 + (saddleS r).im^2 := by
    rw [← saddleS_sq, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  exact ⟨by linarith, by linarith⟩

theorem saddle_norm_bounds_from_components {z : ℂ} {ul uu vl vu wl wu : ℝ}
    (hul : 0 ≤ ul) (hvl : 0 ≤ vl) (hwu : 0 ≤ wu)
    (hU₁ : ul ≤ z.re) (hU₂ : z.re ≤ uu) (hV₁ : vl ≤ z.im) (hV₂ : z.im ≤ vu)
    (hW₁ : wl^2 ≤ ul^2+vl^2) (hW₂ : uu^2+vu^2 ≤ wu^2) :
    wl ≤ ‖z‖ ∧ ‖z‖ ≤ wu := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  constructor
  · apply Real.le_sqrt_of_sq_le
    refine hW₁.trans (add_le_add (pow_le_pow_left₀ hul hU₁ _) (pow_le_pow_left₀ hvl hV₁ _))
  · refine Real.sqrt_le_iff.mpr ⟨hwu, ?_⟩
    exact (add_le_add (pow_le_pow_left₀ (hul.trans hU₁) hU₂ _)
      (pow_le_pow_left₀ (hvl.trans hV₁) hV₂ _)).trans hW₂

private theorem pi_bounds : (3.14159265358979 : ℝ) < Real.pi ∧ Real.pi < 3.14159265358980 :=
  ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩

private theorem pi_sq_bounds :
    (3.14159265358979 : ℝ)^2 ≤ Real.pi^2 ∧ Real.pi^2 ≤ (3.14159265358980 : ℝ)^2 :=
  ⟨pow_le_pow_left₀ (by norm_num) pi_bounds.1.le _,
    pow_le_pow_left₀ Real.pi_pos.le pi_bounds.2.le _⟩

private theorem square_one_re_bounds :
    (0.411233516 : ℝ) ≤ (saddlePhaseSquare 1).re ∧ (saddlePhaseSquare 1).re ≤ 0.411233517 := by
  rw [phaseSquare_re_one]
  exact ⟨by linarith [pi_sq_bounds.1], by linarith [pi_sq_bounds.2]⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem square_one_im_bounds :
    (1.831929 : ℝ) ≤ (saddlePhaseSquare 1).im ∧ (saddlePhaseSquare 1).im ≤ 1.831933 := by
  have hs := saddlePartial_bounds_im 220 (p := 1) (q := 1) (x := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hl : (0.9159645 : ℚ) ≤ saddlePartial 2 220 1 1 := by decide +kernel
  have hu : saddlePartialUpper 2 220 1 1 ≤ (0.9159665 : ℚ) := by decide +kernel
  have hr₁ : (0.9159645 : ℝ) ≤ (saddlePartial 2 220 1 1 : ℝ) := by
    simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).2 hl
  have hr₂ : (saddlePartialUpper 2 220 1 1 : ℝ) ≤ (0.9159665 : ℝ) := by
    simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).2 hu
  rw [phaseSquare_im]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- The lower endpoints for the first interval of the table on page 30. -/
theorem saddle_at_one_lower :
    (1.06975 : ℝ) ≤ (saddleS 1).re ∧ (0.85623 : ℝ) ≤ (saddleS 1).im := by
  obtain ⟨hu₁, hu₂⟩ := square_one_re_bounds
  obtain ⟨hv₁, hv₂⟩ := square_one_im_bounds
  have hw := saddle_norm_bounds_from_components
    (wl := 1.877518805) (wu := 1.87752271)
    (by norm_num) (by norm_num) (by norm_num) hu₁ hu₂ hv₁ hv₂ (by norm_num) (by norm_num)
  obtain ⟨hb, ha⟩ := saddleS_components (r := 1) (by norm_num)
  obtain ⟨hA, hB⟩ := saddle_component_squares 1
  exact ⟨(sq_le_sq₀ (by norm_num) (hb.trans ha).le).mp (by linarith [hw.1]),
    (sq_le_sq₀ (by norm_num) hb.le).mp (by linarith [hw.1])⟩

theorem saddle_at_one_sq_lower : (1.14437 : ℝ) < (saddleS 1).re ^ 2 := by
  obtain ⟨hu₁, hu₂⟩ := square_one_re_bounds
  obtain ⟨hv₁, hv₂⟩ := square_one_im_bounds
  have hw := saddle_norm_bounds_from_components
    (wl := 1.877518805) (wu := 1.87752271)
    (by norm_num) (by norm_num) (by norm_num) hu₁ hu₂ hv₁ hv₂ (by norm_num) (by norm_num)
  linarith [(saddle_component_squares 1).1, hw.1]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem square_1_16_re_bounds :
    (0.456549014 : ℝ) ≤ (saddlePhaseSquare (Real.exp (1/16))).re ∧
      (saddlePhaseSquare (Real.exp (1/16))).re ≤ 0.456549016 := by
  have hx₁ : (0.8824969025845 : ℝ) ≤ Real.exp (-2*(1/16)) := by
    rw [show (-2*(1/16) : ℝ) = -0.125 by norm_num]
    dyadic_interval +kernel [prec := 60]
  have hx₂ : Real.exp (-2*(1/16)) ≤ (0.8824969025846 : ℝ) := by
    rw [show (-2*(1/16) : ℝ) = -0.125 by norm_num]
    dyadic_interval +kernel [prec := 60]
  have hn₁ : ((0.8824969025845 : ℚ) : ℝ) ≤ Real.exp (-2*(1/16)) := by
    simpa only [Rat.cast_ofScientific] using hx₁
  have hn₂ : Real.exp (-2*(1/16)) ≤ ((0.8824969025846 : ℚ) : ℝ) := by
    simpa only [Rat.cast_ofScientific] using hx₂
  have hs := saddlePartial_bounds_re 85 (by norm_num) hn₁ hn₂ (by norm_num)
  have hl : (0.7396485373 : ℚ) ≤ saddlePartial 1 85 0.8824969025845 0.8824969025846 := by
    decide +kernel
  have hu : saddlePartialUpper 1 85 0.8824969025845 0.8824969025846 ≤ (0.7396485376 : ℚ) := by
    decide +kernel
  have hr₁ : (0.7396485373 : ℝ) ≤ (saddlePartial 1 85 0.8824969025845 0.8824969025846 : ℝ) := by
    simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).2 hl
  have hr₂ : (saddlePartialUpper 1 85 0.8824969025845 0.8824969025846 : ℝ) ≤
      (0.7396485376 : ℝ) := by
    simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).2 hu
  rw [phaseSquare_re_exp]
  exact ⟨by linarith [hs.2, pi_sq_bounds.1], by linarith [hs.1, pi_sq_bounds.2]⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem square_1_16_im_bounds :
    (1.932058448 : ℝ) ≤ (saddlePhaseSquare (Real.exp (1/16))).im ∧
      (saddlePhaseSquare (Real.exp (1/16))).im ≤ 1.932058449 := by
  have hx₁ : (0.9394130628134 : ℝ) ≤ Real.exp (-(1/16)) := by
    rw [show (-(1/16) : ℝ) = -0.0625 by norm_num]
    dyadic_interval +kernel [prec := 60]
  have hx₂ : Real.exp (-(1/16)) ≤ (0.9394130628135 : ℝ) := by
    rw [show (-(1/16) : ℝ) = -0.0625 by norm_num]
    dyadic_interval +kernel [prec := 60]
  have hn₁ : ((0.9394130628134 : ℚ) : ℝ) ≤ Real.exp (-(1/16)) := by
    simpa only [Rat.cast_ofScientific] using hx₁
  have hn₂ : Real.exp (-(1/16)) ≤ ((0.9394130628135 : ℚ) : ℝ) := by
    simpa only [Rat.cast_ofScientific] using hx₂
  have hs := saddlePartial_bounds_im 85 (by norm_num) hn₁ hn₂ (by norm_num)
  have hl : (0.8678544537 : ℚ) ≤ saddlePartial 2 85 0.9394130628134 0.9394130628135 := by
    decide +kernel
  have hu : saddlePartialUpper 2 85 0.9394130628134 0.9394130628135 ≤ (0.8678544539 : ℚ) := by
    decide +kernel
  have hr₁ : (0.8678544537 : ℝ) ≤ (saddlePartial 2 85 0.9394130628134 0.9394130628135 : ℝ) := by
    simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).2 hl
  have hr₂ : (saddlePartialUpper 2 85 0.9394130628134 0.9394130628135 : ℝ) ≤
      (0.8678544539 : ℝ) := by
    simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).2 hu
  rw [phaseSquare_im_exp (by norm_num : (0 : ℝ) ≤ 1/16)]
  exact ⟨by linarith [hs.1, pi_bounds.1], by linarith [hs.2, pi_bounds.2]⟩

/-- The upper endpoints for the first interval of the table on page 30. -/
theorem saddle_at_exp_one_sixteenth_upper :
    (saddleS (Real.exp (1/16))).re ≤ (1.10495 : ℝ) ∧
    (saddleS (Real.exp (1/16))).im ≤ (0.87428 : ℝ) := by
  obtain ⟨hu₁, hu₂⟩ := square_1_16_re_bounds
  obtain ⟨hv₁, hv₂⟩ := square_1_16_im_bounds
  have hw := saddle_norm_bounds_from_components
    (wl := 1.98526745) (wu := 1.985267452)
    (by norm_num) (by norm_num) (by norm_num) hu₁ hu₂ hv₁ hv₂ (by norm_num) (by norm_num)
  obtain ⟨hb, ha⟩ := saddleS_components (Real.exp_pos (1/16))
  obtain ⟨hA, hB⟩ := saddle_component_squares (Real.exp (1/16))
  exact ⟨(sq_le_sq₀ (hb.trans ha).le (by norm_num)).mp (by linarith [hw.2]),
    (sq_le_sq₀ hb.le (by norm_num)).mp (by linarith [hw.2])⟩

end DurfeeCCS.Step07
