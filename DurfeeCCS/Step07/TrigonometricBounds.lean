module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Taylor enclosures with a signed first-omitted-term remainder. -/

@[expose] public noncomputable section

open scoped BigOperators Nat

namespace DurfeeCCS.Step07

/-- The first `n` terms of the sine series at `x`. -/
def sinTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (x ^ (2 * k + 1) / (2 * k + 1)!)

/-- The first `n` terms of the cosine series at `x`. -/
def cosTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (x ^ (2 * k) / (2 * k)!)

/-- A convergent alternating series has a signed remainder enclosure whenever
the unsigned terms decrease from the point where the sum is cut. -/
private theorem alternating_tail_bounds {f : ℕ → ℝ} {z : ℝ} (n : ℕ)
    (hs : HasSum (fun i => (-1 : ℝ) ^ i * f i) z)
    (hdec : Antitone (fun k : ℕ => f (k + n))) :
    0 ≤ (-1 : ℝ) ^ n * (z - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) ∧
      (-1 : ℝ) ^ n * (z - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) ≤ f n := by
  let R := (-1 : ℝ) ^ n * (z - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
  have htail := ((hasSum_nat_add_iff' n).mpr hs).mul_left ((-1 : ℝ) ^ n)
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have htail' : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * f (k + n)) R := by
    convert htail using 1
    funext k
    rw [pow_add]
    calc
      _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * ((-1 : ℝ) ^ k * f (k + n)) := by
        rw [hsign, one_mul]
      _ = _ := by ring
  constructor
  · simpa using hdec.alternating_series_le_tendsto htail'.tendsto_sum_nat 0
  · simpa using hdec.tendsto_le_alternating_series htail'.tendsto_sum_nat 0

private theorem factorial_tail_antitone {x : ℝ} (hx : 0 ≤ x) (n j : ℕ)
    (hcut : x ^ 2 ≤ ((2 * n + j + 1 : ℕ) : ℝ) * (2 * n + j + 2 : ℕ)) :
    Antitone (fun k : ℕ => x ^ (2 * (k + n) + j) / (2 * (k + n) + j)!) := by
  apply antitone_nat_of_succ_le
  intro k
  let m : ℕ := 2 * (k + n) + j
  have hm : 2 * (k + 1 + n) + j = m + 1 + 1 := by dsimp [m]; omega
  have hfac : 0 < (m ! : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have h2 : 0 < ((m + 1 + 1 : ℕ) : ℝ) := by positivity
  have hle : 2 * n + j ≤ m := by dsimp [m]; omega
  have h1le : ((2 * n + j + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hle
  have h2le : ((2 * n + j + 2 : ℕ) : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * n + j + 2 ≤ m + 1 + 1 by omega)
  have hmono : x ^ 2 ≤ ((m + 1 : ℕ) : ℝ) * ((m + 1 + 1 : ℕ) : ℝ) :=
    hcut.trans (mul_le_mul h1le h2le (by positivity) h1.le)
  change x ^ (2 * (k + 1 + n) + j) / (2 * (k + 1 + n) + j)! ≤ x ^ m / (m ! : ℝ)
  rw [hm, show m + 1 + 1 = m + 2 by omega, pow_add,
    show (m + 2)! = (m + 1 + 1) * ((m + 1) * m !) from rfl]
  push_cast at hmono ⊢
  rw [div_le_div_iff₀ (by positivity) hfac]
  calc
    _ ≤ (x ^ m * ((↑m + 1) * (↑m + 1 + 1))) * (↑(m !) : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (pow_nonneg hx _)) hfac.le
    _ = _ := by ring

/-- The cosine Taylor remainder lies between zero and the first omitted term after
multiplying by its sign. The cut condition only concerns the omitted tail. -/
theorem cos_taylor_bounds {x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hcut : x ^ 2 ≤ ((2 * n + 1 : ℕ) : ℝ) * (2 * n + 2 : ℕ)) :
    0 ≤ (-1 : ℝ) ^ n * (Real.cos x - cosTaylor n x) ∧
      (-1 : ℝ) ^ n * (Real.cos x - cosTaylor n x) ≤ x ^ (2 * n) / (2 * n)! := by
  have hs : HasSum (fun i : ℕ => (-1 : ℝ) ^ i * (x ^ (2 * i) / (2 * i)!)) (Real.cos x) := by
    simpa only [mul_div_assoc] using Real.hasSum_cos x
  exact alternating_tail_bounds n hs (by simpa using factorial_tail_antitone hx n 0 (by simpa using hcut))

/-- The sine Taylor remainder lies between zero and the first omitted term after
multiplying by its sign. The cut condition only concerns the omitted tail. -/
theorem sin_taylor_bounds {x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hcut : x ^ 2 ≤ ((2 * n + 1 + 1 : ℕ) : ℝ) * (2 * n + 1 + 2 : ℕ)) :
    0 ≤ (-1 : ℝ) ^ n * (Real.sin x - sinTaylor n x) ∧
      (-1 : ℝ) ^ n * (Real.sin x - sinTaylor n x) ≤ x ^ (2 * n + 1) / (2 * n + 1)! := by
  have hs : HasSum (fun i : ℕ => (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)) (Real.sin x) := by
    simpa only [mul_div_assoc] using Real.hasSum_sin x
  exact alternating_tail_bounds n hs (factorial_tail_antitone hx n 1 hcut)

/-- A degree-seven lower enclosure for sine. -/
theorem sin_taylor_seven_lower {x : ℝ} (hx : 0 ≤ x) (hcut : x ^ 2 ≤ 110) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  have h := (sin_taylor_bounds hx 4 (by norm_num; exact hcut)).1
  norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The first `n` terms of the arctangent Taylor expansion at the origin. -/
def arctanTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (x ^ (2 * k + 1) / (2 * k + 1 : ℕ))

private theorem hasDerivAt_oddMonomial (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ (2 * k + 1) / (2 * k + 1 : ℕ)) (x ^ (2 * k)) x := by
  have hden : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  convert (hasDerivAt_pow (2 * k + 1) x).div_const ((2 * k + 1 : ℕ) : ℝ) using 1
  rw [Nat.add_sub_cancel]
  field_simp [hden]

private theorem hasDerivAt_arctanTaylor (n : ℕ) (x : ℝ) :
    HasDerivAt (arctanTaylor n) (∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k)) x := by
  induction n with
  | zero =>
    rw [show arctanTaylor 0 = fun _ => 0 by funext t; simp [arctanTaylor]]
    simpa using hasDerivAt_const x (0 : ℝ)
  | succ n hn =>
    rw [show arctanTaylor (n + 1) = arctanTaylor n +
      (fun t => (-1 : ℝ) ^ n * (t ^ (2 * n + 1) / (2 * n + 1 : ℕ))) by
      funext t
      change arctanTaylor (n + 1) t = arctanTaylor n t + _
      simp only [arctanTaylor, Finset.sum_range_succ]]
    simpa only [Finset.sum_range_succ] using
      hn.add ((hasDerivAt_oddMonomial n x).const_mul ((-1 : ℝ) ^ n))

private theorem arctan_kernel_split (n : ℕ) (x : ℝ) :
    1 / (1 + x ^ 2) - ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k) =
      (-1 : ℝ) ^ n * (x ^ (2 * n) / (1 + x ^ 2)) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ, sub_add_eq_sub_sub, hn, pow_succ,
      show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    have hden : 1 + x ^ 2 ≠ 0 := by positivity
    field_simp [hden]
    ring

/-- The arctangent Taylor error, after multiplying by the sign of the first omitted
term, lies between zero and its magnitude. The estimate holds on the entire
nonnegative real axis by bounding the finite geometric remainder of the derivative. -/
theorem arctan_taylor_bounds {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n * (Real.arctan x - arctanTaylor n x) ∧
      (-1 : ℝ) ^ n * (Real.arctan x - arctanTaylor n x) ≤
        x ^ (2 * n + 1) / (2 * n + 1 : ℕ) := by
  let R (t : ℝ) := (-1 : ℝ) ^ n * (Real.arctan t - arctanTaylor n t)
  have hR (t : ℝ) : HasDerivAt R (t ^ (2 * n) / (1 + t ^ 2)) t := by
    convert ((Real.hasDerivAt_arctan t).sub (hasDerivAt_arctanTaylor n t)).const_mul
      ((-1 : ℝ) ^ n) using 1
    rw [arctan_kernel_split, ← mul_assoc, ← mul_pow]
    norm_num
  have h0 : R 0 = 0 := by simp [R, arctanTaylor, zero_pow (Nat.succ_ne_zero _)]
  have hpow (t : ℝ) : 0 ≤ t ^ (2 * n) := by
    rw [Nat.mul_comm, pow_mul]
    positivity
  have hMono : MonotoneOn R (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hR t).continuousAt.continuousWithinAt
    · intro t _
      exact (hR t).differentiableAt.differentiableWithinAt
    · intro t _
      rw [(hR t).deriv]
      exact div_nonneg (hpow t) (by positivity)
  let U (t : ℝ) := t ^ (2 * n + 1) / (2 * n + 1 : ℕ) - R t
  have hU (t : ℝ) : HasDerivAt U (t ^ (2 * n) - t ^ (2 * n) / (1 + t ^ 2)) t :=
    (hasDerivAt_oddMonomial n t).sub (hR t)
  have hMonoU : MonotoneOn U (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hU t).continuousAt.continuousWithinAt
    · intro t _
      exact (hU t).differentiableAt.differentiableWithinAt
    · intro t _
      rw [(hU t).deriv]
      apply sub_nonneg.mpr
      apply div_le_self
      · exact hpow t
      · linarith [sq_nonneg t]
  constructor
  · simpa only [h0] using hMono (show (0 : ℝ) ∈ Set.Ici 0 from le_rfl) hx hx
  · have hU0 : U 0 = 0 := by simp [U, h0, zero_pow (Nat.succ_ne_zero _)]
    have h := hMonoU (show (0 : ℝ) ∈ Set.Ici 0 from le_rfl) hx hx
    exact sub_nonneg.mp (hU0 ▸ h)

/-- The cubic lower bound on arctangent used on page 53. -/
theorem arctan_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  have h := (arctan_taylor_bounds hx 2).1
  norm_num [arctanTaylor, Finset.sum_range_succ] at h
  linarith

/-- The quadratic cosine gap on the entire interval used on page 20. -/
theorem cosine_gap_on_small_angles {t : ℝ} (ht : |t| ≤ Real.pi / 3) :
    (0.45 : ℝ) * t ^ 2 ≤ 1 - Real.cos t := by
  let x : ℝ := |t|
  have hx : 0 ≤ x := abs_nonneg t
  have hx' : x ≤ 1.05 := by
    have hpi := Real.pi_lt_d2
    change x ≤ Real.pi / 3 at ht
    linarith
  have hsq : x ^ 2 ≤ (1.05 : ℝ) ^ 2 := pow_le_pow_left₀ hx hx' 2
  have h4 : x ^ 4 ≤ (1.05 : ℝ) ^ 2 * x ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 by decide, pow_add]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hcut : x ^ 2 ≤ ((2 * 3 + 1 : ℕ) : ℝ) * (2 * 3 + 2 : ℕ) := hsq.trans (by norm_num)
  have h := (cos_taylor_bounds hx 3 hcut).1
  norm_num [cosTaylor, Finset.sum_range_succ, Nat.factorial] at h
  have gap : (0.45 : ℝ) * x ^ 2 ≤ 1 - Real.cos x := by linarith [sq_nonneg x]
  simpa [x, sq_abs] using gap

/-- The explicit cosine bound used in the page 22 error estimate. -/
theorem cos_1085_lower : (0.466 : ℝ) < Real.cos 1.085 := by
  have h := (cos_taylor_bounds (x := 1.085) (by norm_num) 4 (by norm_num)).1
  norm_num [cosTaylor, Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The small-angle sine bound used on page 21. -/
theorem ninetyNine_mul_le_sin {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 0.245) :
    (0.99 : ℝ) * t ≤ Real.sin t := by
  rcases le_or_gt t (0.2449 : ℝ) with hlo | hhi
  · have h : t ^ 3 ≤ (0.2449 : ℝ) ^ 2 * t := by
      simpa only [pow_succ] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht hlo 2) ht
    linarith [Real.sin_ge_sub_cube ht]
  · have h3 : t ^ 3 ≤ (0.245 : ℝ) ^ 2 * t := by
      simpa only [pow_succ] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht ht' 2) ht
    have h5 : (0.2449 : ℝ) ^ 4 * t ≤ t ^ 5 := by
      simpa only [pow_succ] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hhi.le 4) ht
    have h7 : t ^ 7 ≤ (0.245 : ℝ) ^ 6 * t := by
      simpa only [pow_succ] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht ht' 6) ht
    have hcut : t ^ 2 ≤ 110 := (pow_le_pow_left₀ ht ht' 2).trans (by norm_num)
    linarith [sin_taylor_seven_lower ht hcut]

end DurfeeCCS.Step07
