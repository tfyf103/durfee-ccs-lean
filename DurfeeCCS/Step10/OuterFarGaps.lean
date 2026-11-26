module

public import DurfeeCCS.Step10.OuterFarParameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Exponential decrements for the lower-index and intermediate competitors. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real

/-- The exact deficit in the exponent of the l-th monomial. -/
def farGap (n d l : ℕ) : ℝ :=
  farSample n d * ((d : ℝ) - l) + 2 * π / sqrt 3 * (farRadius n d - farRadius n l)

/-- The Gaussian decay constant for the intermediate range. -/
def farTau (n : ℕ) : ℝ := 24 / π ^ 2 * (1 - 5 / (2 * (outerY n) ^ (1 / 3 : ℝ)))

theorem farGap_eq {n d l : ℕ} (hd : d ^ 2 < n) (hl : l ^ 2 < n) :
    farGap n d l = π / (sqrt 3 * farRadius n d) *
      (((d : ℝ) - l) ^ 2 + (farRadius n l - farRadius n d) ^ 2) := by
  rw [← farExponentGap hd hl]
  unfold farGap
  ring

theorem farRadius_antitone {n l l' : ℕ} (hl : l ≤ l') : farRadius n l' ≤ farRadius n l := by
  unfold farRadius
  apply sqrt_le_sqrt
  have hl' : (l : ℝ) ≤ l' := by exact_mod_cast hl
  exact sub_le_sub_left (pow_le_pow_left₀ (by positivity) hl' 2) _

private theorem farRadius_cube_lt {n d : ℕ} (hn : 6401 ≤ n) (hd : 1 ≤ d)
    (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) :
    farRadius n d ^ 3 < π ^ 3 / (24 * sqrt 3) * (outerY n) ^ 2 := by
  let y := outerY n
  let w := y ^ (1 / 3 : ℝ)
  have hy : 0 ≤ y := (outerY_gt80 hn).le.trans' (by norm_num)
  have hwc : w ^ 3 = y := farCube_eq hy
  have hf := farRadius_pos (cast_sq_lt_of_lt_sqrt hdm)
  have h := pow_lt_pow_left₀ (farParameters_of_threshold hn hd hdm hfar).1 hf.le
    (by decide : 3 ≠ 0)
  refine h.trans_eq ?_
  have h3 : (sqrt 3) ^ 2 = 3 := sq_sqrt (by norm_num)
  change (π / (2 * sqrt 3) * w ^ 2) ^ 3 = _
  rw [mul_pow, ← pow_mul, show (2 : ℕ) * 3 = 3 * 2 by decide, pow_mul, hwc]
  field_simp
  linear_combination -8 * y ^ 2 * h3

/-- The first decrement on the lower-index side, proved by the exact chord identity. -/
theorem farGap_previous_gt {n d : ℕ} (hn : 6401 ≤ n) (hd : 1 ≤ d)
    (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) :
    16 / π ^ 2 < farGap n d (d - 1) := by
  let y := outerY n
  let f := farRadius n d
  let g := farRadius n (d - 1)
  have hy : 0 < y := by linarith [outerY_gt80 hn]
  have hnds := cast_sq_lt_of_lt_sqrt hdm
  have hngs := cast_sq_lt_of_lt_sqrt (show d - 1 < n.sqrt by omega)
  have hf : 0 < f := farRadius_pos hnds
  have hg : 0 < g := farRadius_pos hngs
  have hf2 : f ^ 2 = y ^ 2 - (d : ℝ) ^ 2 := farRadius_sq hnds
  have hg2 : g ^ 2 = y ^ 2 - ((d : ℝ) - 1) ^ 2 := by
    simpa only [Nat.cast_sub hd, Nat.cast_one] using farRadius_sq hngs
  obtain ⟨_, _, hdy, hflo, hf125⟩ := farParameters_of_size hn hdm
  change (d : ℝ) < y at hdy
  change 1.96 * y < f ^ 2 at hflo
  change 12.5 < f at hf125
  have hgf : g ^ 2 - f ^ 2 = 2 * d - 1 := by nlinarith
  have hgRatio : g ≤ 1.422 * f := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h (by positivity : 0 ≤ 1.422 * f) (by decide : 2 ≠ 0)
    nlinarith
  have hden : 1 + (g + f) ^ 2 < 6 * f ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ g + f)
      (show g + f ≤ 2.422 * f by linarith) 2
    have hf2lo := pow_lt_pow_left₀ hf125 (by norm_num : (0 : ℝ) ≤ 12.5) (by decide : 2 ≠ 0)
    nlinarith
  have hgeom : (1 + (g - f) ^ 2) * (1 + (g + f) ^ 2) = 4 * y ^ 2 := by
    linear_combination (g ^ 2 - f ^ 2 + (2 * (d : ℝ) - 1)) * hgf + 2 * hf2 + 2 * hg2
  have hchord : 2 * y ^ 2 / (3 * f ^ 2) < 1 + (g - f) ^ 2 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have h := mul_lt_mul_of_pos_left hden (by positivity : 0 < 1 + (g - f) ^ 2)
    rw [hgeom] at h
    nlinarith
  have hcub : f ^ 3 < π ^ 3 / (24 * sqrt 3) * y ^ 2 := farRadius_cube_lt hn hd hdm hfar
  have hπ : 0 < π := pi_pos
  have hs : 0 < sqrt (3 : ℝ) := by positivity
  calc
    16 / π ^ 2 < π / (sqrt 3 * f) * (2 * y ^ 2 / (3 * f ^ 2)) := by
      rw [show π / (sqrt 3 * f) * (2 * y ^ 2 / (3 * f ^ 2)) =
          (2 * π * y ^ 2) / (3 * sqrt 3 * f ^ 3) by field_simp]
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      have h' := (lt_div_iff₀ (by positivity : 0 < 24 * sqrt (3 : ℝ))).mp
        (show f ^ 3 < (π ^ 3 * y ^ 2) / (24 * sqrt 3) from hcub.trans_eq (by ring))
      linarith
    _ < π / (sqrt 3 * f) * (1 + (g - f) ^ 2) :=
      mul_lt_mul_of_pos_left hchord (by positivity)
    _ = _ := by
      rw [farGap_eq hnds hngs, Nat.cast_sub hd, Nat.cast_one]
      change π / (sqrt 3 * f) * (1 + (g - f) ^ 2) =
        π / (sqrt 3 * f) * (((d : ℝ) - (d - 1)) ^ 2 + (g - f) ^ 2)
      ring

/-- The decrement per index increases along the lower-index side of the stationary point. -/
theorem farGap_lowerIndex_gt {n d l : ℕ} (hn : 6401 ≤ n) (hd : 1 ≤ d)
    (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) (hl : l < d) :
    (16 / π ^ 2) * ((d : ℝ) - l) < farGap n d l := by
  let a := d - 1
  let f := farRadius n d
  let g := farRadius n l
  let g₁ := farRadius n a
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have hls := cast_sq_lt_of_lt_sqrt (hl.trans hdm)
  have has := cast_sq_lt_of_lt_sqrt (show a < n.sqrt by dsimp [a]; omega)
  have hf : 0 < f := farRadius_pos hds
  have hg : 0 < g := farRadius_pos hls
  have hg₁ : 0 < g₁ := farRadius_pos has
  have hla : l ≤ a := by dsimp [a]; omega
  have hgg : g₁ ≤ g := farRadius_antitone hla
  have hq : 0 < (d : ℝ) - l := sub_pos.mpr (by exact_mod_cast hl)
  have heq (i : ℕ) (his : i ^ 2 < n) :
      farGap n d i =
        ((d : ℝ) - i) *
          (farSample n d - 2 * π / sqrt 3 * (((d : ℝ) + i) / (farRadius n i + f))) := by
    have hi := farRadius_sq his
    have hh := farRadius_sq hds
    have hi0 := farRadius_pos his
    have hdif : (farRadius n i - f) * (farRadius n i + f) =
        ((d : ℝ) - i) * ((d : ℝ) + i) := by
      change farRadius n i ^ 2 = _ at hi
      nlinarith
    unfold farGap
    rw [show f - farRadius n i = -(((d : ℝ) - i) * ((d : ℝ) + i) /
        (farRadius n i + f)) by
      rw [← hdif, mul_div_cancel_right₀ _ (by positivity)]
      ring]
    ring
  have ha : (a : ℝ) = (d : ℝ) - 1 := by simp only [a, Nat.cast_sub hd, Nat.cast_one]
  have hfirst : 16 / π ^ 2 < farGap n d a := farGap_previous_gt hn hd hdm hfar
  rw [heq a has] at hfirst
  have hfirst' : 16 / π ^ 2 <
      farSample n d - 2 * π / sqrt 3 * (((d : ℝ) + a) / (g₁ + f)) := by
    convert hfirst using 1
    have ha' : (d : ℝ) - a = 1 := by linarith
    rw [ha', one_mul]
  have hratio : ((d : ℝ) + l) / (g + f) ≤ ((d : ℝ) + a) / (g₁ + f) := by
    apply div_le_div₀ (by positivity) (by gcongr) (by positivity)
    linarith
  rw [heq l hls, mul_comm (16 / π ^ 2)]
  apply mul_lt_mul_of_pos_left _ hq
  exact hfirst'.trans_le (sub_le_sub_left (mul_le_mul_of_nonneg_left hratio (by positivity)) _)

/-- The quadratic bound on the higher-index side holds throughout the positive shifted support. -/
theorem farGap_upperIndex_ge {n d l : ℕ} (hn : 6401 ≤ n) (hd : 1 ≤ d)
    (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) (hl : d < l)
    (hls : l ^ 2 < n) :
    24 / π ^ 2 * ((l : ℝ) - d) ^ 2 ≤ farGap n d l := by
  let y := outerY n
  let f := farRadius n d
  let g := farRadius n l
  let q := (l : ℝ) - d
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have hf : 0 < f := farRadius_pos hds
  have hg : 0 < g := farRadius_pos hls
  have hf2 : f ^ 2 = y ^ 2 - (d : ℝ) ^ 2 := farRadius_sq hds
  have hg2 : g ^ 2 = y ^ 2 - (l : ℝ) ^ 2 := farRadius_sq hls
  have hgf : g ≤ f := farRadius_antitone hl.le
  have hq : 0 < q := sub_pos.mpr (by exact_mod_cast hl)
  have hdiff : (d : ℝ) / f * q ≤ f - g := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hf).mpr
    have heq : (f - g) * (f + g) = q * (2 * (d : ℝ) + q) := by dsimp only [q]; nlinarith
    have hle := mul_le_mul_of_nonneg_left (show f + g ≤ 2 * f by linarith)
      (sub_nonneg.mpr hgf)
    nlinarith [sq_nonneg q]
  have hdiff2 := pow_le_pow_left₀ (by positivity : 0 ≤ (d : ℝ) / f * q) hdiff 2
  have hr : q ^ 2 + ((d : ℝ) / f * q) ^ 2 = (y ^ 2 / f ^ 2) * q ^ 2 := by
    field_simp
    linear_combination hf2
  have hbound : 24 / π ^ 2 ≤ π * y ^ 2 / (sqrt 3 * f ^ 3) := by
    have h := farRadius_cube_lt hn hd hdm hfar
    have h' := (lt_div_iff₀ (by positivity : 0 < 24 * sqrt (3 : ℝ))).mp
      (show f ^ 3 < (π ^ 3 * y ^ 2) / (24 * sqrt 3) from h.trans_eq (by ring))
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  calc
    _ ≤ (π * y ^ 2 / (sqrt 3 * f ^ 3)) * q ^ 2 :=
      mul_le_mul_of_nonneg_right hbound (sq_nonneg _)
    _ = π / (sqrt 3 * f) * (q ^ 2 + ((d : ℝ) / f * q) ^ 2) := by rw [hr]; field_simp
    _ ≤ π / (sqrt 3 * f) * (q ^ 2 + (f - g) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hdiff2 _) (by positivity)
    _ = _ := by rw [farGap_eq hds hls]; dsimp [f, g, q]; ring

theorem farGap_radial {n d l : ℕ} (hd : d ^ 2 < n) (hl : l ^ 2 < n) :
    (π * farRadius n d / sqrt 3) * (1 - farRadius n l / farRadius n d) ^ 2 ≤ farGap n d l := by
  have hf := farRadius_pos hd
  have hs : 0 < sqrt (3 : ℝ) := by positivity
  rw [farGap_eq hd hl,
    show π * farRadius n d / sqrt 3 * (1 - farRadius n l / farRadius n d) ^ 2 =
      π / (sqrt 3 * farRadius n d) * (farRadius n l - farRadius n d) ^ 2 by field_simp; ring]
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ((d : ℝ) - l)]) (by positivity)

/-- If the competitor retains at least half the central radius, its polynomial prefactor
can be absorbed at the cost of the factor in the manuscript's τ. -/
theorem farGap_halfRadius {n d l : ℕ} (hn : 6401 ≤ n) (hd : 1 ≤ d)
    (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) (hl : d < l)
    (hls : l ^ 2 < n) (hhalf : farRadius n d / 2 ≤ farRadius n l) :
    (farRadius n d / farRadius n l) ^ (5 / 2 : ℝ) * exp (-farGap n d l) ≤
      exp (-farTau n * ((l : ℝ) - d) ^ 2) := by
  let y := outerY n
  let w := y ^ (1 / 3 : ℝ)
  let f := farRadius n d
  let g := farRadius n l
  let q := (l : ℝ) - d
  let θ := 1 - g / f
  let h := farSample n d
  let G := farGap n d l
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have hf : 0 < f := farRadius_pos hds
  have hg : 0 < g := farRadius_pos hls
  have hf2 := farRadius_sq hds
  have hg2 := farRadius_sq hls
  have hgf : g ≤ f := farRadius_antitone hl.le
  have hq : 1 ≤ q := by
    have hh : (d : ℝ) + 1 ≤ l := by exact_mod_cast hl
    dsimp [q]
    linarith
  have hq0 : 0 ≤ q := by linarith
  have hθ : 0 ≤ θ := sub_nonneg.mpr ((div_le_iff₀ hf).mpr (by simpa using hgf))
  have hθid : f * θ = f - g := by
    dsimp only [θ]
    field_simp
  have hπ := pi_pos
  have hs : 0 < sqrt (3 : ℝ) := by positivity
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  have hy80 : 80 < y := outerY_gt80 hn
  have hy : 0 < y := by linarith
  have hw : 0 < w := rpow_pos_of_pos hy _
  have hwlo : 4.3 < w := farCube_gt hy80.le
  have hpos : 0 < h := by unfold h farSample; positivity
  change 4 * w ≤ h at hfar
  have hdiff : (d : ℝ) ≤ f * (f - g) := by
    have heq : (f - g) * (f + g) = q * (2 * (d : ℝ) + q) := by
      dsimp only [q]
      change f ^ 2 = _ at hf2
      change g ^ 2 = _ at hg2
      nlinarith
    have hle := mul_le_mul_of_nonneg_left (show f + g ≤ 2 * f by linarith)
      (sub_nonneg.mpr hgf)
    have hq' := mul_le_mul_of_nonneg_left hq hd0.le
    nlinarith [sq_nonneg q]
  have hhθ : h / 2 ≤ π * f / sqrt 3 * θ := by
    unfold h farSample
    change (2 * π * (d : ℝ) / (sqrt 3 * f)) / 2 ≤ π * f / sqrt 3 * θ
    field_simp
    have hθd : (d : ℝ) ≤ f ^ 2 * θ := by
      rw [pow_two, mul_assoc, hθid]
      exact hdiff
    nlinarith [mul_le_mul_of_nonneg_left hθd pi_pos.le]
  have hGθ : h / 2 * θ ≤ G :=
    (mul_le_mul_of_nonneg_right hhθ hθ).trans (by
      rw [mul_assoc, ← pow_two]
      exact farGap_radial hds hls)
  have hlθ : (5 / 2 : ℝ) * log (f / g) ≤ 5 * θ := by
    have hlog := log_le_sub_one_of_pos (div_pos hf hg)
    have hg' : f / 2 ≤ g := hhalf
    have hv : f / g - 1 ≤ 2 * θ := by
      unfold θ
      have hfg : f / g - 1 = (f - g) / g := by field_simp
      rw [hfg]
      apply (div_le_iff₀ hg).mpr
      have hid : (2 * (1 - g / f)) * g = (2 * g / f) * (f - g) := by field_simp
      rw [hid]
      exact le_mul_of_one_le_left (sub_nonneg.mpr hgf)
        ((le_div_iff₀ hf).mpr (by linarith))
    linarith
  have hG0 : 0 ≤ G := (mul_nonneg (by positivity : 0 ≤ h / 2) hθ).trans hGθ
  have hlog : (5 / 2 : ℝ) * log (f / g) ≤ (5 / (2 * w)) * G := by
    calc
      _ ≤ 5 * θ := hlθ
      _ ≤ (10 / h) * G := by
        have hh := mul_le_mul_of_nonneg_left hGθ (show 0 ≤ 10 / h by positivity)
        convert hh using 1
        field_simp
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hG0
        calc
          _ ≤ (10 : ℝ) / (4 * w) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hfar
          _ = _ := by ring
  have hweight : 0 ≤ 1 - 5 / (2 * w) := sub_nonneg.mpr
    ((div_le_iff₀ (by positivity : 0 < 2 * w)).mpr (by linarith))
  have hbound : (1 - 5 / (2 * w)) * (24 / π ^ 2 * q ^ 2) ≤
      G - (5 / 2 : ℝ) * log (f / g) := by
    have hB := mul_le_mul_of_nonneg_left (farGap_upperIndex_ge hn hd hdm hfar hl hls) hweight
    change _ ≤ (1 - 5 / (2 * w)) * G at hB
    linarith
  change (f / g) ^ (5 / 2 : ℝ) * exp (-G) ≤ exp (-farTau n * q ^ 2)
  rw [rpow_def_of_pos (div_pos hf hg), ← exp_add]
  apply exp_le_exp.mpr
  change log (f / g) * (5 / 2) + -G ≤ -(24 / π ^ 2 * (1 - 5 / (2 * w))) * q ^ 2
  nlinarith

end DurfeeCCS.Step10
