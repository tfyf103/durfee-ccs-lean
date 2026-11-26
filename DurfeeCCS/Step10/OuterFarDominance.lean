module

public import DurfeeCCS.Step10.OuterFarCentral
public import DurfeeCCS.Step10.OuterFarSmallBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! Lemma 4.3 and its sign consequence, given the two-colour coefficient estimates. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Finset Step06

/-- The contribution of one competitor relative to the central monomial. -/
def farRatio (n d l : ℕ) : ℝ :=
  farWeighted n l (farSample n d) / farWeighted n d (farSample n d)

theorem farWeighted_central_pos (hc : FarCoefficientBounds) {n d : ℕ}
    (hn : 6401 ≤ n) (hd : 1 ≤ d) (hdm : d < n.sqrt)
    (hfar : farThreshold n ≤ farSample n d) :
    0 < farWeighted n d (farSample n d) := by
  have hf := farRadius_pos (cast_sq_lt_of_lt_sqrt hdm)
  have hb := farCentral_lower hc hn hd hdm hfar
  have hpd : 0 < (p n d : ℝ) := (mul_pos (by norm_num) (outerComparisonB_pos hf)).trans hb
  unfold farWeighted
  positivity

private theorem farRatio_of_coeff_bound {n d l : ℕ} {c : ℝ}
    (hds : d ^ 2 < n) (hls : l ^ 2 < n)
    (hmain : 0.875 * outerComparisonB (farRadius n d) < (p n d : ℝ))
    (hcoeff : (p n l : ℝ) ≤ c * outerComparisonB (farRadius n l)) :
    farRatio n d l ≤ c / 0.875 * (farRadius n d / farRadius n l) ^ (5 / 2 : ℝ) *
      exp (-farGap n d l) := by
  let h := farSample n d
  let f := farRadius n d
  let g := farRadius n l
  have hf : 0 < f := farRadius_pos hds
  have hg : 0 < g := farRadius_pos hls
  have hb : 0 < outerComparisonB f := outerComparisonB_pos hf
  have heq : ((l : ℝ) * h - (d : ℝ) * h) + (2 * π / sqrt 3 * (g - f)) =
       -farGap n d l := by unfold farGap; dsimp only [h, f, g]; ring
  unfold farRatio farWeighted
  change (p n l : ℝ) * exp ((l : ℝ) * h) / ((p n d : ℝ) * exp ((d : ℝ) * h)) ≤ _
  calc
    _ ≤ (c * outerComparisonB g * exp ((l : ℝ) * h)) /
        (0.875 * outerComparisonB f * exp ((d : ℝ) * h)) := by
      apply div_le_div₀ (mul_nonneg ((Nat.cast_nonneg (p n l)).trans hcoeff) (exp_nonneg _))
        (mul_le_mul_of_nonneg_right hcoeff (exp_nonneg _)) (by positivity)
        (mul_le_mul_of_nonneg_right hmain.le (exp_nonneg _))
    _ = c / 0.875 * (outerComparisonB g / outerComparisonB f) *
        (exp ((l : ℝ) * h) / exp ((d : ℝ) * h)) := by ring
    _ = _ := by
      rw [outerComparisonB_ratio hg hf, ← exp_sub]
      rw [← heq, exp_add]
      ring

/-- Equation (76), including its strict simplification to 1.26. -/
theorem farRatio_bound (hc : FarCoefficientBounds) {n d l : ℕ} (hn : 6401 ≤ n)
    (hd : 1 ≤ d) (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d)
    (hls : l ^ 2 + 25 ≤ n) :
    farRatio n d l ≤ (1.1 / 0.875) * (farRadius n d / farRadius n l) ^ (5 / 2 : ℝ) *
        exp (-farGap n d l) ∧
    farRatio n d l < 1.26 * (farRadius n d / farRadius n l) ^ (5 / 2 : ℝ) *
        exp (-farGap n d l) := by
  have hld : l ^ 2 < n := by omega
  have hcoeff := (durfeeCoeff_le_twoColour hld.le).trans
    (hc.2.1 (n - l ^ 2) (by omega))
  rw [show twoColourShift (n - l ^ 2) = farRadius n l from farShift_eq hld] at hcoeff
  have h := farRatio_of_coeff_bound (cast_sq_lt_of_lt_sqrt hdm) hld
    (farCentral_lower hc hn hd hdm hfar) hcoeff
  have hf := farRadius_pos (cast_sq_lt_of_lt_sqrt hdm)
  have hg := farRadius_pos hld
  refine ⟨h, h.trans_lt ?_⟩
  gcongr
  norm_num

private theorem farRatio_lowerIndex (hc : FarCoefficientBounds) {n d l : ℕ}
    (hn : 6401 ≤ n) (hd : 1 ≤ d) (hdm : d < n.sqrt)
    (hfar : farThreshold n ≤ farSample n d) (hl : l < d) :
    farRatio n d l ≤ 1.26 * exp (-(16 / π ^ 2) * ((d : ℝ) - l)) := by
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have hls := cast_sq_lt_of_lt_sqrt (hl.trans hdm)
  have hl25 : l ^ 2 + 25 ≤ n := by
    have hfsq := farRadius_sq hds
    have hfg := farRadius_antitone (n := n) hl.le
    obtain ⟨_, _, _, hflo, _⟩ := farParameters_of_size hn hdm
    have hnd := outerY_gt80 hn
    have hs : (d : ℝ) ^ 2 + 25 ≤ n := by
      rw [hfsq, outerY_sq (by omega : 0 < n)] at hflo
      linarith
    have hs' : (l : ℝ) ^ 2 + 25 ≤ n :=
      (add_le_add_left (pow_le_pow_left₀ (by positivity : 0 ≤ (l : ℝ)) (by exact_mod_cast hl.le) 2)
        25).trans hs
    exact_mod_cast hs'
  have hb := (farRatio_bound hc hn hd hdm hfar hl25).2
  have hg := farRadius_pos hls
  have hf := farRadius_pos hds
  have hratio : (farRadius n d / farRadius n l) ^ (5 / 2 : ℝ) ≤ 1 := by
    apply rpow_le_one (by positivity) (by exact (div_le_one hg).mpr (farRadius_antitone hl.le))
      (by norm_num)
  apply hb.le.trans
  calc
    _ ≤ 1.26 * 1 * exp (-farGap n d l) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (by norm_num)) (exp_nonneg _)
    _ ≤ _ := by
      rw [mul_one]
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (by norm_num)
      linarith [farGap_lowerIndex_gt hn hd hdm hfar hl]

private theorem farRatio_halfRadius (hc : FarCoefficientBounds) {n d l : ℕ}
    (hn : 6401 ≤ n) (hd : 1 ≤ d) (hdm : d < n.sqrt)
    (hfar : farThreshold n ≤ farSample n d) (hl : d < l) (hlm : l ≤ n.sqrt)
    (hhalf : farRadius n d / 2 ≤ farRadius n l) :
    farRatio n d l ≤ 1.26 * exp (-farTau n * ((l : ℝ) - d) ^ 2) := by
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have hn0 : 0 < n := by omega
  have hy80 := outerY_gt80 hn
  obtain ⟨_, _, _, hflo, hf125⟩ := farParameters_of_size hn hdm
  have hls : l ^ 2 < n := by
    have hlq := (pow_le_pow_left₀ (Nat.zero_le l) hlm 2).trans (Nat.sqrt_le' n)
    by_contra! hge
    have hln : l ^ 2 = n := le_antisymm hlq hge
    have he : (l : ℝ) ^ 2 = n := by exact_mod_cast hln
    have hz : farRadius n l = 0 := by
      rw [farRadius, outerY_sq hn0, he, sqrt_eq_zero_of_nonpos (by linarith)]
    rw [hz] at hhalf
    linarith
  have hl25 : l ^ 2 + 25 ≤ n := by
    have hf := farRadius_pos hds
    have hg := farRadius_pos hls
    have hsq := pow_le_pow_left₀ (show 0 ≤ farRadius n d / 2 by positivity) hhalf 2
    have hc' : (l : ℝ) ^ 2 + 25 ≤ n := by
      rw [farRadius_sq hls, outerY_sq hn0] at hsq
      nlinarith
    exact_mod_cast hc'
  apply (farRatio_bound hc hn hd hdm hfar hl25).2.le.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (farGap_halfRadius hn hd hdm hfar hl hls hhalf) (by norm_num)

private theorem farRatio_smallRadius (hc : FarCoefficientBounds) {n d l : ℕ}
    (hn : 6401 ≤ n) (hd : 1 ≤ d) (hdm : d < n.sqrt)
    (hfar : farThreshold n ≤ farSample n d)
    (hls : l ^ 2 < n) (hsmall : farRadius n l < farRadius n d / 2) :
    farRatio n d l < 16.82 * exp (-(π * farRadius n d / (4 * sqrt 3))) := by
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have hf := farRadius_pos hds
  have hg := farRadius_pos hls
  have hcoeff := (durfeeCoeff_le_twoColour hls.le).trans (hc.1 (n - l ^ 2) (by omega))
  rw [show twoColourShift (n - l ^ 2) = farRadius n l from farShift_eq hls] at hcoeff
  have hb := farRatio_of_coeff_bound hds hls (farCentral_lower hc hn hd hdm hfar) hcoeff
  have hgl : sqrt (11 / 12) ≤ farRadius n l := by
    have hls' : (l : ℝ) ^ 2 + 1 ≤ n := by exact_mod_cast (show l ^ 2 + 1 ≤ n by omega)
    unfold farRadius
    apply sqrt_le_sqrt
    rw [outerY_sq (by omega : 0 < n)]
    linarith
  have hh := (farParameters_of_size hn hdm).2.2.2.2
  apply hb.trans_lt
  refine lt_of_le_of_lt ?_ (farSmallRadius_point hh.le hgl hsmall.le)
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (by positivity)
  linarith [farGap_radial hds hls]

/-- The square endpoint is treated without using any positive shifted radius for its coefficient. -/
theorem farRatio_squareEndpoint (hc : FarCoefficientBounds) {n d l : ℕ} (hn : 6401 ≤ n)
    (hd : 1 ≤ d) (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d)
    (hls : n = l ^ 2) (hlm : l ≤ n.sqrt) :
    l = n.sqrt ∧ p n l = 1 ∧
    farRatio n d l < 16.82 * exp (-(π * farRadius n d / (4 * sqrt 3))) := by
  let h := farSample n d
  let y := outerY n
  let f := farRadius n d
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have hf : 0 < f := farRadius_pos hds
  have hf2 : f ^ 2 = y ^ 2 - (d : ℝ) ^ 2 := farRadius_sq hds
  have hdm' : (d : ℝ) < n.sqrt := by exact_mod_cast hdm
  have hy : 0 < y := by linarith [outerY_gt80 hn]
  obtain ⟨_, hmhi, hdy, _, hf125⟩ := farParameters_of_size hn hdm
  change (d : ℝ) < y at hdy
  change 12.5 < f at hf125
  have h0 : 0 < h := by unfold h farSample; positivity
  have hde : (0 : ℝ) < d := by exact_mod_cast hd
  have hmain : 0.875 * outerComparisonB f < (p n d : ℝ) := farCentral_lower hc hn hd hdm hfar
  have hB : 0 < outerComparisonB f := outerComparisonB_pos hf
  have hln : l = n.sqrt := by
    have hh : n.sqrt ^ 2 ≤ l ^ 2 := (Nat.sqrt_le' n).trans_eq hls
    by_contra! hne
    exact (not_lt_of_ge hh) (pow_lt_pow_left₀ (lt_of_le_of_ne hlm hne) (Nat.zero_le _) (by decide : 2 ≠ 0))
  have hp : p n l = 1 := durfee_square_coeff hls
  have heq : h * (y - (d : ℝ)) - 2 * π * f / sqrt 3 =
      -(2 * π * f / sqrt 3) * (y / (y + d)) := by
    have hid : (y - (d : ℝ)) * (y + d) = f ^ 2 := by nlinarith
    have hsub : y - (d : ℝ) = f ^ 2 / (y + d) :=
      (eq_div_iff (show y + (d : ℝ) ≠ 0 by positivity)).mpr hid
    rw [hsub]
    unfold h farSample
    change (2 * π * (d : ℝ) / (sqrt 3 * f)) * (f ^ 2 / (y + d)) - 2 * π * f / sqrt 3 = _
    field_simp
    ring
  have ha : h * (y - (d : ℝ)) - 2 * π * f / sqrt 3 < -(π * f / sqrt 3) := by
    rw [heq]
    have hh : (1 / 2 : ℝ) < y / (y + d) := (lt_div_iff₀ (by positivity)).mpr (by linarith)
    have hfac : 0 < 2 * π * f / sqrt 3 := by positivity
    rw [show -(π * f / sqrt 3) = -(2 * π * f / sqrt 3) * (1 / 2) by ring]
    exact mul_lt_mul_of_neg_left hh (neg_neg_of_pos hfac)
  have hb : h * ((l : ℝ) - y) < π / (6 * sqrt 3 * f) := by
    rw [hln]
    change (n.sqrt : ℝ) < y + 1 / (12 * y) at hmhi
    have hdiff : (n.sqrt : ℝ) - y < 1 / (12 * y) := by linarith
    apply (mul_lt_mul_of_pos_left hdiff h0).trans
    unfold h farSample
    change (2 * π * (d : ℝ) / (sqrt 3 * f)) * (1 / (12 * y)) < _
    field_simp
    nlinarith [mul_lt_mul_of_pos_left hdy pi_pos]
  have hc' : (l : ℝ) * h - (d : ℝ) * h - 2 * π * f / sqrt 3 <
      -(π * f / sqrt 3) + π / (6 * sqrt 3 * f) := by linarith
  refine ⟨hln, hp, ?_⟩
  unfold farRatio farWeighted
  rw [hp, Nat.cast_one, one_mul]
  change exp ((l : ℝ) * h) / ((p n d : ℝ) * exp ((d : ℝ) * h)) < _
  calc
    _ ≤ exp ((l : ℝ) * h) / (0.875 * outerComparisonB f * exp ((d : ℝ) * h)) :=
      div_le_div_of_nonneg_left (exp_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_right hmain.le (exp_nonneg _))
    _ = (4 * (3 : ℝ) ^ (3 / 4 : ℝ) / 0.875) * f ^ (5 / 2 : ℝ) *
        exp ((l : ℝ) * h - (d : ℝ) * h - 2 * π * f / sqrt 3) := by
      rw [exp_sub, exp_sub]
      unfold outerComparisonB
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ ≤ (4 * (3 : ℝ) ^ (3 / 4 : ℝ) / 0.875) * f ^ (5 / 2 : ℝ) *
        exp (-(π * f / sqrt 3) + π / (6 * sqrt 3 * f)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hc'.le) (by positivity)
    _ < _ := farSquare_cost hf125.le

private theorem farSum_le_geometric {s : Finset ℕ} {F : ℕ → ℝ} (g : ℕ → ℕ)
    (hgi : Set.InjOn g ↑s) {A q : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ l ∈ s, F l ≤ A * q ^ (g l)) :
    (∑ l ∈ s, F l) ≤ A / (1 - q) := by
  calc
    _ ≤ ∑ l ∈ s, A * q ^ (g l) := Finset.sum_le_sum hb
    _ = ∑ k ∈ s.image g, A * q ^ k := (Finset.sum_image (f := fun k => A * q ^ k) hgi).symm
    _ ≤ ∑' k : ℕ, A * q ^ k :=
      ((summable_geometric_of_lt_one hq hq1).mul_left A).sum_le_tsum _
        (fun i _ => mul_nonneg hA (pow_nonneg hq i))
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]

/-- Total of the competitors to the right of j = m-d in the manuscript. -/
theorem farUpperIndexTail (hc : FarCoefficientBounds) {n d : ℕ} (hn : 6401 ≤ n)
    (hd : 1 ≤ d) (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) :
    (∑ l ∈ Finset.Ico 1 d, farRatio n d l) < 0.311 := by
  let a := 16 / π ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hq := exp_lt_one_iff.mpr (show -a < 0 by linarith)
  have hb (l : ℕ) (hl : l ∈ Finset.Ico 1 d) :
      farRatio n d l ≤ (1.26 * exp (-a)) * exp (-a) ^ (d - 1 - l) := by
    have hl' := (Finset.mem_Ico.mp hl).2
    have h := farRatio_lowerIndex hc hn hd hdm hfar hl'
    have hcast : ((d - 1 - l : ℕ) : ℝ) = (d : ℝ) - 1 - l := by
      rw [Nat.cast_sub (show l ≤ d - 1 by omega), Nat.cast_sub hd, Nat.cast_one]
    rw [mul_assoc, ← exp_nat_mul, ← exp_add, hcast,
      show -a + ((d : ℝ) - 1 - l) * -a = -(16 / π ^ 2) * ((d : ℝ) - l) by
        dsimp only [a]
        ring]
    exact h
  have hgi : Set.InjOn (fun l : ℕ => d - 1 - l) (↑(Finset.Ico 1 d)) := by
    intro l hl l' hl' he
    have h1 := (Finset.mem_Ico.mp hl).2
    have h2 := (Finset.mem_Ico.mp hl').2
    change d - 1 - l = d - 1 - l' at he
    omega
  have hm := farSum_le_geometric (fun l => d - 1 - l) hgi (by positivity) (exp_nonneg _) hq hb
  refine hm.trans_lt ?_
  rw [exp_neg, show 1 - (exp a)⁻¹ = (exp a - 1) / exp a by field_simp]
  rw [show 1.26 * (exp a)⁻¹ / ((exp a - 1) / exp a) = (1.26 : ℝ) / (exp a - 1) by
    have hnon : exp a - 1 ≠ 0 := (sub_pos.mpr (one_lt_exp_iff.mpr ha)).ne'
    field_simp]
  exact farRightTail_constant

/-- Total of the competitors to the left of j with at least half the central radius. -/
theorem farHalfRadiusTail (hc : FarCoefficientBounds) {n d : ℕ} (hn : 6401 ≤ n)
    (hd : 1 ≤ d) (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) :
    (∑ l ∈ (Finset.Icc (d + 1) n.sqrt).filter (fun l => farRadius n d / 2 ≤ farRadius n l),
      farRatio n d l) < 0.477 := by
  let τ := farTau n
  let s := (Finset.Icc (d + 1) n.sqrt).filter (fun l => farRadius n d / 2 ≤ farRadius n l)
  have ht := farTau_ge hn
  have ht0 : 0 ≤ τ := by dsimp [τ]; linarith
  have hq := exp_lt_one_iff.mpr (show -3 * τ < 0 by dsimp [τ]; linarith)
  have hb (l : ℕ) (hl : l ∈ s) :
      farRatio n d l ≤ (1.26 * exp (-τ)) * exp (-3 * τ) ^ (l - d - 1) := by
    obtain ⟨⟨hld, hlm⟩, hhalf⟩ := (Finset.mem_filter.mp hl).imp_left Finset.mem_Icc.mp
    have h := farRatio_halfRadius hc hn hd hdm hfar (show d < l by omega) hlm hhalf
    have hcast : ((l - d - 1 : ℕ) : ℝ) = (l : ℝ) - d - 1 := by
      rw [Nat.cast_sub (show 1 ≤ l - d by omega), Nat.cast_sub (show d ≤ l by omega), Nat.cast_one]
    have hh : (1 : ℝ) + 3 * ((l : ℝ) - d - 1) ≤ ((l : ℝ) - d) ^ 2 := by
      by_cases hle : l ≤ d + 1
      · have heq : l = d + 1 := by omega
        norm_num [heq]
      · have hge : (d : ℝ) + 2 ≤ l := by exact_mod_cast (show d + 2 ≤ l by omega)
        nlinarith [mul_nonneg (show 0 ≤ (l : ℝ) - d - 1 by linarith)
          (show 0 ≤ (l : ℝ) - d - 2 by linarith)]
    apply h.trans
    rw [mul_assoc, ← exp_nat_mul, ← exp_add, hcast]
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hh ht0]
  have hgi : Set.InjOn (fun l : ℕ => l - d - 1) (↑s) := by
    intro l hl l' hl' he
    have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1).1
    have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hl').1).1
    change l - d - 1 = l' - d - 1 at he
    omega
  exact (farSum_le_geometric _ hgi (by positivity) (exp_nonneg _) hq hb).trans_lt
    (farMiddleTail_constant ht)

/-- Total of the small-radius competitors, including the possible zero-shift square. -/
theorem farSmallRadiusTail (hc : FarCoefficientBounds) {n d : ℕ} (hn : 6401 ≤ n)
    (hd : 1 ≤ d) (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) :
    (∑ l ∈ (Finset.Icc (d + 1) n.sqrt).filter (fun l => ¬ farRadius n d / 2 ≤ farRadius n l),
      farRatio n d l) < 0.105 := by
  let f := farRadius n d
  let s := (Finset.Icc (d + 1) n.sqrt).filter (fun l => ¬ farRadius n d / 2 ≤ farRadius n l)
  let E := 16.82 * exp (-(π * f / (4 * sqrt 3)))
  have hb (l : ℕ) (hl : l ∈ s) : farRatio n d l ≤ E := by
    obtain ⟨⟨hld, hlm⟩, hsmall⟩ := (Finset.mem_filter.mp hl).imp_left Finset.mem_Icc.mp
    have hs := (pow_le_pow_left₀ (Nat.zero_le l) hlm 2).trans (Nat.sqrt_le' n)
    rcases lt_or_eq_of_le hs with hlt | heq
    · exact (farRatio_smallRadius hc hn hd hdm hfar hlt (lt_of_not_ge hsmall)).le
    · exact (farRatio_squareEndpoint hc hn hd hdm hfar heq.symm hlm).2.2.le
  have hcard : s.card ≤ n.sqrt - d := by
    have h := Finset.card_filter_le (s := Finset.Icc (d + 1) n.sqrt)
      (p := fun l => ¬ farRadius n d / 2 ≤ farRadius n l)
    rwa [Nat.card_Icc, Nat.add_sub_add_right] at h
  have hf := farRadius_pos (cast_sq_lt_of_lt_sqrt hdm)
  have hy := outerY_gt80 hn
  have hflo := (farParameters_of_size hn hdm).2.2.2.1
  have hj := (farParameters_of_threshold hn hd hdm hfar).2.2
  calc
    _ ≤ ∑ _l ∈ s, E := Finset.sum_le_sum hb
    _ = (s.card : ℝ) * E := by simp
    _ ≤ ((n.sqrt - d : ℕ) : ℝ) * E :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by dsimp only [E]; positivity)
    _ < _ := farSmallTail_constant hy.le hflo.le hf.le hj.le

/-- Lemma 4.3 conditional on the two-colour estimates, with the threshold included. -/
theorem singleMonomialDominates (hc : FarCoefficientBounds) {n d : ℕ} (hn : 6401 ≤ n)
    (hd : 1 ≤ d) (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) :
    (∑ l ∈ (Finset.Icc 1 n.sqrt).erase d, farWeighted n l (farSample n d)) <
      farWeighted n d (farSample n d) := by
  have hpos := farWeighted_central_pos hc hn hd hdm hfar
  let A := Finset.Ico 1 d
  let B := Finset.Icc (d + 1) n.sqrt
  have hu : A ∪ B = (Finset.Icc 1 n.sqrt).erase d := by
    ext l
    simp only [A, B, Finset.mem_union, Finset.mem_Ico, Finset.mem_Icc, Finset.mem_erase]
    omega
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    have h1' := (Finset.mem_Ico.mp h1).2
    have h2' := (Finset.mem_Icc.mp h2).1
    omega
  have ha := farUpperIndexTail hc hn hd hdm hfar
  have hb := farHalfRadiusTail hc hn hd hdm hfar
  have hs := farSmallRadiusTail hc hn hd hdm hfar
  have hsum : (∑ l ∈ (Finset.Icc 1 n.sqrt).erase d, farRatio n d l) < 1 := by
    rw [← hu, Finset.sum_union hdis, ← Finset.sum_filter_add_sum_filter_not B
      (fun l => farRadius n d / 2 ≤ farRadius n l)]
    change (∑ l ∈ Finset.Ico 1 d, farRatio n d l) +
      ((∑ l ∈ (Finset.Icc (d + 1) n.sqrt).filter (fun l => farRadius n d / 2 ≤ farRadius n l),
        farRatio n d l) +
      ∑ l ∈ (Finset.Icc (d + 1) n.sqrt).filter (fun l => ¬ farRadius n d / 2 ≤ farRadius n l),
        farRatio n d l) < 1
    linarith
  simp only [farRatio, ← Finset.sum_div] at hsum
  exact (div_lt_one hpos).mp hsum

theorem farSample_sign_of_coefficientBounds (hc : FarCoefficientBounds) {n d : ℕ}
    (hn : 6401 ≤ n) (hd : 1 ≤ d) (hdm : d < n.sqrt)
    (hfar : farThreshold n ≤ farSample n d) :
    0 < (-1 : ℝ) ^ d * Step08.durfeeNegativeValue n (exp (farSample n d / 2)) :=
  farSign_of_dominance (by omega) (Finset.mem_Icc.mpr ⟨hd, hdm.le⟩)
    (singleMonomialDominates hc hn hd hdm hfar)

end DurfeeCCS.Step10
