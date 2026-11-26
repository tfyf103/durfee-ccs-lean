module

public import DurfeeCCS.Step10.OuterFarCoefficients
public import DurfeeCCS.Step10.OuterFarNumerics
public import DurfeeCCS.Step10.OuterCoeffData
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Bound the loss from restricting the two colours to the central Durfee size. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Step06 Finset Set

/-- The coefficient bounds used in the proof of Lemma 4.3, stated independently of
the method of obtaining the Rademacher coefficient estimate. -/
def FarCoefficientBounds : Prop :=
  (∀ t : ℕ, 0 < t → (twoColourPartitionCount t : ℝ) ≤ 2.6 * outerComparisonB (twoColourShift t)) ∧
  (∀ t : ℕ, 25 ≤ t → (twoColourPartitionCount t : ℝ) ≤ 1.1 * outerComparisonB (twoColourShift t)) ∧
  (∀ t : ℕ, 100 ≤ t → 0.9 * outerComparisonB (twoColourShift t) ≤ (twoColourPartitionCount t : ℝ)) ∧
  (∀ t : ℕ, t < 25 → (twoColourPartitionCount t : ℝ) ≤ exp (10 * π / sqrt 3))

theorem outerComparisonB_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    outerComparisonB a / outerComparisonB b =
      (b / a) ^ (5 / 2 : ℝ) * exp (2 * π / sqrt 3 * (a - b)) := by
  rw [div_rpow hb.le ha.le, show 2 * π / sqrt 3 * (a - b) =
      2 * π * a / sqrt 3 - 2 * π * b / sqrt 3 by ring, exp_sub]
  unfold outerComparisonB
  have ha' : a ^ (5 / 2 : ℝ) ≠ 0 := (rpow_pos_of_pos ha _).ne'
  have hb' : b ^ (5 / 2 : ℝ) ≠ 0 := (rpow_pos_of_pos hb _).ne'
  have h3 : (3 : ℝ) ^ (3 / 4 : ℝ) ≠ 0 := by positivity
  field_simp

private def outerLogB (x : ℝ) : ℝ :=
  2 * π / sqrt 3 * sqrt (x - 1 / 12) -
    (log (4 * (3 : ℝ) ^ (3 / 4 : ℝ)) + 5 / 4 * log (x - 1 / 12))

private theorem outerLogB_eq {x : ℝ} (hx : 1 / 12 < x) :
    outerLogB x = log (outerComparisonB (sqrt (x - 1 / 12))) := by
  have h : 0 < x - 1 / 12 := sub_pos.mpr hx
  have hsq : 0 < sqrt (x - 1 / 12) := sqrt_pos.mpr h
  unfold outerLogB outerComparisonB
  have hlog := log_mul (x := 4 * (3 : ℝ) ^ (3 / 4 : ℝ))
    (y := sqrt (x - 1 / 12) ^ (5 / 2 : ℝ)) (by positivity) (by positivity)
  rw [log_div (exp_ne_zero _) (by positivity), log_exp, hlog, log_rpow hsq, log_sqrt h.le]
  ring

private theorem outerLogB_Deriv {x : ℝ} (hx : 1 / 12 < x) :
    HasDerivAt outerLogB (π / (sqrt 3 * sqrt (x - 1 / 12)) - 5 / (4 * (x - 1 / 12))) x := by
  have hs : 0 < x - 1 / 12 := sub_pos.mpr hx
  have h := (hasDerivAt_id x).sub_const (1 / 12)
  have ha := (h.sqrt hs.ne').const_mul (2 * π / sqrt 3)
  have hb := (h.log hs.ne').const_mul (5 / 4)
  have ho := ha.sub (hb.const_add (log (4 * (3 : ℝ) ^ (3 / 4 : ℝ))))
  convert ho using 1
  · rfl
  · simp only [id_eq]
    field_simp

private theorem outerLogB_decrement {t v : ℝ} (hv : 25 ≤ v) (hvt : v ≤ t) :
    outerComparisonB (sqrt (v - 1 / 12)) ≤ outerComparisonB (sqrt (t - 1 / 12)) *
      exp (-(2 * π / (3 * sqrt 3 * sqrt (t - 1 / 12))) * (t - v)) := by
  let α := 2 * π / (3 * sqrt 3 * sqrt (t - 1 / 12))
  let F := fun x => outerLogB x - α * x
  have hd (x : ℝ) (hx : x ∈ Icc v t) :
      HasDerivAt F (π / (sqrt 3 * sqrt (x - 1 / 12)) -
        5 / (4 * (x - 1 / 12)) - α) x := by
    have hx' : v ≤ x := hx.1
    have h₁ := outerLogB_Deriv (show 1 / 12 < x by linarith)
    have h₂ := (hasDerivAt_id x).const_mul α
    convert h₁.sub h₂ using 1
    · rfl
    · rw [mul_one]
  have hmono : MonotoneOn F (Icc v t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc v t := interior_subset hx
      have h25 := hv.trans hx'.1
      have hh : 0 < x - 1 / 12 := by linarith
      have hxs := sqrt_pos.mpr hh
      have hsqx := sq_sqrt hh.le
      have hs3 := farSqrtThree_bounds.2
      have hπ := Real.pi_gt_three
      have hxl : (4.9 : ℝ) ≤ sqrt (x - 1 / 12) := le_sqrt_of_sq_le (by linarith)
      have hsm : 5 / (4 * sqrt (x - 1 / 12)) ≤ π / (3 * sqrt 3) := by
        calc
          _ ≤ (5 : ℝ) / (4 * 4.9) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
            gcongr
          _ ≤ 3 / (3 * 1.73205081) := by norm_num
          _ ≤ _ := by gcongr
      have hsub : 5 / (4 * (x - 1 / 12)) ≤ π / (3 * sqrt 3 * sqrt (x - 1 / 12)) := by
        have h' := div_le_div_of_nonneg_right hsm hxs.le
        rw [div_div, div_div, mul_assoc 4, ← pow_two, hsqx] at h'
        exact h'
      have halpha : α ≤ 2 * π / (3 * sqrt 3 * sqrt (x - 1 / 12)) := by
        unfold α
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
        exact hx'.2
      rw [(hd x hx').deriv]
      have heq : π / (sqrt 3 * sqrt (x - 1 / 12)) =
          3 * (π / (3 * sqrt 3 * sqrt (x - 1 / 12))) := by ring
      have heq' : 2 * π / (3 * sqrt 3 * sqrt (x - 1 / 12)) =
          2 * (π / (3 * sqrt 3 * sqrt (x - 1 / 12))) := by ring
      rw [heq'] at halpha
      rw [heq]
      linarith
  have h := hmono ⟨le_rfl, hvt⟩ ⟨hvt, le_rfl⟩ hvt
  dsimp only [F] at h
  rw [outerLogB_eq (show 1 / 12 < v by linarith),
    outerLogB_eq (show 1 / 12 < t by linarith)] at h
  have hlog : log (outerComparisonB (sqrt (v - 1 / 12))) ≤
      log (outerComparisonB (sqrt (t - 1 / 12))) + -α * (t - v) := by linarith
  have he := exp_le_exp.mpr hlog
  rw [exp_add, exp_log (outerComparisonB_pos (sqrt_pos.mpr (by linarith))),
    exp_log (outerComparisonB_pos (sqrt_pos.mpr (by linarith)))] at he
  exact he

private theorem farGeometricSum_bound {α : ℝ} (ha : 0 < α) (t : ℕ) :
    (∑ v ∈ Finset.Ico 25 (t + 1), exp (-α * ((t : ℝ) - v))) ≤ 1 + 1 / α := by
  have hsubset : Finset.Ico 25 (t + 1) ⊆ range (t + 1) := by
    intro v hv
    exact mem_range.mpr (Finset.mem_Ico.mp hv).2
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (f := fun v : ℕ => exp (-α * ((t : ℝ) - v))) (fun _ _ _ => exp_nonneg _)
  have hreflect :
      (∑ v ∈ range (t + 1), exp (-α * ((t : ℝ) - v))) =
        ∑ v ∈ range (t + 1), exp (-α) ^ v := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ t := by
      have hh := mem_range.mp hi
      omega
    rw [show t + 1 - 1 - i = t - i by omega, Nat.cast_sub hi', ← exp_nat_mul]
    congr 1
    ring
  rw [hreflect] at h1
  have hq : exp (-α) < 1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hseries := summable_geometric_of_lt_one (exp_nonneg _) hq
  have h2 := hseries.sum_le_tsum (range (t + 1)) (fun i _ => pow_nonneg (exp_nonneg _) i)
  rw [tsum_geometric_of_lt_one (exp_nonneg _) hq] at h2
  refine h1.trans (h2.trans ?_)
  rw [exp_neg]
  have hex : α + 1 ≤ exp α := add_one_le_exp α
  have hs : 0 < exp α - 1 := sub_pos.mpr (one_lt_exp_iff.mpr ha)
  have hd : 0 < 1 - (exp α)⁻¹ := by
    simpa only [exp_neg] using sub_pos.mpr hq
  rw [show (1 - (exp α)⁻¹)⁻¹ = exp α / (exp α - 1) by field_simp,
    show 1 + 1 / α = (α + 1) / α by field_simp]
  apply (div_le_div_iff₀ hs ha).mpr
  linarith

private theorem farCentralSize {n d : ℕ} (hn : 6401 ≤ n) (hdm : d < n.sqrt) :
    let t : ℕ := n - d ^ 2 - d - 1
    (78 : ℕ) < t ∧ (d : ℝ) + 1 ≤ 2 * ((t : ℝ) - 1 / 12) ∧
      ((t : ℝ) - 1 / 12) + ((d : ℝ) + 1) = farRadius n d ^ 2 ∧
      (100 : ℕ) ≤ n - d ^ 2 := by
  dsimp only
  let t : ℕ := n - d ^ 2 - d - 1
  let m := n.sqrt
  let f := farRadius n d
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have h80 := outerY_gt80 hn
  obtain ⟨hm, _, _, hflo, _⟩ := farParameters_of_size hn hdm
  have hm80 : (79 : ℝ) < m := by change (79 : ℝ) < n.sqrt; linarith
  have h1 : (d : ℝ) + 1 ≤ m := by exact_mod_cast (show d + 1 ≤ m from hdm)
  have hn2 : (m : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hdiff0 : 0 ≤ (m : ℝ) - (d : ℝ) - 1 := by linarith
  have hdiff1 : 0 ≤ (m : ℝ) + (d : ℝ) := by positivity
  have hmlo : (m : ℝ) - 1 ≤ (n : ℝ) - (d : ℝ) ^ 2 - (d : ℝ) - 1 :=
    by nlinarith [mul_nonneg hdiff0 hdiff1]
  have hin : (d : ℝ) ^ 2 + d + 1 ≤ n := by linarith
  have hint : d ^ 2 + d + 1 ≤ n := by exact_mod_cast hin
  have htcast : (t : ℝ) = (n : ℝ) - (d : ℝ) ^ 2 - (d : ℝ) - 1 := by
    simp only [t, Nat.cast_sub (show 1 ≤ n - d ^ 2 - d by omega),
      Nat.cast_sub (show d ≤ n - d ^ 2 by omega), Nat.cast_sub hds.le, Nat.cast_pow, Nat.cast_one]
  have htf : (t : ℝ) - 1 / 12 + ((d : ℝ) + 1) = f ^ 2 := by
    rw [htcast, farRadius_sq hds, outerY_sq (by omega : 0 < n)]
    ring
  have ht : (78 : ℝ) < t := by linarith
  have hrec : (d : ℝ) + 1 ≤ 2 * ((t : ℝ) - 1 / 12) := by linarith
  have hn100 : (100 : ℝ) ≤ (n : ℝ) - (d : ℝ) ^ 2 := by
    rw [farRadius_sq hds, outerY_sq (by omega : 0 < n)] at hflo
    linarith
  refine ⟨by exact_mod_cast ht, hrec, htf, ?_⟩
  exact_mod_cast (show (100 : ℝ) ≤ ((n - d ^ 2 : ℕ) : ℝ) by rwa [Nat.cast_sub hds.le, Nat.cast_pow])

/-- The normalized losses in the central coefficient, for sizes at least 25 and below 25. -/
theorem farCentral_lossParts (hc : FarCoefficientBounds) {n d : ℕ} (hn : 6401 ≤ n)
    (hd : 1 ≤ d) (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) :
    let t : ℕ := n - d ^ 2 - d - 1
    let f := farRadius n d
    2 / (0.9 * outerComparisonB f) *
        (∑ v ∈ Finset.Ico 25 (t + 1), (twoColourPartitionCount v : ℝ)) < 0.026053 ∧
      2 / (0.9 * outerComparisonB f) *
        (∑ v ∈ range 25, (twoColourPartitionCount v : ℝ)) < 4e-7 := by
  dsimp only
  let t : ℕ := n - d ^ 2 - d - 1
  let f := farRadius n d
  let g := twoColourShift t
  let h := farSample n d
  let y := outerY n
  let w := y ^ (1 / 3 : ℝ)
  let α := 2 * π / (3 * sqrt 3 * g)
  obtain ⟨ht, hrec, hshift, _⟩ := farCentralSize hn hdm
  have ht0 : 0 < t := by change 0 < n - d ^ 2 - d - 1; omega
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have hf : 0 < f := farRadius_pos hds
  have hg : 0 < g := twoColourShift_pos ht0
  have hg2 : g ^ 2 = (t : ℝ) - 1 / 12 := twoColourShift_sq ht0
  change (d : ℝ) + 1 ≤ 2 * ((t : ℝ) - 1 / 12) at hrec
  change (t : ℝ) - 1 / 12 + ((d : ℝ) + 1) = f ^ 2 at hshift
  have hglt : g < f := by nlinarith
  have hα : 0 < α := by dsimp only [α]; positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hpos : 0 < h := by unfold h farSample; change 0 < 2 * π * (d : ℝ) / (sqrt 3 * f); positivity
  have hy80 : 80 < y := outerY_gt80 hn
  have hy : 0 < y := by linarith
  have hw : 0 < w := rpow_pos_of_pos hy _
  have hwc : w ^ 3 = y := farCube_eq hy.le
  obtain ⟨_, _, hdy, hflo, _⟩ := farParameters_of_size hn hdm
  change (d : ℝ) < y at hdy
  change 1.96 * y < f ^ 2 at hflo
  have hf1252 : 12.52 ≤ f := by
    by_contra! h'
    nlinarith [pow_lt_pow_left₀ h' hf.le (by decide : 2 ≠ 0)]
  change 4 * w ≤ h at hfar
  have hrpow : (f / g) ^ (5 / 2 : ℝ) ≤ (3 : ℝ) ^ (5 / 4 : ℝ) := by
    have hs3 := sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hfg : f ≤ sqrt 3 * g := by
      by_contra! hp
      have hp2 := pow_lt_pow_left₀ hp (by positivity : 0 ≤ sqrt 3 * g) (by decide : 2 ≠ 0)
      rw [mul_pow, hs3] at hp2
      nlinarith
    have hdiv := (div_le_iff₀ hg).mpr hfg
    calc
      _ ≤ (sqrt 3) ^ (5 / 2 : ℝ) := rpow_le_rpow (by positivity) hdiv (by norm_num)
      _ = _ := by rw [sqrt_eq_rpow, ← rpow_mul (by norm_num), show (1 / 2 : ℝ) * (5 / 2) = 5 / 4 by norm_num]
  have hdec : 2 * π / sqrt 3 * (g - f) ≤ -h / 2 := by
    have hsg : 0 < sqrt (3 : ℝ) := by positivity
    have hh : f * (f - g) ≥ (d : ℝ) / 2 := by
      have hs := mul_le_mul_of_nonneg_right (show f + g ≤ 2 * f by linarith)
        (sub_nonneg.mpr hglt.le)
      nlinarith
    unfold h farSample
    change 2 * π / sqrt 3 * (g - f) ≤ -(2 * π * (d : ℝ) / (sqrt 3 * f)) / 2
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hh pi_pos.le]
  have hrem : 1 / α ≤ 3 * y / h := by
    have hs3 : 0 < sqrt (3 : ℝ) := by positivity
    have hinv : 1 / α = 3 * sqrt 3 * g / (2 * π) := by unfold α; rw [one_div_div]
    calc
      _ = 3 * sqrt 3 * g / (2 * π) := hinv
      _ ≤ 3 * sqrt 3 * f / (2 * π) := by gcongr
      _ = 3 * (d : ℝ) / h := by
        unfold h farSample
        change _ = 3 * (d : ℝ) / (2 * π * (d : ℝ) / (sqrt 3 * f))
        field_simp
      _ ≤ _ := by gcongr
  have hhbound : (1 + 1 / α) * exp (-h / 2) ≤
      (1 + 3 / 4 * w ^ 2) * exp (-2 * w) := by
    apply mul_le_mul
    · apply add_le_add_right (hrem.trans ?_)
      calc
        _ ≤ 3 * y / (4 * w) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hfar
        _ = _ := by rw [← hwc]; field_simp
    · exact exp_le_exp.mpr (by linarith)
    · positivity
    · positivity
  have hhterm (v : ℕ) (hv : v ∈ Finset.Ico 25 (t + 1)) :
      (twoColourPartitionCount v : ℝ) ≤
        (1.1 * outerComparisonB g) * exp (-α * ((t : ℝ) - v)) := by
    obtain ⟨hv25, hvt⟩ := Finset.mem_Ico.mp hv
    have h₁ : (25 : ℝ) ≤ v := by exact_mod_cast hv25
    have h₂ : (v : ℝ) ≤ t := by exact_mod_cast (show v ≤ t by omega)
    calc
      _ ≤ 1.1 * outerComparisonB (twoColourShift v) := hc.2.1 v hv25
      _ ≤ 1.1 * (outerComparisonB g * exp (-α * ((t : ℝ) - v))) := by
        exact mul_le_mul_of_nonneg_left (outerLogB_decrement h₁ h₂) (by norm_num)
      _ = _ := by ring
  have hb : 0 < outerComparisonB f := outerComparisonB_pos hf
  have hb' : 0 < outerComparisonB g := outerComparisonB_pos hg
  have hbh : (∑ v ∈ Finset.Ico 25 (t + 1), (twoColourPartitionCount v : ℝ)) ≤
      1.1 * outerComparisonB g * (1 + 1 / α) := by
    calc
      _ ≤ ∑ v ∈ Finset.Ico 25 (t + 1),
          (1.1 * outerComparisonB g) * exp (-α * ((t : ℝ) - v)) := Finset.sum_le_sum hhterm
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (farGeometricSum_bound hα t) (by positivity)
  have hbl : (∑ v ∈ range 25, (twoColourPartitionCount v : ℝ)) ≤
      25 * exp (10 * π / sqrt 3) := by
    calc
      _ ≤ ∑ _v ∈ range 25, exp (10 * π / sqrt 3) :=
        Finset.sum_le_sum fun v hv => hc.2.2.2 v (mem_range.mp hv)
      _ = _ := by simp
  constructor
  · calc
      _ ≤ 2 / (0.9 * outerComparisonB f) * (1.1 * outerComparisonB g * (1 + 1 / α)) :=
        mul_le_mul_of_nonneg_left hbh (by positivity)
      _ = (2.2 / 0.9) * ((f / g) ^ (5 / 2 : ℝ) *
          ((1 + 1 / α) * exp (2 * π / sqrt 3 * (g - f)))) := by
        rw [show (f / g) ^ (5 / 2 : ℝ) * ((1 + 1 / α) * exp (2 * π / sqrt 3 * (g - f))) =
          ((f / g) ^ (5 / 2 : ℝ) * exp (2 * π / sqrt 3 * (g - f))) * (1 + 1 / α) by ring,
          ← outerComparisonB_ratio hg hf]
        ring
      _ ≤ (2.2 / 0.9) * ((3 : ℝ) ^ (5 / 4 : ℝ) *
          ((1 + 3 / 4 * w ^ 2) * exp (-2 * w))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul hrpow _ (by positivity) (by positivity)
        exact (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hdec) (by positivity)).trans hhbound
      _ < _ := by
        simpa only [mul_assoc] using farCentralHigh_constant (farCube_lower hy80.le)
  · calc
      _ ≤ 2 / (0.9 * outerComparisonB f) * (25 * exp (10 * π / sqrt 3)) :=
        mul_le_mul_of_nonneg_left hbl (by positivity)
      _ = (200 * (3 : ℝ) ^ (3 / 4 : ℝ) / 0.9) *
          (f ^ (5 / 2 : ℝ) * exp (2 * π * (5 - f) / sqrt 3)) := by
        rw [show 2 * π * (5 - f) / sqrt 3 = 10 * π / sqrt 3 - 2 * π * f / sqrt 3 by ring,
          exp_sub]
        unfold outerComparisonB
        field_simp
        ring
      _ < _ := farCentralLow_constant hf1252

/-- Complete central monomial lower bound, conditional on the coefficient estimates. -/
theorem farCentral_lower (hc : FarCoefficientBounds) {n d : ℕ} (hn : 6401 ≤ n)
    (hd : 1 ≤ d) (hdm : d < n.sqrt) (hfar : farThreshold n ≤ farSample n d) :
    0.875 * outerComparisonB (farRadius n d) < (p n d : ℝ) := by
  let t : ℕ := n - d ^ 2 - d - 1
  let f := farRadius n d
  have hds := cast_sq_lt_of_lt_sqrt hdm
  have hf : 0 < f := farRadius_pos hds
  have hb : 0 < outerComparisonB f := outerComparisonB_pos hf
  obtain ⟨ht, _, _, ht100⟩ := farCentralSize hn hdm
  obtain ⟨hi, hlo⟩ := farCentral_lossParts hc hn hd hdm hfar
  have hi' : 2 * (∑ v ∈ Finset.Ico 25 (t + 1), (twoColourPartitionCount v : ℝ)) <
      0.026053 * (0.9 * outerComparisonB f) := by
    exact (div_lt_iff₀ (by positivity : 0 < 0.9 * outerComparisonB f)).mp
      (by rw [div_mul_eq_mul_div] at hi; exact hi)
  have hlo' : 2 * (∑ v ∈ range 25, (twoColourPartitionCount v : ℝ)) <
      4e-7 * (0.9 * outerComparisonB f) := by
    exact (div_lt_iff₀ (by positivity : 0 < 0.9 * outerComparisonB f)).mp
      (by rw [div_mul_eq_mul_div] at hlo; exact hlo)
  have hcoeff := hc.2.2.1 (n - d ^ 2) ht100
  rw [show twoColourShift (n - d ^ 2) = f from farShift_eq hds] at hcoeff
  have hloss := (durfeeCoeff_loss hds.le).2
  have htEq : n - d ^ 2 - d = t + 1 := by
    dsimp only [t]
    omega
  rw [htEq, ← Finset.sum_range_add_sum_Ico _ (show 25 ≤ t + 1 by change 25 ≤ n - d ^ 2 - d - 1 + 1; omega)] at hloss
  change 0.875 * outerComparisonB f < (p n d : ℝ)
  linarith

end DurfeeCCS.Step10
