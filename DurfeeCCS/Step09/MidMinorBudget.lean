module

public import DurfeeCCS.Step09.MidMinorGrid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The finite and infinite sums of the smaller-arc mode bounds. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open DurfeeCCS.Step07

def midMinorWeightMode (j : ℕ) : ℝ := 2 * (19/20 : ℝ)^j / (j : ℝ)

def midMinorModeBudget (u t v : ℝ) : ℝ :=
  0.1 * (u * ‖midMinorMode 1 u t 0‖) +
    ∑' i : ℕ, midMinorWeightMode (i+1) * (u * ‖midMinorMode (i+1) u t v‖)

theorem midMinorModeBudget_neg (u t v : ℝ) :
    midMinorModeBudget u t (-v) = midMinorModeBudget u t v := by
  simp [midMinorModeBudget,midMinorMode_neg]

theorem summable_midMinorModeBudget {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t) (v : ℝ) :
    Summable (fun i : ℕ => midMinorWeightMode (i+1) * (u * ‖midMinorMode (i+1) u t v‖)) := by
  let α : ℝ := 19/20
  have hs := (summable_geometric_of_lt_one (show 0 ≤ α by norm_num [α])
    (show α < 1 by norm_num [α])).mul_right α |>.mul_left (2*(2+u))
  apply hs.of_nonneg_of_le (fun i => by unfold midMinorWeightMode; positivity)
  intro i
  have hj : (1 : ℝ) ≤ ((i+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
  have hj' : 0 < ((i+1 : ℕ) : ℝ) := by positivity
  have hS := scaled_mode_le_tail (v := v) (Nat.succ_pos i) hu ht
  have hW : midMinorWeightMode (i+1) ≤ 2 * α^(i+1) := by
    unfold midMinorWeightMode
    exact div_le_self (by positivity) hj
  have hD : (2 : ℝ) / ((i+1:ℕ):ℝ) ≤ 2 := div_le_self (by norm_num) hj
  have hL : u * ‖midMinorMode (i+1) u t v‖ ≤ 2+u :=
    hS.trans (add_le_add_left hD u)
  have h := mul_le_mul hW hL
    (mul_nonneg hu.le (norm_nonneg (midMinorMode (i+1) u t v))) (by positivity : 0 ≤ 2*α^(i+1))
  convert h using 1
  rw [pow_succ]
  ring

private theorem minor_tail_summable (ν : ℕ) :
    Summable (fun k : ℕ => (19/20 : ℝ)^(k+21) / ((k+21:ℕ):ℝ)^ν) := by
  let α : ℝ := 19/20
  have hs := (summable_geometric_of_lt_one (show 0 ≤ α by norm_num [α])
    (show α < 1 by norm_num [α])).mul_right (α^21)
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro k
  rw [pow_add]
  exact div_le_self (by positivity) (one_le_pow₀ (by exact_mod_cast (show 1 ≤ k+21 by omega)))

theorem midMinorModeBudget_tail {u t Y : ℝ} (hu : 0 < u) (ht : 0 ≤ t) (hY : u ≤ Y) (v : ℝ) :
    (∑' k : ℕ, midMinorWeightMode (k+21) * (u * ‖midMinorMode (k+21) u t v‖)) ≤
      4 * minorArcTailReal 2 + 2*Y*minorArcTailReal 1 := by
  let α : ℝ := 19/20
  have hS₁ := (minor_tail_summable 1).mul_left (2*Y)
  have hS₂ := (minor_tail_summable 2).mul_left 4
  have hQ := (summable_midMinorModeBudget hu ht v).comp_injective
    (add_left_injective (20:ℕ))
  have hQ' : Summable (fun k : ℕ => midMinorWeightMode (k+21) * (u * ‖midMinorMode (k+21) u t v‖)) := by
    refine hQ.congr (fun i => ?_)
    change midMinorWeightMode (i+20+1) * (u * ‖midMinorMode (i+20+1) u t v‖) = _
    rw [Nat.add_assoc]
  have h := hQ'.tsum_le_tsum (g := fun k : ℕ =>
    4*(α^(k+21)/((k+21:ℕ):ℝ)^2)+(2*Y)*(α^(k+21)/((k+21:ℕ):ℝ)^1)) ?_ (hS₂.add hS₁)
  · rw [hS₂.tsum_add hS₁, tsum_mul_left, tsum_mul_left] at h
    exact h
  · intro k
    let j := k+21
    have hj : 0 < j := by omega
    have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
    change midMinorWeightMode j * (u * ‖midMinorMode j u t v‖) ≤
      4 * (α ^ j / (j:ℝ)^2) + (2*Y)*(α^j/(j:ℝ)^1)
    calc
      _ ≤ midMinorWeightMode j * (2/j + Y) := mul_le_mul_of_nonneg_left
        ((scaled_mode_le_tail hj hu ht).trans (add_le_add_right hY _)) (by unfold midMinorWeightMode; positivity)
      _ = _ := by unfold midMinorWeightMode; dsimp [α]; field_simp; ring

private theorem midMinorModeBudget_constant {u t Y eₗ : ℝ} (hu : 0 < u) (ht : 0 ≤ t)
    (heₗ : 0 ≤ eₗ) (heₗ' : eₗ ≤ Real.exp (-t)) (hY : u ≤ Y) (hY' : Y ≤ 0.072) :
    0.1 * (u * ‖midMinorMode 1 u t 0‖) ≤ 0.2 + Y ^ 2 / 48 - 0.1 * eₗ := by
  have hε : eₗ ≤ 1 := heₗ'.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hY₀ := hu.le.trans hY
  have hsq := pow_le_pow_left₀ hY₀ hY' 2
  have hcut : ((1 : ℝ)*Y)^2 ≤ 24 := by norm_num at hsq ⊢; linarith
  have h := (scaled_mode_le_c (v := 0) (by decide : 0 < (1 : ℕ)) hu ht).trans
    (minorArc_c_increases 1 hu.le hY heₗ heₗ' (by simpa using hcut))
  have h' := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (0.1:ℝ))
  unfold minorArcCReal at h'
  norm_num at h' ⊢
  nlinarith only [h', mul_le_mul_of_nonneg_right hε (sq_nonneg Y)]

theorem midMinorModeBudget_le_row {u t v : ℝ} (hu : 0 < u) (ht : 0 ≤ t)
    (i : Fin 18)
    (heₗ : (if i.val < 17 then Real.exp (-((minorArcData i).right : ℝ)) else 0) ≤ Real.exp (-t))
    (heᵤ : Real.exp (-t) ≤ Real.exp (-((minorArcData i).left : ℝ)))
    (hY : u ≤ (minorArcYmax (minorArcData i) : ℝ)) (hmin : 8*u ≤ |v|) (hmax : |v| ≤ Real.pi) :
    midMinorModeBudget u t v ≤ minorArcQstarRow i := by
  classical
  let eₗ : ℝ := if i.val < 17 then Real.exp (-((minorArcData i).right : ℝ)) else 0
  let eᵤ := Real.exp (-((minorArcData i).left : ℝ))
  let Y := (minorArcYmax (minorArcData i) : ℝ)
  have heₗ₀ : 0 ≤ eₗ := by dsimp [eₗ]; split_ifs <;> positivity
  have hY' : Y ≤ 0.072 := by
    unfold Y minorArcYmax
    rw [Rat.cast_min]
    exact (min_le_left _ _).trans (by norm_num)
  have hb : midMinorModeBudget u t v = midMinorModeBudget u t |v| := by
    rcases le_total 0 v with hv|hv
    · rw [abs_of_nonneg hv]
    · rw [abs_of_nonpos hv,midMinorModeBudget_neg]
  rw [hb]
  let z := |v|
  let A (j : ℕ) := midMinorWeightMode (j+1) * (u * ‖midMinorMode (j+1) u t z‖)
  let qmax := (minorArcCandidates eₗ eᵤ Y).sup' (minorArcCandidates_nonempty eₗ eᵤ Y) id
  have hM : (∑ j ∈ Finset.range 20, A j) ≤ qmax := by
    by_cases hs : z ≤ Real.pi/320
    · refine le_trans (b := minorArcQSmall eᵤ) ?_ (Finset.le_sup' (f := id) ?_)
      · unfold minorArcQSmall
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left (scaled_mode_small_term (Nat.succ_pos i)
          (by have := Finset.mem_range.mp hi; omega) hu ht heᵤ hmin hs)
        unfold midMinorWeightMode
        positivity
      · exact Finset.mem_insert_self _ _
    · obtain ⟨k,hk,hkl,hkr⟩ := minorArcGrid_elementary_cover (lt_of_not_ge hs) hmax
      refine le_trans (b := minorArcQFinite eₗ eᵤ Y k.val) ?_ (Finset.le_sup' (f := id) ?_)
      · unfold minorArcQFinite
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left (scaled_mode_grid_term (Nat.succ_pos j)
          (by have := Finset.mem_range.mp hj; omega) hu ht heₗ₀ heₗ heᵤ hY hY' hmin hkl hkr)
        unfold midMinorWeightMode
        positivity
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩,rfl⟩)
  have hsum := (summable_midMinorModeBudget hu ht z).sum_add_tsum_nat_add 20
  change 0.1 * (u * ‖midMinorMode 1 u t 0‖) + ∑' j, A j ≤ minorArcFixedReal eₗ Y + qmax
  change (∑ j ∈ Finset.range 20, A j) + (∑' j, A (j+20)) = ∑' j, A j at hsum
  rw [← hsum]
  have htail := midMinorModeBudget_tail hu ht hY z
  have htA : (∑' j, A (j+20)) = ∑' j : ℕ,
      midMinorWeightMode (j+21) * (u * ‖midMinorMode (j+21) u t z‖) := by
    simp only [A, Nat.add_assoc]
  rw [htA]
  unfold minorArcFixedReal
  linarith only [hM,htail,midMinorModeBudget_constant hu ht heₗ₀ heₗ hY hY']

end DurfeeCCS.Step09
