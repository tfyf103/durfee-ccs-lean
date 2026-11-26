module

public import DurfeeCCS.Step09.MidMinorEnvelope
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Connecting the angle bounds for the actual modes to the rational grid in (64). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Set DurfeeCCS.Step07

theorem minorArc_exact_sine_le {j k : ℕ} {v : ℝ}
    (hl : (k : ℝ) * Real.pi / 1600 ≤ v)
    (hh : v ≤ ((k + 1 : ℕ) : ℝ) * Real.pi / 1600) :
    minorArcExactSin j k ≤ |Real.sin ((j : ℝ) * v / 2)| := by
  unfold minorArcExactSin
  split_ifs with hq
  · let l : ℝ := (j : ℝ) * k * Real.pi / 3200
    let h : ℝ := (j : ℝ) * (k + 1 : ℕ) * Real.pi / 3200
    let z : ℝ := (j : ℝ) * v / 2
    let q := j*k/3200
    let shift : ℝ := (q : ℝ) * Real.pi
    have hsL : shift ≤ l := by
      have hNat := Nat.div_mul_le_self (j*k) 3200
      have hReal : (q : ℝ)*3200 ≤ (j:ℝ)*(k:ℝ) := by exact_mod_cast hNat
      have hMul := mul_le_mul_of_nonneg_right hReal Real.pi_pos.le
      dsimp [shift,l]
      linarith only [hMul]
    have hsH : h ≤ shift + Real.pi := by
      have hNat := (Nat.lt_mul_div_succ (j*(k+1)) (by decide : 0 < 3200)).le
      rw [← hq] at hNat
      have hReal : (j:ℝ)*((k+1:ℕ):ℝ) ≤ 3200*((q:ℝ)+1) := by exact_mod_cast hNat
      have hMul := mul_le_mul_of_nonneg_right hReal Real.pi_pos.le
      dsimp [shift,h]
      linarith only [hMul]
    have hzL : l ≤ z := by
      have h := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) j)
      dsimp [l,z]; linarith only [h]
    have hzH : z ≤ h := by
      have hw := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) j)
      dsimp [h,z]; linarith only [hw]
    have hsin (x : ℝ) (hx₀ : shift ≤ x) (hx₁ : x ≤ shift + Real.pi) :
        |Real.sin x| = Real.sin (x-shift) := by
      nth_rw 1 [show x = (x - shift) + (q : ℤ) * Real.pi by push_cast; dsimp [shift]; ring]
      rw [Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
    change min |Real.sin l| |Real.sin h| ≤ |Real.sin z|
    rw [hsin l hsL (hzL.trans (hzH.trans hsH)), hsin h (hsL.trans (hzL.trans hzH)) hsH,
      hsin z (hsL.trans hzL) (hzH.trans hsH)]
    exact strictConcaveOn_sin_Icc.concaveOn.min_le_of_mem_Icc
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩
  · exact abs_nonneg _

theorem minorArcGrid_elementary_cover {v : ℝ} (hLow : Real.pi / 320 < v) (hHi : v ≤ Real.pi) :
    ∃ k : Fin 1600, 5 ≤ k.val ∧
      (k.val : ℝ) * Real.pi / 1600 ≤ v ∧ v ≤ (((k.val + 1 : ℕ) : ℝ) * Real.pi / 1600) := by
  by_cases hv : v = Real.pi
  · refine ⟨1599, by decide, ?_, ?_⟩ <;> rw [hv] <;> norm_num <;> linarith [Real.pi_pos]
  let k := ⌊1600 * v / Real.pi⌋₊
  have hu : 0 ≤ 1600 * v / Real.pi := by positivity [Real.pi_pos, lt_trans (by positivity : 0 < Real.pi/320) hLow]
  have hkLow : 5 ≤ k := by
    apply Nat.le_floor
    norm_num
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith only [hLow]
  have hk₁ : (k:ℝ) ≤ 1600*v/Real.pi := Nat.floor_le hu
  have hk₂ : (1600*v/Real.pi) < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hk' : k < 1600 := by
    have h : 1600 * v / Real.pi < 1600 := by
      apply (div_lt_iff₀ Real.pi_pos).mpr
      linarith [lt_of_le_of_ne hHi hv]
    exact_mod_cast hk₁.trans_lt h
  refine ⟨⟨k,hk'⟩,hkLow,?_,?_⟩
  · apply (div_le_iff₀ (by norm_num : 0 < (1600:ℝ))).mpr
    linarith only [(le_div_iff₀ Real.pi_pos).mp hk₁]
  · push_cast
    apply (le_div_iff₀ (by norm_num : 0 < (1600:ℝ))).mpr
    linarith only [(div_lt_iff₀ Real.pi_pos).mp hk₂]

theorem minorArcBReal_compare {j : ℕ} (hj : 0 < j) {e E u y z Z : ℝ}
    (he : 0 ≤ e) (hE : e ≤ E) (hu : 0 < u) (hy : u ≤ y)
    (hz : 0 < Z) (hZ : Z ≤ z) :
    minorArcBReal e u z j ≤ minorArcBReal E y Z j := by
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have hy' := hu.trans_le hy
  have hz' := hz.trans_le hZ
  have hSu : 0 < Real.sinh (j*u/2) := Real.sinh_pos_iff.mpr (by positivity)
  have hSy : 0 < Real.sinh (j*y/2) := Real.sinh_pos_iff.mpr (by positivity)
  have hS : Real.sinh (j*u/2) ≤ Real.sinh (j*y/2) := by
    apply Real.sinh_le_sinh.mpr
    gcongr
  have hR : Z / Real.sinh (j*y/2) ≤ z / Real.sinh (j*u/2) :=
    div_le_div₀ hz'.le hZ hSu hS
  have hR₂ := pow_le_pow_left₀ (show 0 ≤ Z / Real.sinh (j*y/2) by positivity) hR 2
  unfold minorArcBReal
  have hE₀ : 0 ≤ E := he.trans hE
  refine add_le_add ?_ ?_
  · exact div_le_div₀ (by positivity) (by gcongr) (by positivity) (by linarith only [hR₂])
  · exact div_le_div₀ (by positivity)
      (mul_le_mul hy (pow_le_pow_left₀ he hE _) (by positivity) hy'.le)
      (by positivity) (by linarith only [hZ])

private theorem minorArc_jCutoff {j : ℕ} {y : ℝ} (hj : j ≤ 20) (hy : 0 ≤ y) (hy' : y ≤ 0.072) :
    ((j : ℝ) * y)^2 ≤ 24 := by
  have hj' : (j : ℝ) ≤ 20 := by exact_mod_cast hj
  have h := mul_le_mul hj' hy' hy (by norm_num : (0:ℝ) ≤ 20)
  have hs := pow_le_pow_left₀ (show 0 ≤ (j:ℝ)*y by positivity) h 2
  norm_num at hs
  linarith only [hs]

theorem scaled_mode_grid_term {j k : ℕ} (hj₀ : 0 < j) (hj₁ : j ≤ 20)
    {u t v eₗ eᵤ yplus : ℝ} (hu : 0 < u) (ht : 0 ≤ t)
    (heₗ : 0 ≤ eₗ) (heₗ' : eₗ ≤ Real.exp (-t)) (heᵤ : Real.exp (-t) ≤ eᵤ)
    (hY : u ≤ yplus) (hY' : yplus ≤ 0.072) (hmin : 8 * u ≤ v)
    (hl : (k : ℝ) * Real.pi / 1600 ≤ v) (hh : v ≤ ((k+1:ℕ):ℝ)*Real.pi/1600) :
    u * ‖midMinorMode j u t v‖ ≤ minorArcExactTerm eₗ eᵤ yplus j k := by
  let y := min yplus (((k+1:ℕ):ℝ)*Real.pi/12800)
  let z := minorArcExactSin j k
  have hy : u ≤ y := le_min hY ((le_div_iff₀ (by norm_num : (0:ℝ)<12800)).mpr <| by
    linarith only [(le_div_iff₀ (by norm_num : (0:ℝ)<1600)).mp hh,hmin])
  have hzy := minorArc_exact_sine_le (j := j) hl hh
  have hsmall := minorArc_jCutoff hj₁ (hu.le.trans hy) ((min_le_left _ _).trans hY')
  have hc := (scaled_mode_le_c (v := v) hj₀ hu ht).trans
    (minorArc_c_increases j hu.le hy heₗ heₗ' hsmall)
  unfold minorArcExactTerm
  dsimp only
  split_ifs with hz
  · have hz' : 0 < |Real.sin ((j:ℝ)*v/2)| := lt_of_lt_of_le hz hzy
    exact le_min hc ((scaled_mode_le_b hj₀ hu ht hz').trans
      (minorArcBReal_compare hj₀ (Real.exp_nonneg _) heᵤ hu hy hz hzy))
  · exact hc

theorem scaled_mode_small_term {j : ℕ} (hj₀ : 0 < j) (hj₁ : j ≤ 20)
    {u t v eᵤ : ℝ} (hu : 0 < u) (ht : 0 ≤ t) (heᵤ : Real.exp (-t) ≤ eᵤ)
    (hmin : 8 * u ≤ v) (hh : v ≤ Real.pi/320) :
    let y₀ := Real.pi/2560
    u * ‖midMinorMode j u t v‖ ≤
      (2 / j + j * y₀ ^ 2 / 6) / (1 + (0.998*80*y₀ / Real.sinh (10*y₀)) ^ 2) +
        eᵤ^j/(0.998*8*j) := by
  let y₀ := Real.pi/2560
  let a : ℝ := j*u/2
  let z := |Real.sin ((j:ℝ)*v/2)|
  let x : ℝ := (j:ℝ)*v/2
  have hJ : 0 < (j : ℝ) := by exact_mod_cast hj₀
  have hJ' : (j:ℝ) ≤ 20 := by exact_mod_cast hj₁
  have hv : 0 < v := (by positivity : 0 < 8*u).trans_le hmin
  have hx : 0 < x := by dsimp [x]; positivity
  have hx' : x ≤ Real.pi/32 := by
    have h := mul_le_mul hJ' hh hv.le (by norm_num : (0:ℝ) ≤ 20)
    dsimp [x]
    linarith only [h]
  have hxnum : x ≤ 0.1 := by linarith [Real.pi_lt_d2]
  have hsin : 0.998*x ≤ Real.sin x := by
    have hs : x ^ 2 ≤ 0.012 := by
      have := pow_le_pow_left₀ hx.le hxnum 2
      norm_num at this
      linarith only [this]
    have hg := mul_le_mul_of_nonneg_left hs hx.le
    have := Real.sin_ge_sub_cube hx.le
    nlinarith only [hg,this]
  have hz : (0.998:ℝ)*4*(j:ℝ)*u ≤ z := calc
    _ ≤ 0.998 * x := by
      have h := mul_le_mul_of_nonneg_left hmin hJ.le
      dsimp [x]
      linarith only [h]
    _ ≤ _ := hsin.trans (le_abs_self _)
  have hz' : 0 < z := (by positivity : 0 < (0.998:ℝ)*4*(j:ℝ)*u).trans_le hz
  have hy : u ≤ y₀ := by dsimp [y₀]; linarith only [hmin,hh]
  have hy₀ : 0 < y₀ := by dsimp [y₀]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a ≤ 10*y₀ := by
    dsimp [a]
    have := mul_le_mul hJ' hy hu.le (by norm_num : (0:ℝ) ≤ 20)
    linarith only [this]
  have hS : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hS₀ : 0 < Real.sinh (10*y₀) := Real.sinh_pos_iff.mpr (by positivity)
  have hR : 0.998*80*y₀/Real.sinh (10*y₀) ≤ z/Real.sinh a := by
    have hm := midMinor_x_div_sinh_antitone ha (show (10*y₀ : ℝ) ∈ Ioi 0 from by
      change 0 < 10*y₀
      positivity) ha'
    have hc := mul_le_mul_of_nonneg_left hm (show 0 ≤ (0.998:ℝ)*8 by norm_num)
    calc
      _ = (0.998*8)*(10*y₀/Real.sinh (10*y₀)) := by ring
      _ ≤ (0.998*8)*(a/Real.sinh a) := hc
      _ ≤ _ := by rw [← mul_div_assoc]; gcongr; dsimp [a]; linarith only [hz]
  have hR₂ := pow_le_pow_left₀ (show 0 ≤ 0.998*80*y₀/Real.sinh (10*y₀) by positivity) hR 2
  exact (scaled_mode_le_b hj₀ hu ht hz').trans (by
    unfold minorArcBReal
    change (2/j+j*u^2/6)/(1+(z/Real.sinh a)^2) + u*(Real.exp (-t))^j/(2*z) ≤ _
    refine add_le_add (div_le_div₀ (by positivity) (by gcongr)
      (by positivity) (by linarith only [hR₂])) ?_
    have heᵤ₀ : 0 ≤ eᵤ := (Real.exp_nonneg _).trans heᵤ
    calc
      _ ≤ u*eᵤ^j/(2*(0.998*4*(j:ℝ)*u)) := div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_nonneg _) heᵤ _) hu.le)
        (by positivity) (mul_le_mul_of_nonneg_left hz (by norm_num))
      _ = _ := by field_simp; ring)

end DurfeeCCS.Step09
