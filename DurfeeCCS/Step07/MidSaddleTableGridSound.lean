module

public import DurfeeCCS.Step07.MidSaddleTableGrid
public import DurfeeCCS.Step07.TrigonometricBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Analytical enclosures used by the rational grid certificate for (64). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

theorem minorArc_fold_le_half (n : ℕ) : minorArcFold n ≤ 1600 := by
  unfold minorArcFold
  omega

/-- The certificate's polynomial is below every absolute sine value on its block. -/
theorem minorArc_sine_lower {j l u : ℕ} {v : ℝ}
    (hl : (l : ℝ) * Real.pi / 1600 ≤ v) (hu : v ≤ (u : ℝ) * Real.pi / 1600) :
    (minorArcSinLower j l u : ℝ) ≤ |Real.sin ((j : ℝ) * v / 2)| := by
  let d := minorArcBlockDist j l u
  let x := (3.141592 : ℝ) * d / 3200
  have hdist : d ≤ 1600 := by
    unfold d minorArcBlockDist
    split
    · exact (min_le_left _ _).trans (minorArc_fold_le_half _)
    · omega
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxpi : x ≤ Real.pi / 2 := by
    dsimp only [x]
    have hd' : (d : ℝ) ≤ 1600 := by exact_mod_cast hdist
    have hh : (3.141592 : ℝ) * d ≤ Real.pi * 1600 := by
      exact mul_le_mul Real.pi_gt_d6.le hd' (Nat.cast_nonneg d) Real.pi_pos.le
    linarith
  have hx2 : x ^ 2 ≤ 110 := by
    have hh : x ≤ 2 := hxpi.trans (by linarith [Real.pi_lt_d6])
    exact (pow_le_pow_left₀ hx0 hh 2).trans (by norm_num)
  have hcast :
      (minorArcSinLower j l u : ℝ) = x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 := by
    unfold minorArcSinLower x d
    push_cast
    norm_num
  rw [hcast]
  refine (sin_taylor_seven_lower hx0 hx2).trans ?_
  by_cases hf : (j * l) / 3200 = (j * u) / 3200
  · let k := (j * l) / 3200
    let f := (j * l) % 3200
    let g := (j * u) % 3200
    let s : ℝ := (j : ℝ) * v / 2 - (k : ℝ) * Real.pi
    have hlf : (j : ℝ) * l = f + 3200 * (k : ℝ) :=
      by exact_mod_cast (Nat.mod_add_div (j * l) 3200).symm
    have hug : (j : ℝ) * u = g + 3200 * (k : ℝ) := by
      have hg := (Nat.mod_add_div (j * u) 3200).symm
      rw [← hf] at hg
      exact_mod_cast hg
    have hle : (f : ℝ) * Real.pi / 3200 ≤ s := by
      have hs := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) j)
      dsimp only [s]
      nlinarith only [hs, congrArg (· * Real.pi) hlf]
    have hue : s ≤ (g : ℝ) * Real.pi / 3200 := by
      have hs := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) j)
      dsimp only [s]
      nlinarith only [hs, congrArg (· * Real.pi) hug]
    have hgl : (g : ℝ) ≤ 3200 := by exact_mod_cast (Nat.mod_lt (j * u) (by decide : 0 < 3200)).le
    have hs0 : 0 ≤ s := (show 0 ≤ (f : ℝ) * Real.pi / 3200 by positivity).trans hle
    have hspi : s ≤ Real.pi := by
      have hh := mul_le_mul_of_nonneg_right hgl Real.pi_pos.le
      linarith
    have hdf : d ≤ f := by
      unfold d minorArcBlockDist
      rw [ite_eq_left hf]
      exact (min_le_left _ _).trans (min_le_left _ _)
    have hdg : d ≤ 3200 - g := by
      unfold d minorArcBlockDist
      rw [ite_eq_left hf]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hx' : x ≤ (d : ℝ) * Real.pi / 3200 := by
      dsimp only [x]
      have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_d6.le (Nat.cast_nonneg (α := ℝ) d)
      linarith
    have hxs : x ≤ s :=
      hx'.trans ((by gcongr : (d : ℝ) * Real.pi / 3200 ≤ (f : ℝ) * Real.pi / 3200).trans hle)
    have hxt : x ≤ Real.pi - s := by
      have hdc : (d : ℝ) ≤ 3200 - (g : ℝ) := by
        have hg : g ≤ 3200 := by exact_mod_cast hgl
        have hnat : d + g ≤ 3200 := by omega
        have hreal : (d : ℝ) + (g : ℝ) ≤ 3200 := by exact_mod_cast hnat
        linarith
      have hh := mul_le_mul_of_nonneg_right hdc Real.pi_pos.le
      linarith
    have hfold : Real.sin (min s (Real.pi - s)) = Real.sin s := by
      rcases le_total s (Real.pi - s) with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, Real.sin_pi_sub]
    have hsmin : min s (Real.pi - s) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · exact le_min (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      · rcases le_total s (Real.pi / 2) with h | h
        · exact (min_le_left _ _).trans h
        · exact (min_le_right _ _).trans (by linarith)
    have hmono := Real.monotoneOn_sin
      (show x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], hxpi⟩)
      hsmin (le_min hxs hxt)
    have hs_eq : (j : ℝ) * v / 2 = s + (k : ℝ) * Real.pi := by dsimp [s]; ring
    simpa only [hfold, hs_eq, Real.sin_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hs0 hspi)] using hmono
  · have hxzero : x = 0 := by simp [x, d, minorArcBlockDist, hf]
    rw [hxzero, Real.sin_zero]
    exact abs_nonneg _

private theorem odd_factorial_lower (k : ℕ) : 6 ^ k ≤ (2 * k + 1).factorial := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ, show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    calc
      _ ≤ (2 * k + 1).factorial * 6 := Nat.mul_le_mul_right _ ih
      _ ≤ (2 * k + 1).factorial * ((2 * k + 1 + 1 + 1) * (2 * k + 1 + 1)) := by
        apply Nat.mul_le_mul_left
        calc
          6 = 3 * 2 := by decide
          _ ≤ _ := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring

/-- A geometric upper bound on sinh from its nonnegative odd power series. -/
theorem minorArc_sinh_upper {x : ℝ} (hx : 0 ≤ x) (hx2 : x ^ 2 < 6) :
    Real.sinh x ≤ x / (1 - x ^ 2 / 6) := by
  let r := x ^ 2 / 6
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  rw [Real.sinh_eq_tsum]
  calc
    _ ≤ ∑' k : ℕ, x * r ^ k := by
      apply (Real.hasSum_sinh x).summable.tsum_le_tsum _ ((summable_geometric_of_lt_one hr0 hr1).mul_left x)
      intro k
      have hk : (6 : ℝ) ^ k ≤ ((2 * k + 1).factorial : ℝ) := by
        exact_mod_cast odd_factorial_lower k
      dsimp only [r]
      rw [div_pow, ← mul_div_assoc, pow_succ, pow_mul, mul_comm _ x]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hk
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

theorem minorArc_sinh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have hex := Real.exp_lt_exp.mpr (show -x < x by linarith)
  linarith

theorem minorArc_sinh_mono {x y : ℝ} (hxy : x ≤ y) : Real.sinh x ≤ Real.sinh y := by
  rw [Real.sinh_eq, Real.sinh_eq]
  linarith [Real.exp_le_exp.mpr hxy, Real.exp_le_exp.mpr (neg_le_neg hxy)]


/-- The first entry c_j in (63). -/
def minorArcCReal (eps y : ℝ) (j : ℕ) : ℝ :=
  2 / j + j * y ^ 2 / 6 - (eps ^ j / j) * (1 - (j * y) ^ 2 / 24)

/-- The second entry b_j in (63). -/
def minorArcBReal (eps y z : ℝ) (j : ℕ) : ℝ :=
  (2 / j + j * y ^ 2 / 6) / (1 + (z / Real.sinh (j * y / 2)) ^ 2) + y * eps ^ j / (2 * z)

theorem minorArc_c_increases (j : ℕ) {e eₗ y yHi : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ yHi) (heₗ : 0 ≤ eₗ) (he : eₗ ≤ e)
    (hsmall : ((j : ℝ) * yHi) ^ 2 ≤ 24) :
    minorArcCReal e y j ≤ minorArcCReal eₗ yHi j := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hjy : 0 ≤ (j : ℝ) * y := mul_nonneg hj hy
  have hsmall₀ : 0 ≤ 1 - ((j : ℝ) * y) ^ 2 / 24 := by
    have h := (pow_le_pow_left₀ hjy (mul_le_mul_of_nonneg_left hy' hj) 2).trans hsmall
    linarith
  have he' : 0 ≤ e := heₗ.trans he
  have h₁ : minorArcCReal e y j ≤ minorArcCReal eₗ y j := by
    unfold minorArcCReal
    apply sub_le_sub_left
    gcongr
  refine h₁.trans ?_
  unfold minorArcCReal
  apply sub_le_sub
  · gcongr
  · gcongr

theorem minorArc_b_upper (j : ℕ) (hj : 0 < j) {e eHi y yHi z zₗ : ℝ}
    (hy : 0 < y) (hy' : y ≤ yHi) (he : 0 ≤ e) (he' : e ≤ eHi)
    (hz : 0 < zₗ) (hz' : zₗ ≤ z) (hsmall : ((j : ℝ) * yHi / 2) ^ 2 < 6) :
    minorArcBReal e y z j ≤
      let x := (j : ℝ) * yHi / 2
      (2 / j + j * yHi ^ 2 / 6) / (1 + (zₗ * (1 - x ^ 2 / 6) / x) ^ 2) + yHi * eHi ^ j / (2 * zₗ) := by
  let x := (j : ℝ) * yHi / 2
  let x₀ := (j : ℝ) * y / 2
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have hY : 0 < yHi := hy.trans_le hy'
  have hx : 0 < x := by dsimp [x]; positivity
  have hx₀ : 0 < x₀ := by dsimp [x₀]; positivity
  have hs : 0 < Real.sinh x₀ := minorArc_sinh_pos hx₀
  have hs' : Real.sinh x₀ ≤ x / (1 - x ^ 2 / 6) := calc
    _ ≤ Real.sinh x := minorArc_sinh_mono (by dsimp only [x₀, x]; gcongr)
    _ ≤ _ := minorArc_sinh_upper hx.le hsmall
  have hfac : 0 < 1 - x ^ 2 / 6 := by change x ^ 2 < 6 at hsmall; linarith
  have hrat : zₗ * (1 - x ^ 2 / 6) / x ≤ z / Real.sinh x₀ := calc
    _ = zₗ / (x / (1 - x ^ 2 / 6)) := by
      field_simp [hx.ne', hfac.ne']
    _ ≤ _ := div_le_div₀ (hz.le.trans hz') hz' hs hs'
  have hrat₀ : 0 ≤ zₗ * (1 - x ^ 2 / 6) / x := by positivity
  have hn : 0 ≤ (2 / (j : ℝ) + j * yHi ^ 2 / 6) := by positivity
  unfold minorArcBReal
  change _ ≤ (2 / j + j * yHi ^ 2 / 6) / (1 + (zₗ * (1 - x ^ 2 / 6) / x) ^ 2) +
    yHi * eHi ^ j / (2 * zₗ)
  apply add_le_add
  · exact div_le_div₀ hn (by gcongr) (by positivity)
      (add_le_add_right (pow_le_pow_left₀ hrat₀ hrat 2) _)
  have heHi : 0 ≤ eHi := he.trans he'
  · apply div_le_div₀ (by positivity) (by gcongr) (by positivity) (by linarith)

def minorArcTailReal (ν : ℕ) : ℝ :=
  ∑' k : ℕ, (19 / 20 : ℝ) ^ (k + 21) / ((k + 21 : ℕ) : ℝ) ^ ν

private theorem minorArc_tail_block_cast (ν k₀ : ℕ) :
    (minorArcTailBlock ν k₀ : ℝ) =
      ∑ k ∈ Finset.range 15, (19 / 20 : ℝ) ^ (k + k₀) / ((k + k₀ : ℕ) : ℝ) ^ ν := by
  rw [minorArcTailBlock, Rat.cast_list_sum, List.map_map, Finset.sum_list_map_count]
  rw [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [List.count_eq_one_of_mem List.nodup_range (by simpa using hi), one_nsmul]
  simp [Function.comp_apply]

/-- An upper bound on Tν with the first sixty terms and a geometric bound on the tail. -/
theorem minorArc_tail_sum {ν : ℕ} :
    minorArcTailReal ν ≤
      ((minorArcTailBlock ν 21 : ℚ) : ℝ) + ((minorArcTailBlock ν 36 : ℚ) : ℝ) +
      ((minorArcTailBlock ν 51 : ℚ) : ℝ) + ((minorArcTailBlock ν 66 : ℚ) : ℝ) +
      ((minorArcTailResidual ν : ℚ) : ℝ) := by
  let α : ℝ := 19 / 20
  let f (k : ℕ) : ℝ := α ^ (k + 21) / ((k + 21 : ℕ) : ℝ) ^ ν
  have hα₀ : 0 ≤ α := by norm_num [α]
  have hα₁ : α < 1 := by norm_num [α]
  have hgeo := summable_geometric_of_lt_one hα₀ hα₁
  have hf : Summable f := by
    apply (hgeo.mul_right (α ^ 21)).of_nonneg_of_le (fun _ => by dsimp [f, α]; positivity)
    intro k
    dsimp only [f]
    rw [pow_add]
    have hk : (1 : ℝ) ≤ ((k + 21 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k + 21 by omega)
    exact div_le_self (by positivity) (one_le_pow₀ hk)
  have hsum :
      (∑ k ∈ Finset.range 60, f k) =
        ((minorArcTailBlock ν 21 : ℚ) : ℝ) + ((minorArcTailBlock ν 36 : ℚ) : ℝ) +
        ((minorArcTailBlock ν 51 : ℚ) : ℝ) + ((minorArcTailBlock ν 66 : ℚ) : ℝ) := by
    rw [show (60 : ℕ) = ((15 + 15) + 15) + 15 by decide,
      Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
    simp only [minorArc_tail_block_cast, f, α]
    congr 1
  have hrem : (∑' k, f (k + 60)) ≤ (minorArcTailResidual ν : ℝ) := by
    calc
      _ ≤ ∑' k : ℕ, α ^ k * (α ^ 81 / (81 : ℝ) ^ ν) := by
        apply ((summable_nat_add_iff 60).2 hf).tsum_le_tsum _ (hgeo.mul_right _)
        intro k
        dsimp only [f]
        rw [show k + 60 + 21 = k + 81 by omega, pow_add, ← mul_div_assoc]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
        exact_mod_cast (show 81 ≤ k + 81 by omega)
      _ = _ := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hα₀ hα₁, minorArcTailResidual]
        push_cast
        dsimp [α]
        ring
  change (∑' k, f k) ≤ _
  rw [← hf.sum_add_tsum_nat_add 60, hsum]
  exact add_le_add_right hrem _

theorem minorArc_tail_one : minorArcTailReal 1 < 0.20195 := by
  have ⟨ha, hb, hc, hd, he⟩ := minorArc_tail_arithmetic_one
  have a : (minorArcTailBlock 1 21 : ℝ) < 0.138489947 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr ha
  have b : (minorArcTailBlock 1 36 : ℝ) < 0.040684031 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr hb
  have c : (minorArcTailBlock 1 51 : ℝ) < 0.013828993 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr hc
  have d : (minorArcTailBlock 1 66 : ℝ) < 0.005062682 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr hd
  have e : (minorArcTailResidual 1 : ℝ) < 0.003873977 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr he
  linarith [minorArc_tail_sum (ν := 1)]

theorem minorArc_tail_two : minorArcTailReal 2 < 0.006725 := by
  have ⟨ha, hb, hc, hd, he⟩ := minorArc_tail_arithmetic_two
  have a : (minorArcTailBlock 2 21 : ℝ) < 0.005373340 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr ha
  have b : (minorArcTailBlock 2 36 : ℝ) < 0.000987032 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr hb
  have c : (minorArcTailBlock 2 51 : ℝ) < 0.000245052 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr hc
  have d : (minorArcTailBlock 2 66 : ℝ) < 0.000070748 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr hd
  have e : (minorArcTailResidual 2 : ℝ) < 0.000047827 := by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).mpr he
  linarith [minorArc_tail_sum (ν := 2)]


theorem minorArc_eps_upper (r : Fin 18) :
    Real.exp (-((minorArcData r).left : ℝ)) ≤ (minorArcData r).epsUpper := by
  fin_cases r <;> simp only [minorArcData, Rat.cast_ofScientific]
  all_goals dyadic_interval +kernel [prec := 55]

theorem minorArc_eps_lower (r : Fin 18) (hr : r.val < 17) :
    ((minorArcData r).epsLower : ℝ) ≤ Real.exp (-((minorArcData r).right : ℝ)) := by
  fin_cases r <;> norm_num at hr
  all_goals simp only [minorArcData]
  all_goals dyadic_interval +kernel [prec := 55]

/-- The exact endpoint sine minimum used for elementary interval k. -/
def minorArcExactSin (j k : ℕ) : ℝ :=
  if j * k / 3200 = j * (k + 1) / 3200 then
    min |Real.sin ((j : ℝ) * k * Real.pi / 3200)|
      |Real.sin ((j : ℝ) * (k + 1 : ℕ) * Real.pi / 3200)|
  else 0

theorem minorArc_block_sine_lower {j l u k : ℕ} (hlk : l ≤ k) (hku : k + 1 ≤ u) :
    (minorArcSinLower j l u : ℝ) ≤ minorArcExactSin j k := by
  by_cases hf : j * l / 3200 = j * u / 3200
  · have hfk : j * k / 3200 = j * (k + 1) / 3200 := by
      have hl := Nat.div_le_div_right (Nat.mul_le_mul_left j hlk) (c := 3200)
      have hu := Nat.div_le_div_right (Nat.mul_le_mul_left j hku) (c := 3200)
      have hm : j * k / 3200 ≤ j * (k + 1) / 3200 :=
        Nat.div_le_div_right (Nat.mul_le_mul_left j (Nat.le_succ k))
      omega
    rw [minorArcExactSin, ite_eq_left hfk]
    apply le_min
    · have h := minorArc_sine_lower (j := j) (l := l) (u := u)
          (v := (k : ℝ) * Real.pi / 1600) (by gcongr) (by gcongr; exact_mod_cast (show k ≤ u by omega))
      convert h using 3; ring
    · have h := minorArc_sine_lower (j := j) (l := l) (u := u)
          (v := ((k + 1 : ℕ) : ℝ) * Real.pi / 1600)
          (by gcongr; exact_mod_cast (show l ≤ k + 1 by omega)) (by gcongr)
      convert h using 3; ring
  · simp [minorArcSinLower, minorArcBlockDist, hf, minorArcExactSin]
    split <;> positivity

/-- The elementary q_k term of (64) before multiplication by 2α^j/j. -/
def minorArcExactTerm (epsₗ epsᵤ yplus : ℝ) (j k : ℕ) : ℝ :=
  let y := min yplus (((k + 1 : ℕ) : ℝ) * Real.pi / 12800)
  let z := minorArcExactSin j k
  let c := minorArcCReal epsₗ y j
  if 0 < z then min c (minorArcBReal epsᵤ y z j) else c

theorem minorArc_block_term_bound
    (row : MinorArcData) {j l u k : ℕ} (hj : 0 < j) (hj' : j ≤ 20) (hk : 5 ≤ k)
    (hlk : l ≤ k) (hku : k + 1 ≤ u)
    {epsₗ epsᵤ yplus : ℝ} (hY : 0 < yplus) (hY' : yplus ≤ minorArcYmax row)
    (heₗ : 0 ≤ row.epsLower) (heₗ' : (row.epsLower : ℝ) ≤ epsₗ)
    (heᵤ : 0 ≤ epsᵤ) (heᵤ' : epsᵤ ≤ (row.epsUpper : ℝ)) :
    minorArcExactTerm epsₗ epsᵤ yplus j k ≤ (minorArcBlockTerm row l u j : ℝ) := by
  let Y := min (minorArcYmax row : ℝ) ((3.141593 : ℝ) * u / 12800)
  let y := min yplus (((k + 1 : ℕ) : ℝ) * Real.pi / 12800)
  let z := minorArcExactSin j k
  let Z := (minorArcSinLower j l u : ℝ)
  let C := minorArcCReal (row.epsLower : ℝ) Y j
  let c := minorArcCReal epsₗ y j
  have hy : 0 < y := lt_min hY (by positivity)
  have hYd : y ≤ Y := by
    apply min_le_min hY'
    have hh : (((k + 1 : ℕ) : ℝ) * Real.pi) ≤ (u : ℝ) * 3.141593 :=
      mul_le_mul (by exact_mod_cast hku) Real.pi_lt_d6.le Real.pi_pos.le (Nat.cast_nonneg _)
    linarith
  have hYmax : Y ≤ (0.072 : ℝ) := by
    have h := min_le_left (0.072 : ℚ) (row.amplitude / 80)
    have h' : (minorArcYmax row : ℝ) ≤ ((0.072 : ℚ) : ℝ) := Rat.cast_le.mpr h
    exact (min_le_left _ _).trans (by simpa only [Rat.cast_ofScientific] using h')
  have hYpos : 0 < Y := hy.trans_le hYd
  have hjcast : (j : ℝ) ≤ 20 := by exact_mod_cast hj'
  have hjY : 0 ≤ (j : ℝ) * Y := by positivity
  have hjY' : (j : ℝ) * Y ≤ 20 * 0.072 :=
    mul_le_mul hjcast hYmax hYpos.le (by norm_num)
  have hjsq : ((j : ℝ) * Y) ^ 2 ≤ 24 :=
    (pow_le_pow_left₀ hjY hjY' 2).trans (by norm_num)
  have hjsq' : ((j : ℝ) * Y / 2) ^ 2 < 6 := by
    have hh := pow_le_pow_left₀ hjY hjY' 2
    nlinarith only [hh]
  have hc : c ≤ C := minorArc_c_increases j hy.le hYd (by exact_mod_cast heₗ) heₗ' hjsq
  have hz : Z ≤ z := minorArc_block_sine_lower hlk hku
  have hcast :
      (minorArcBlockTerm row l u j : ℝ) =
      if 0 < Z then
        min C ((2 / j + j * Y ^ 2 / 6) / (1 + (Z * (1 - ((j : ℝ) * Y / 2) ^ 2 / 6) /
          ((j : ℝ) * Y / 2)) ^ 2) + Y * (row.epsUpper : ℝ) ^ j / (2 * Z))
      else C := by
    by_cases hz' : 0 < minorArcSinLower j l u
    · have hzR : 0 < Z := Rat.cast_pos.mpr hz'
      simp only [minorArcBlockTerm, ite_eq_left hz', ite_eq_left hzR, Rat.cast_min, C, Y, Z,
        minorArcC, minorArcBupper, minorArcCReal]
      push_cast
      norm_num
    · have hzR : ¬ (0 < Z) := fun hp => hz' (Rat.cast_pos.mp hp)
      simp only [minorArcBlockTerm, ite_eq_right hz', ite_eq_right hzR, C, Y, Z,
        minorArcC, minorArcCReal]
      push_cast
      norm_num
  rw [hcast]
  change (if 0 < z then min c (minorArcBReal epsᵤ y z j) else c) ≤ _
  by_cases hZ : 0 < Z
  · rw [ite_eq_left hZ, ite_eq_left (hZ.trans_le hz)]
    apply min_le_min hc
    exact minorArc_b_upper j hj hy hYd heᵤ heᵤ' hZ hz hjsq'
  · rw [ite_eq_right hZ]
    split
    · exact (min_le_left _ _).trans hc
    · exact hc


def minorArcQFinite (epsₗ epsᵤ yplus : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range 20,
    (2 * (19 / 20 : ℝ) ^ (i + 1) / ((i + 1 : ℕ) : ℝ)) *
      minorArcExactTerm epsₗ epsᵤ yplus (i + 1) k

def minorArcQSmall (epsᵤ : ℝ) : ℝ :=
  let y₀ := Real.pi / 2560
  ∑ i ∈ Finset.range 20,
    let j : ℕ := i + 1
    (2 * (19 / 20 : ℝ) ^ j / (j : ℝ)) *
      ((2 / j + j * y₀ ^ 2 / 6) / (1 + (0.998 * 80 * y₀ / Real.sinh (10 * y₀)) ^ 2) +
        epsᵤ ^ j / (0.998 * 8 * j))

def minorArcFixedReal (epsₗ yplus : ℝ) : ℝ :=
  0.2 + yplus ^ 2 / 48 - 0.1 * epsₗ +
    4 * minorArcTailReal 2 + 2 * yplus * minorArcTailReal 1

private theorem minorArc_fixed_bound (row : MinorArcData) {epsₗ yplus : ℝ}
    (hY : 0 ≤ yplus) (hY' : yplus ≤ minorArcYmax row)
    (heₗ' : (row.epsLower : ℝ) ≤ epsₗ) :
    minorArcFixedReal epsₗ yplus ≤ (minorArcFixed row : ℝ) := by
  unfold minorArcFixedReal minorArcFixed
  push_cast
  have hsq : yplus ^ 2 ≤ (minorArcYmax row : ℝ) ^ 2 := pow_le_pow_left₀ hY hY' 2
  have htn : 0 ≤ minorArcTailReal 1 := tsum_nonneg (fun _ => by positivity)
  have h₁ := mul_le_mul hY' minorArc_tail_one.le htn (hY.trans hY')
  linarith [minorArc_tail_two.le]

private theorem minorArc_grid_sum_bound (row : MinorArcData) {k l u : ℕ} (hk : 5 ≤ k)
    (hlk : l ≤ k) (hku : k + 1 ≤ u)
    {epsₗ epsᵤ yplus : ℝ} (hY : 0 < yplus) (hY' : yplus ≤ minorArcYmax row)
    (heₗ : 0 ≤ row.epsLower) (heₗ' : (row.epsLower : ℝ) ≤ epsₗ)
    (heᵤ : 0 ≤ epsᵤ) (heᵤ' : epsᵤ ≤ (row.epsUpper : ℝ)) :
    minorArcQFinite epsₗ epsᵤ yplus k ≤ (minorArcBlockSum row l u : ℝ) := by
  unfold minorArcBlockSum minorArcQFinite
  rw [Rat.cast_list_sum, List.map_map, Finset.sum_list_map_count]
  simp only [List.toFinset_range]
  apply Finset.sum_le_sum
  intro i hi
  have hcnt : (List.range 20).count i = 1 :=
    List.count_eq_one_of_mem List.nodup_range (by simpa using hi)
  simp only [hcnt, one_nsmul, Function.comp_apply, minorArcWeight]
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact minorArc_block_term_bound row (by omega) (by
    have := Finset.mem_range.mp hi
    omega) hk hlk hku hY hY' heₗ heₗ' heᵤ heᵤ'

private theorem minorArc_small_sum_bound (row : MinorArcData) {epsᵤ : ℝ}
    (heᵤ : 0 ≤ epsᵤ) (heᵤ' : epsᵤ ≤ (row.epsUpper : ℝ)) :
    minorArcQSmall epsᵤ ≤ (minorArcSmallSum row : ℝ) := by
  let Y₀ : ℝ := (3.141593 : ℝ) / 2560
  let y₀ : ℝ := Real.pi / 2560
  have hello : 0 < y₀ := by dsimp [y₀]; positivity
  have hh₀ : y₀ ≤ Y₀ := div_le_div_of_nonneg_right Real.pi_lt_d6.le (by norm_num)
  have hYY : (10 * Y₀) ^ 2 < 6 := by norm_num [Y₀]
  have hyy : (10 * y₀) ^ 2 < 6 :=
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hh₀ (by norm_num)) 2).trans_lt hYY
  have hh := minorArc_sinh_upper (show 0 ≤ 10 * y₀ by positivity) hyy
  have hs : 0 < Real.sinh (10 * y₀) := minorArc_sinh_pos (by positivity)
  have hy' : 0 < 1 - (10 * y₀) ^ 2 / 6 := by linarith
  have hYY' : 0 < 1 - (10 * Y₀) ^ 2 / 6 := by linarith
  have hw :
      0.998 * 8 * (1 - (10 * Y₀) ^ 2 / 6) ≤ 0.998 * 80 * y₀ / Real.sinh (10 * y₀) := calc
    _ ≤ 0.998 * 8 * (1 - (10 * y₀) ^ 2 / 6) := by gcongr
    _ = 0.998 * 80 * y₀ / (10 * y₀ / (1 - (10 * y₀) ^ 2 / 6)) := by
      rw [div_div_eq_mul_div]
      field_simp [hello.ne']
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hs hh
  unfold minorArcQSmall minorArcSmallSum
  rw [Rat.cast_list_sum, List.map_map, Finset.sum_list_map_count]
  simp only [List.toFinset_range]
  apply Finset.sum_le_sum
  intro i hi
  have hcnt : (List.range 20).count i = 1 :=
    List.count_eq_one_of_mem List.nodup_range (by simpa using hi)
  simp only [hcnt, one_nsmul, Function.comp_apply, minorArcWeight]
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply div_le_div₀ (by positivity) (by gcongr) (by positivity)
    exact add_le_add_right (pow_le_pow_left₀ (by positivity) hw 2) _
  · gcongr

/-- A certificate for both q₀ and all q_k, with the common terms of q* included. -/
theorem minorArc_qstar_enveloped (r : Fin 18) {epsₗ epsᵤ yplus : ℝ}
    (hY : 0 < yplus) (hY' : yplus ≤ minorArcYmax (minorArcData r))
    (heₗ' : ((minorArcData r).epsLower : ℝ) ≤ epsₗ)
    (heᵤ : 0 ≤ epsᵤ) (heᵤ' : epsᵤ ≤ ((minorArcData r).epsUpper : ℝ)) :
    minorArcFixedReal epsₗ yplus + minorArcQSmall epsᵤ < (minorArcData r).target ∧
      ∀ k : Fin 1600, 5 ≤ k.val →
        minorArcFixedReal epsₗ yplus + minorArcQFinite epsₗ epsᵤ yplus k.val < (minorArcData r).target := by
  have heₗ : 0 ≤ (minorArcData r).epsLower := by fin_cases r <;> norm_num [minorArcData]
  have hf := minorArc_fixed_bound (minorArcData r) hY.le hY' heₗ'
  constructor
  · refine lt_of_le_of_lt (add_le_add hf (minorArc_small_sum_bound (minorArcData r) heᵤ heᵤ')) ?_
    exact_mod_cast minorArc_small_arithmetic r
  · intro k hk
    obtain ⟨b, hl, hu⟩ := minorArc_grid_cover k hk
    have hQ := minorArc_grid_sum_bound (minorArcData r) hk hl hu hY hY' heₗ heₗ' heᵤ heᵤ'
    refine lt_of_le_of_lt (add_le_add hf hQ) ?_
    exact_mod_cast minorArc_block_arithmetic r b

/-- The seventeen finite rows and the last unbounded row of the q* certificate
at the manuscript's reciprocal-radius and y_+ values. -/
theorem minorArc_qstar_upper (r : Fin 18) :
    let epsₗ := if r.val < 17 then Real.exp (-((minorArcData r).right : ℝ)) else 0
    let epsᵤ := Real.exp (-((minorArcData r).left : ℝ))
    let yplus := (minorArcYmax (minorArcData r) : ℝ)
    minorArcFixedReal epsₗ yplus + minorArcQSmall epsᵤ < (minorArcData r).target ∧
      ∀ k : Fin 1600, 5 ≤ k.val →
        minorArcFixedReal epsₗ yplus + minorArcQFinite epsₗ epsᵤ yplus k.val < (minorArcData r).target := by
  dsimp only
  have hY : (0 : ℚ) < minorArcYmax (minorArcData r) := by
    fin_cases r <;> norm_num [minorArcYmax, minorArcData]
  apply minorArc_qstar_enveloped r (by exact_mod_cast hY) le_rfl _ (by positivity) (minorArc_eps_upper r)
  split
  · exact minorArc_eps_lower r (by assumption)
  · have hr : r.val = 17 := by omega
    have heq : r = 17 := Fin.ext hr
    norm_num [heq, minorArcData]

end DurfeeCCS.Step07
