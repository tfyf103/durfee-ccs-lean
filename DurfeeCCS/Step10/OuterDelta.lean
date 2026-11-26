module

public import DurfeeCCS.Step10.OuterFarData
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Set

def outerA : ℝ := 4 * π ^ 2 / 3

def outerStart (n : ℕ) : ℝ := log ((n : ℝ) - 1 / 12)

/-- The real phase comparison whose inverse gives the far sample points. -/
def outerDelta (y h : ℝ) : ℝ := y * h / sqrt (h ^ 2 + outerA)

theorem outerA_pos : 0 < outerA := by
  unfold outerA
  positivity

theorem outerBase_pos (h : ℝ) : 0 < h ^ 2 + outerA :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) outerA_pos

theorem eighty_lt_outerY {n : ℕ} (hn : 6401 ≤ n) : 80 < outerY n := by
  have hn' : (6401 : ℝ) ≤ n := by exact_mod_cast hn
  apply (lt_sqrt (by norm_num)).2
  linarith

theorem outerStart_eq {n : ℕ} (hn : 1 ≤ n) : outerStart n = 2 * log (outerY n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold outerStart outerY
  rw [log_sqrt (by linarith)]
  ring

theorem cast_lt_outerY {n d : ℕ} (hd : d < n.sqrt) : (d : ℝ) < outerY n := by
  have hlt : d ^ 2 < n := by
    have h := Nat.sqrt_le n
    nlinarith only [hd, h]
  have hlt' : (d : ℝ) ^ 2 + 1 ≤ n := by exact_mod_cast (by omega : d ^ 2 + 1 ≤ n)
  apply (lt_sqrt (Nat.cast_nonneg _)).2
  linarith

theorem outerY_lt_sqrtNat_succ {n : ℕ} (hn : 1 ≤ n) : outerY n < (n.sqrt : ℝ) + 1 := by
  have h := Nat.lt_succ_sqrt n
  have h' : (n : ℝ) < ((n.sqrt : ℝ) + 1) ^ 2 := by
    exact_mod_cast (by simpa [pow_two] using h : n < (n.sqrt + 1) ^ 2)
  apply (sqrt_lt' (by positivity)).2
  linarith

theorem hasDerivAt_outerDelta (y h : ℝ) :
    HasDerivAt (outerDelta y) (y * outerA / ((h ^ 2 + outerA) * sqrt (h ^ 2 + outerA))) h := by
  have hb := outerBase_pos h
  have hs := sqrt_pos.2 hb
  have hss := sq_sqrt hb.le
  have hq : HasDerivAt (fun x : ℝ => x ^ 2 + outerA) (2 * h) h := by
    simpa [id, mul_comm] using ((hasDerivAt_id h).pow 2).add_const outerA
  have hroot : HasDerivAt (fun x : ℝ => sqrt (x ^ 2 + outerA))
        ((1 / (2 * sqrt (h ^ 2 + outerA))) * (2 * h)) h :=
    (hasDerivAt_sqrt hb.ne').comp h hq
  convert (((hasDerivAt_id h).const_mul y).div hroot hs.ne') using 1
  · funext x
    rfl
  · generalize hr : sqrt (h ^ 2 + outerA) = R at hs hss ⊢
    calc
      y * outerA / ((h ^ 2 + outerA) * R) =
          y * (R ^ 2 - h ^ 2) / (R ^ 2 * R) := by
        rw [show R ^ 2 - h ^ 2 = outerA by linarith, hss]
      _ = _ := by simp only [id_eq]; field_simp

theorem strictMono_outerDelta {y : ℝ} (hy : 0 < y) : StrictMono (outerDelta y) := by
  apply strictMono_of_deriv_pos
  intro h
  rw [(hasDerivAt_outerDelta y h).deriv]
  exact div_pos (mul_pos hy outerA_pos) (mul_pos (outerBase_pos h) (sqrt_pos.2 (outerBase_pos h)))

theorem farSample_pos {n d : ℕ} (hd : 0 < d) (hdm : d < n.sqrt) :
    0 < farSample n d := by
  have h : 0 < (outerY n) ^ 2 - (d : ℝ) ^ 2 := by
    nlinarith [cast_lt_outerY hdm, Nat.cast_nonneg (α := ℝ) d, sqrt_nonneg ((n : ℝ) - 1 / 12)]
  unfold farSample farRadius
  positivity

theorem outerDelta_farSample {n d : ℕ} (hdm : d < n.sqrt) :
    outerDelta (outerY n) (farSample n d) = d := by
  let y := outerY n
  let h := farSample n d
  let v := sqrt 3 * farRadius n d
  have hy : 0 < y := lt_of_le_of_lt (Nat.cast_nonneg d) (cast_lt_outerY hdm)
  have hdiff : 0 < y ^ 2 - (d : ℝ) ^ 2 := by
    nlinarith [cast_lt_outerY hdm, Nat.cast_nonneg (α := ℝ) d]
  have hv : 0 < v := mul_pos (by positivity) (sqrt_pos.2 hdiff)
  have hv2 : v ^ 2 = 3 * (y ^ 2 - (d : ℝ) ^ 2) := by
    simp [v, farRadius, y, mul_pow, sq_sqrt hdiff.le]
  have hhv : h * v = 2 * π * d := by
    change 2 * π * (d : ℝ) / v * v = _
    exact div_mul_cancel₀ _ hv.ne'
  have hprod : sqrt (h ^ 2 + outerA) * v = 2 * π * y := by
    have h1 := (sq_sqrt (outerBase_pos h).le)
    have h2 := congrArg (fun u : ℝ => u ^ 2) hhv
    rw [mul_pow] at h2
    have h3 : outerA * v ^ 2 = 4 * π ^ 2 * (y ^ 2 - (d : ℝ) ^ 2) := by rw [hv2]; unfold outerA; ring
    have hs : (sqrt (h ^ 2 + outerA) * v) ^ 2 = (2 * π * y) ^ 2 := by
      rw [mul_pow, h1, add_mul, h3, h2]
      ring
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hs
  change y * h / sqrt (h ^ 2 + outerA) = (d : ℝ)
  apply (div_eq_iff (sqrt_pos.2 (outerBase_pos h)).ne').2
  apply mul_right_cancel₀ hv.ne'
  rw [mul_assoc, mul_assoc, hhv, hprod]
  ring

theorem strictMonoOn_farSample {n : ℕ} (hn : 6401 ≤ n) :
    StrictMonoOn (farSample n) (Iio n.sqrt) := by
  intro a ha b hb hab
  apply (strictMono_outerDelta (lt_trans (by norm_num) (eighty_lt_outerY hn))).lt_iff_lt.mp
  rw [outerDelta_farSample ha, outerDelta_farSample hb]
  exact_mod_cast hab

end DurfeeCCS.Step10
