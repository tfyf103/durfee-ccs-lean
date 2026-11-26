module

public import DurfeeCCS.Step09.MidMinorGeometric
public import DurfeeCCS.Step06.PairedProduct
public import DurfeeCCS.Step08.NearOriginLaplace
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A modulus estimate for the clipped factors in the proof of (62). -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex DurfeeCCS.Step06 DurfeeCCS.Step08
open scoped ComplexConjugate BigOperators

def midMinorAlpha : ℝ := 19 / 20

def midFactorLogRadius (u t : ℝ) (m : ℕ) : ℝ := t - ((m : ℝ)+1/2)*u

def midFactorAngle (v θ : ℝ) (m : ℕ) : ℝ :=
  Real.pi/2 - ((m : ℝ)+1/2)*v + θ

def midClippedTerm (u t v θ : ℝ) (m : ℕ) : ℂ :=
  ((midMinorAlpha * midMinorWeight 1 u t m : ℝ) : ℂ) * midMinorPhase (midFactorAngle v θ m)

theorem norm_midClippedTerm (u t v θ : ℝ) (m : ℕ) :
    ‖midClippedTerm u t v θ m‖ = midMinorAlpha * midMinorWeight 1 u t m := by
  rw [midClippedTerm,norm_mul,norm_midMinorPhase,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact abs_of_nonneg (mul_nonneg (by norm_num [midMinorAlpha]) (Real.exp_nonneg _))

theorem norm_midClippedTerm_le (u t v θ : ℝ) (m : ℕ) :
    ‖midClippedTerm u t v θ m‖ ≤ midMinorAlpha := by
  rw [norm_midClippedTerm]
  exact mul_le_of_le_one_right (by norm_num [midMinorAlpha])
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) 1)) (abs_nonneg _)))

private theorem midMinorPhase_re (b : ℝ) : (midMinorPhase b).re = Real.cos b := by
  rw [midMinorPhase,Complex.exp_re]
  simp [Complex.mul_re,Complex.mul_im]

private theorem norm_sq_one_add_phase (x b : ℝ) :
    ‖1 + (x : ℂ)*midMinorPhase b‖^2 = 1+x^2+2*x*Real.cos b := by
  let z := midMinorPhase b
  have hn : z.re^2 + z.im^2 = 1 := by
    rw [pow_two, pow_two, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, show z = midMinorPhase b from rfl,
      norm_midMinorPhase]
    norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,zero_add]
  rw [← midMinorPhase_re]
  change (1+x*z.re)*(1+x*z.re)+(x*z.im)*(x*z.im)=_
  nlinarith only [congrArg (fun q : ℝ => x^2*q) hn]

private theorem norm_factor_clip {α x : ℝ} (ha : 0 ≤ α) (ha' : α ≤ 1) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (b : ℝ) :
    ‖1 + (x : ℂ)*midMinorPhase b‖ ≤
      Real.exp ((1-α)*x) * ‖1 + ((α*x : ℝ) : ℂ)*midMinorPhase b‖ := by
  let y := α*x
  have hxy : y ≤ x := mul_le_of_le_one_left hx ha'
  have hy : 0 ≤ y := mul_nonneg ha hx
  have hxy' : x*y ≤ 1 := (mul_le_mul_of_nonneg_left hxy hx).trans
    (by have h := pow_le_pow_left₀ hx hx' 2; simpa [pow_two] using h)
  have H : ‖1+(x:ℂ)*midMinorPhase b‖*(1+y) ≤
      (1+x)*‖1+(y:ℂ)*midMinorPhase b‖ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,norm_sq_one_add_phase,norm_sq_one_add_phase]
    have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hxy'))
      (sub_nonneg.mpr (Real.cos_le_one b))
    nlinarith only [h]
  have hx1 : 0 < 1+y := by positivity
  have hratio : (1+x)/(1+y) ≤ Real.exp ((1-α)*x) := by
    calc
      _ = 1+(x-y)/(1+y) := by field_simp; ring
      _ ≤ 1+(x-y) := add_le_add_right (div_le_self (sub_nonneg.mpr hxy) (by linarith only [hy])) 1
      _ ≤ _ := by
        rw [show x-y = (1-α)*x by dsimp [y]; ring, add_comm 1]
        exact Real.add_one_le_exp _
  calc
    _ ≤ (1+x)/(1+y)*‖1+(y:ℂ)*midMinorPhase b‖ := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hx1).mpr H
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

private theorem norm_one_add_w_phase (s b : ℝ) :
    ‖1 + (Real.exp s : ℂ)*midMinorPhase b‖ =
      Real.exp (max s 0) * ‖1 + (Real.exp (-|s|) : ℂ)*midMinorPhase b‖ := by
  by_cases hs : s ≤ 0
  · rw [max_eq_right hs,abs_of_nonpos hs,neg_neg, Real.exp_zero,one_mul]
  · have hS := le_of_not_ge hs
    rw [max_eq_left hS, abs_of_nonneg hS]
    have hfac : 1 + (Real.exp s : ℂ)*midMinorPhase b =
        ((Real.exp s : ℂ)*midMinorPhase b) *
          (1 + (Real.exp (-s) : ℂ)*midMinorPhase (-b)) := by
      have h₁ : (Real.exp s : ℂ)*(Real.exp (-s) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,Real.exp_zero,Complex.ofReal_one]
      have h₂ : midMinorPhase b * midMinorPhase (-b) = 1 := by rw [← midMinorPhase_add,add_neg_cancel,midMinorPhase_zero]
      rw [mul_add,mul_one]
      have h₃ : (Real.exp s : ℂ)*midMinorPhase b*((Real.exp (-s) : ℂ)*midMinorPhase (-b)) =
          ((Real.exp s : ℂ)*(Real.exp (-s) : ℂ))*(midMinorPhase b*midMinorPhase (-b)) := by ring
      rw [h₃,h₁,h₂]
      ring
    have hconj : 1 + (Real.exp (-s) : ℂ)*midMinorPhase (-b) =
        conj (1+(Real.exp (-s) : ℂ)*midMinorPhase b) := by
      rw [map_add,map_one,map_mul,Complex.conj_ofReal,conj_midMinorPhase]
    rw [hfac,norm_mul,norm_mul,norm_midMinorPhase,mul_one,Complex.norm_real,Real.norm_eq_abs,
       abs_of_pos (Real.exp_pos _),hconj,Complex.norm_conj]

theorem pairedTerm_eq_midFactor {r : ℝ} (hr : 0 < r) (u v θ : ℝ) (m : ℕ) :
    pairedTerm r θ (verticalPoint u v) m =
      (Real.exp (midFactorLogRadius u (Real.log r) m) : ℂ)*midMinorPhase (midFactorAngle v θ m) := by
  have hi : midMinorPhase (Real.pi / 2) = Complex.I := by
    rw [midMinorPhase, Complex.exp_mul_I]
    simp
  let h : ℝ := (m : ℝ)+1/2
  have hR : (Real.exp (midFactorLogRadius u (Real.log r) m) : ℂ) =
      (r:ℂ)*cexp ((-h*u : ℝ):ℂ) := by
    unfold midFactorLogRadius
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hr,Complex.ofReal_mul,Complex.ofReal_exp]
    congr 2
    dsimp [h]
    push_cast
    ring
  have hθ : midMinorPhase (midFactorAngle v θ m) = I * midMinorPhase (-h*v + θ) := by
    have hEq : midFactorAngle v θ m = Real.pi/2 + (-h*v+θ) := by
      dsimp only [midFactorAngle,h]
      ring
    rw [hEq,midMinorPhase_add,hi]
  rw [hR,hθ,pairedTerm,midMinorPhase]
  have he : -((m:ℂ)+1/2)*verticalPoint u v + θ*I =
      ((-h*u:ℝ):ℂ) + ((-h*v+θ:ℝ):ℂ)*I := by
    unfold verticalPoint
    dsimp only [h]
    push_cast
    ring
  rw [he,Complex.exp_add]
  ring

theorem norm_pairedFactor_clipped {r : ℝ} (hr : 0 < r) (u v θ : ℝ) (m : ℕ) :
    ‖1 + pairedTerm r θ (verticalPoint u v) m‖ ≤
      Real.exp (max (midFactorLogRadius u (Real.log r) m) 0 +
        (1-midMinorAlpha)*midMinorWeight 1 u (Real.log r) m) *
        ‖1 + midClippedTerm u (Real.log r) v θ m‖ := by
  rw [pairedTerm_eq_midFactor hr,norm_one_add_w_phase,Real.exp_add, mul_assoc, midClippedTerm]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  have he : Real.exp (-|midFactorLogRadius u (Real.log r) m|) = midMinorWeight 1 u (Real.log r) m := by
    unfold midFactorLogRadius midMinorWeight
    rw [abs_sub_comm]
    norm_num
  rw [he]
  exact norm_factor_clip (α := midMinorAlpha) (by norm_num [midMinorAlpha]) (by norm_num [midMinorAlpha])
    (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) 1)) (abs_nonneg _))) _

private theorem midClipped_add_one_ne_zero (u t v θ : ℝ) (m : ℕ) :
    1 + midClippedTerm u t v θ m ≠ 0 := by
  intro h
  have h' := norm_midClippedTerm_le u t v θ m
  rw [eq_neg_of_add_eq_zero_right h,norm_neg,norm_one] at h'
  norm_num [midMinorAlpha] at h'

theorem summable_norm_log_midClippedTerm {u : ℝ} (hu : 0 < u) (t v θ : ℝ) :
    Summable (fun m : ℕ => ‖Complex.log (1 + midClippedTerm u t v θ m)‖) := by
  let α := midMinorAlpha
  have ha : α < 1 := by norm_num [α,midMinorAlpha]
  have ha₀ : 0 ≤ α := by norm_num [α,midMinorAlpha]
  have hSa := (summable_midMinorWeight (by decide : 0 < (1:ℕ)) hu t).mul_left (α/(1-α))
  apply hSa.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  let x := ‖midClippedTerm u t v θ m‖
  have hx : 0 ≤ x := norm_nonneg _
  have hα : x ≤ α := norm_midClippedTerm_le u t v θ m
  have hx' := hα.trans_lt ha
  have hx1 : 0 < 1-x := by linarith
  change ‖Complex.log (1 + midClippedTerm u t v θ m)‖ ≤ _
  refine (Complex.norm_log_one_add_le hx').trans ?_
  calc
    _ ≤ x / (1-x) := by
      change x^2 * (1-x)⁻¹ / 2 + x ≤ x/(1-x)
      apply (le_div_iff₀ hx1).mpr
      field_simp
      nlinarith [sq_nonneg x]
    _ ≤ x/(1-α) := div_le_div_of_nonneg_left hx (by linarith) (by linarith)
    _ = _ := by rw [show x = α*midMinorWeight 1 u t m from norm_midClippedTerm u t v θ m]; ring

theorem summable_midFactorLoss {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t) :
    Summable (fun m : ℕ => max (midFactorLogRadius u t m) 0) := by
  let K := ⌊t/u+1/2⌋₊
  apply summable_of_ne_finset_zero (s := Finset.range K)
  intro m hm
  have hk : K ≤ m := by simpa [Finset.mem_range,not_lt] using hm
  have hk' : (K : ℝ) ≤ m := by exact_mod_cast hk
  have hfloor : t/u+1/2 < (K:ℝ)+1 := Nat.lt_floor_add_one _
  rw [max_eq_right]
  unfold midFactorLogRadius
  have h : t/u ≤ (m:ℝ)+1/2 := by linarith only [hk',hfloor]
  linarith only [(div_le_iff₀ hu).mp h]

theorem midFactorLoss_sum {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t) :
    2*u*(∑' m : ℕ, max (midFactorLogRadius u t m) 0) ≤ t^2 := by
  let K := ⌊t/u+1/2⌋₊
  have hfloor : t/u+1/2 < (K:ℝ)+1 := Nat.lt_floor_add_one _
  have hfloor' : (K:ℝ) ≤ t/u+1/2 := Nat.floor_le (by positivity)
  have he : (∑' m : ℕ, max (midFactorLogRadius u t m) 0) =
      ∑ m ∈ Finset.range K, midFactorLogRadius u t m := by
    rw [tsum_eq_sum (s := Finset.range K) (fun m hm => ?_)]
    · refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm' : (m:ℝ)+1 ≤ K := by exact_mod_cast (Finset.mem_range.mp hm)
      have h : (m:ℝ)+1/2 ≤ t/u := by linarith only [hm',hfloor']
      unfold midFactorLogRadius
      rw [max_eq_left (by linarith only [(le_div_iff₀ hu).mp h])]
    · have hm' : (K:ℝ) ≤ m := by exact_mod_cast (show K ≤ m by simpa using hm)
      have h : t/u ≤ (m:ℝ)+1/2 := by linarith only [hfloor,hm']
      unfold midFactorLogRadius
      rw [max_eq_right (by linarith only [(div_le_iff₀ hu).mp h])]
  rw [he]
  simp only [midFactorLogRadius,Finset.sum_sub_distrib,← Finset.sum_mul,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hsum : (∑ m ∈ Finset.range K, (m : ℝ)) = (K:ℝ)*((K:ℝ)-1)/2 := by
    by_cases hz : K = 0
    · simp [hz]
    have h := Finset.sum_range_id_mul_two K
    have := congrArg (fun x : ℕ => (x:ℝ)) h
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hz)] at this
    linarith
  rw [hsum]
  nlinarith only [sq_nonneg (t-(K:ℝ)*u)]

/-- The first parts of (62), directly as a modulus bound, including zero factors. -/
theorem norm_pairedProduct_le_clippedLog {r u : ℝ} (hr : 1 ≤ r) (hu : 0 < u) (v θ : ℝ) :
    let t := Real.log r
    ‖pairedProduct r θ (verticalPoint u v)‖ ≤ Real.exp
      (2 * (∑' m : ℕ, max (midFactorLogRadius u t m) 0) +
        2*(1-midMinorAlpha)*(∑' m : ℕ, midMinorWeight 1 u t m) +
        ((∑' m : ℕ, (Complex.log (1+midClippedTerm u t v θ m) +
          Complex.log (1+midClippedTerm u t v (-θ) m))) : ℂ).re) := by
  let t := Real.log r
  let L (m : ℕ) := 2*max (midFactorLogRadius u t m) 0 +
    2*(1-midMinorAlpha)*midMinorWeight 1 u t m
  let W (m : ℕ) := 1 + midClippedTerm u t v θ m
  let Z (m : ℕ) := 1 + midClippedTerm u t v (-θ) m
  let B (m : ℕ) := Real.exp (L m) * ‖W m‖ * ‖Z m‖
  have hp : 0 < r := by linarith
  have ht : 0 ≤ t := Real.log_nonneg hr
  have hpL := summable_midFactorLoss hu ht
  have hpw := summable_midMinorWeight (by decide : 0 < (1:ℕ)) hu t
  have hLS := (hpL.mul_left 2).add (hpw.mul_left (2*(1-midMinorAlpha)))
  have hW : Summable (fun m => Complex.log (W m)) := (summable_norm_log_midClippedTerm hu t v θ).of_norm
  have hZ : Summable (fun m => Complex.log (Z m)) := (summable_norm_log_midClippedTerm hu t v (-θ)).of_norm
  have hB (m : ℕ) : 0 < B m := mul_pos (mul_pos (Real.exp_pos _)
    (norm_pos_iff.mpr (midClipped_add_one_ne_zero u t v θ m)))
    (norm_pos_iff.mpr (midClipped_add_one_ne_zero u t v (-θ) m))
  have hLog (m : ℕ) : Real.log (B m) = L m + (Complex.log (W m) + Complex.log (Z m)).re := by
    rw [show B m = Real.exp (L m) * ‖W m‖ * ‖Z m‖ from rfl,
      Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (norm_pos_iff.mpr
        (midClipped_add_one_ne_zero u t v θ m)).ne')
        (norm_pos_iff.mpr (midClipped_add_one_ne_zero u t v (-θ) m)).ne',
      Real.log_mul (Real.exp_ne_zero _) (norm_pos_iff.mpr
        (midClipped_add_one_ne_zero u t v θ m)).ne', Real.log_exp, Complex.add_re,
      Complex.log_re, Complex.log_re]
    ring
  have hBsum : Summable (fun m => Real.log (B m)) := by
    simp_rw [hLog]
    exact hLS.add (Complex.reCLM.summable (hW.add hZ))
  let P (m : ℕ) := (1 + pairedTerm r θ (verticalPoint u v) m) *
    (1 + pairedTerm r (-θ) (verticalPoint u v) m)
  have hP := multipliable_pairedProduct r θ (ζ := verticalPoint u v) ((verticalPoint_re u v).symm ▸ hu)
  have hb (m : ℕ) : ‖P m‖ ≤ B m := by
    have h := mul_le_mul (norm_pairedFactor_clipped hp u v θ m) (norm_pairedFactor_clipped hp u v (-θ) m)
      (norm_nonneg _) (by positivity)
    unfold P
    rw [norm_mul]
    refine h.trans_eq ?_
    have hL : L m = (max (midFactorLogRadius u t m) 0 + (1-midMinorAlpha)*midMinorWeight 1 u t m) +
        (max (midFactorLogRadius u t m) 0 + (1-midMinorAlpha)*midMinorWeight 1 u t m) := by
      dsimp only [L]
      ring
    have hExp : Real.exp (L m) =
        Real.exp (max (midFactorLogRadius u t m) 0 + (1-midMinorAlpha)*midMinorWeight 1 u t m) *
        Real.exp (max (midFactorLogRadius u t m) 0 + (1-midMinorAlpha)*midMinorWeight 1 u t m) := by
      rw [hL,Real.exp_add]
    change _ = Real.exp (L m) * ‖W m‖ * ‖Z m‖
    rw [hExp]
    dsimp only [t,W,Z]
    ring
  change ‖∏' m, P m‖ ≤ _
  have hEval := hP.hasProd.norm
  have hEvalB := Real.hasProd_of_hasSum_log hB hBsum.hasSum
  have hFin (s : Finset ℕ) : (∏ m ∈ s, ‖P m‖) ≤ ∏ m ∈ s, B m :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun m _ => hb m)
  refine (le_of_tendsto_of_tendsto' hEval hEvalB hFin).trans_eq ?_
  congr 1
  simp_rw [hLog]
  have hLSS : Summable L := hLS
  change (∑' m : ℕ, (L m + Complex.reCLM (Complex.log (W m) + Complex.log (Z m)))) = _
  rw [hLSS.tsum_add (Complex.reCLM.summable (hW.add hZ)), ← Complex.reCLM.map_tsum (hW.add hZ)]
  unfold L
  rw [Summable.tsum_add (hpL.mul_left 2) (hpw.mul_left (2*(1-midMinorAlpha))), tsum_mul_left, tsum_mul_left]
  rfl

end DurfeeCCS.Step09
