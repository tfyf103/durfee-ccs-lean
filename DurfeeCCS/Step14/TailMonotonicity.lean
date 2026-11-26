module

public import DurfeeCCS.Step07.ThetaBoundsTail
import all DurfeeCCS.Step07.MidSaddleTail
import all DurfeeCCS.Step07.ThetaBoundsTail

/-! Strict decay of the two growing-amplitude terms in the page 31 tail estimate. -/

public noncomputable section

namespace DurfeeCCS.Step14

open Real Set DurfeeCCS.Step07

private theorem strictAntiOn_tailProduct (φ : ℝ → ℝ)
    (hφ : ∀ x ∈ Ici 80, ∃ d, HasDerivAt φ d x ∧ 1 ≤ x * d) :
    StrictAntiOn (fun x : ℝ => √(arcGrowth x * x) * exp (-φ x)) (Ici 80) := by
  have hderiv (x : ℝ) (hx : x ∈ Ici 80) :
      ∃ d < 0, HasDerivAt (fun t : ℝ => √(arcGrowth t * t) * exp (-φ t)) d x := by
    have hx₀ : 0 < x := (by norm_num : (0 : ℝ) < 80).trans_le hx
    let A := arcGrowth x
    let A' := (log x + 1) / (x * A)
    let w := √(A * x)
    have hA : 0 < A := arcGrowth_pos x
    have hw : 0 < w := sqrt_pos_of_pos (mul_pos hA hx₀)
    have hw₂ : w ^ 2 = A * x := sq_sqrt (mul_nonneg hA.le hx₀.le)
    have hAderiv : HasDerivAt arcGrowth A' x := hasDerivAt_arcGrowth hx₀
    have hroot : HasDerivAt (fun t : ℝ => √(arcGrowth t * t))
        ((A' * x + A) / (2 * w)) x := by
      have hp : HasDerivAt (fun t : ℝ => arcGrowth t * t) (A' * x + A) x := by
        simpa only [id, mul_one] using hAderiv.fun_mul (hasDerivAt_id x)
      have hr := (hasDerivAt_sqrt (mul_pos hA hx₀).ne').comp
        (h := fun t : ℝ => arcGrowth t * t) x hp
      change HasDerivAt (fun t : ℝ => √(arcGrowth t * t))
        (1 / (2 * w) * (A' * x + A)) x at hr
      simpa only [one_div, inv_mul_eq_div] using hr
    obtain ⟨d, hd, hr⟩ := hφ x hx
    have hlog : x * A' / A < 0.168 := by
      have h := (arcGrowth_relative_lt (show 80 ≤ x from hx)).2
      change x * deriv arcGrowth x / A < 0.168 at h
      rwa [hAderiv.deriv] at h
    have hlog' := (div_lt_iff₀ hA).mp hlog
    have hrA := mul_le_mul_of_nonneg_left hr hA.le
    have hnum : A' * x + A < (w * d) * (2 * w) := by
      calc
        _ < 2 * (A * (x * d)) := by nlinarith only [hlog', hrA, hA]
        _ = 2 * w ^ 2 * d := by rw [hw₂]; ring
        _ = _ := by ring
    have hdec : (A' * x + A) / (2 * w) < w * d :=
      (div_lt_iff₀ (by positivity)).mpr hnum
    refine ⟨(A' * x + A) / (2 * w) * exp (-φ x) + w * (exp (-φ x) * -d), ?_,
      hroot.mul hd.neg.exp⟩
    rw [show (A' * x + A) / (2 * w) * exp (-φ x) + w * (exp (-φ x) * -d) =
      exp (-φ x) * ((A' * x + A) / (2 * w) - w * d) from by ring]
    exact mul_neg_of_pos_of_neg (exp_pos _) (sub_neg.mpr hdec)
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    obtain ⟨d, _, hd⟩ := hderiv x hx
    exact hd.continuousAt.continuousWithinAt
  · intro x hx
    obtain ⟨d, hn, hd⟩ := hderiv x (interior_subset hx)
    rwa [hd.deriv]

/-- Both summands in the last term of the page 31 bound on (E'_J) strictly
decrease in (x = \sqrt n) for (x \geq 80). -/
theorem theta38_tail_summands_strictAntiOn :
    StrictAntiOn (fun x : ℝ => √(theta38Growth x * x) *
      exp (-(1.48481 : ℝ) ^ 2 * x / theta38Growth x)) (Ici 80) ∧
    StrictAntiOn (fun x : ℝ => √(theta38Growth x * x) *
      exp (-theta38TailD * (x / 80))) (Ici 80) := by
  constructor
  · have h := strictAntiOn_tailProduct (fun x => (1.48481 : ℝ) ^ 2 * (x / arcGrowth x)) (by
      intro x hx
      have hx' : 80 ≤ x := hx
      have hx₀ : 0 < x := (by norm_num : (0 : ℝ) < 80).trans_le hx'
      refine ⟨_, (hasDerivAt_arcGrowthRatio hx₀).const_mul _, ?_⟩
      calc
        (1 : ℝ) ≤ (1.48481 : ℝ) ^ 2 * 13.8 * (1 - 0.168) := by norm_num
        _ ≤ (1.48481 : ℝ) ^ 2 * (x / arcGrowth x) *
            (1 - (log x + 1) / arcGrowth x ^ 2) := by
          refine mul_le_mul ?_ (sub_le_sub_left (arcGrowth_relative_le hx') _) (by norm_num)
            (mul_nonneg (sq_nonneg _) (div_nonneg hx₀.le (arcGrowth_pos x).le))
          exact mul_le_mul_of_nonneg_left (arcGrowthRatio_lower hx') (by positivity)
        _ = _ := by ring)
    simpa only [arcGrowth, theta38Growth, ← mul_div_assoc, neg_div, neg_mul] using h
  · have h := strictAntiOn_tailProduct (fun x => theta38TailD * (x / 80)) (by
      intro x hx
      have hx' : 80 ≤ x := hx
      refine ⟨_, ((hasDerivAt_id x).div_const 80).const_mul _, ?_⟩
      have hD : 2 ≤ theta38TailD := theta38TailD_ge
      calc
        (1 : ℝ) ≤ 2 * (80 / 80) := by norm_num
        _ ≤ theta38TailD * (x / 80) := by gcongr
        _ = _ := by ring)
    simpa only [arcGrowth, theta38Growth, neg_mul] using h

end DurfeeCCS.Step14
