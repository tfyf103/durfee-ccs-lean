module

public import DurfeeCCS.Step09.MidPoissonProduct

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Continuity and logarithmic expansion of the Euler product on the right half-plane. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step09

open Complex Set Filter DurfeeCCS.Step06 DurfeeCCS.Step08
open scoped Topology

private def eulerPerturbation (j : ℕ) (ζ : ℂ) : ℂ := -exp (-((j : ℂ) + 1) * ζ)

private theorem norm_eulerPerturbation (j : ℕ) (ζ : ℂ) :
    ‖eulerPerturbation j ζ‖ = (Real.exp (-ζ.re)) ^ (j + 1) := by
  rw [eulerPerturbation, norm_neg, norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.add_re]
  ring

private theorem norm_eulerPerturbation_le {ζ : ℂ} {u : ℝ} (hu : 0 < u) (hζ : u ≤ ζ.re) (j : ℕ) :
    ‖eulerPerturbation j ζ‖ ≤ (Real.exp (-u))^(j+1) ∧ ‖eulerPerturbation j ζ‖ ≤ Real.exp (-u) := by
  have hq : 0 ≤ Real.exp (-u) := Real.exp_nonneg _
  have hq₁ : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [norm_eulerPerturbation]
  have ha := pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr (neg_le_neg hζ)) (j+1)
  refine ⟨ha, ha.trans ?_⟩
  conv_rhs => rw [← pow_one (Real.exp (-u))]
  exact pow_le_pow_of_le_one hq hq₁ (by omega)

private theorem norm_log_eulerPerturbation_le {ζ : ℂ} {u : ℝ} (hu : 0 < u) (hζ : u ≤ ζ.re) (j : ℕ) :
    ‖log (1 + eulerPerturbation j ζ)‖ ≤ (Real.exp (-u))^(j+1) / (1 - Real.exp (-u)) := by
  let b := ‖eulerPerturbation j ζ‖
  let q := Real.exp (-u)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  obtain ⟨hpow,hb⟩ := norm_eulerPerturbation_le hu hζ j
  have hb₀ : 0 ≤ b := norm_nonneg _
  have hb₁ : b < 1 := hb.trans_lt hq
  have hden : 0 < 1 - b := sub_pos.mpr hb₁
  apply (norm_log_one_add_le hb₁).trans ?_
  change b ^ 2 * (1 - b)⁻¹ / 2 + b ≤ q ^ (j + 1) / (1 - q)
  calc
    b ^ 2 * (1 - b)⁻¹ / 2 + b ≤ b / (1 - b) := by
      apply (le_div_iff₀ hden).2
      field_simp
      nlinarith [sq_nonneg b]
    _ ≤ q ^ (j + 1) / (1 - q) :=
      div_le_div₀ (by positivity) hpow (sub_pos.mpr hq) (sub_le_sub_left hb 1)

private theorem eulerLogMajorant_summable {u : ℝ} (hu : 0 < u) :
    Summable (fun j : ℕ => (Real.exp (-u))^(j+1) / (1 - Real.exp (-u))) := by
  have hs := summable_geometric_of_lt_one (Real.exp_nonneg (-u))
    (Real.exp_lt_one_iff.mpr (by linarith : -u < 0))
  simpa only [div_eq_mul_inv] using ((summable_nat_add_iff 1).mpr hs).mul_right _

/-- The series of principal logarithms on the convergence half-plane. -/
def eulerProductLog (ζ : ℂ) : ℂ :=
  ∑' j : ℕ, log (1 - exp (-((j : ℂ) + 1) * ζ))

theorem summable_norm_eulerProductLog_terms {ζ : ℂ} (hζ : 0 < ζ.re) :
    Summable (fun j : ℕ => ‖log (1 - exp (-((j : ℂ) + 1) * ζ))‖) :=
  (eulerLogMajorant_summable hζ).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_log_eulerPerturbation_le hζ le_rfl)

theorem norm_eulerProductLog_le {ζ : ℂ} (hζ : 0 < ζ.re) :
    ‖eulerProductLog ζ‖ ≤ Real.exp (-ζ.re) / (1 - Real.exp (-ζ.re)) ^ 2 := by
  let q := Real.exp (-ζ.re)
  have hq₀ : 0 ≤ q := Real.exp_nonneg _
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := summable_norm_eulerProductLog_terms hζ
  have h := (norm_tsum_le_tsum_norm hs).trans
    (hs.tsum_le_tsum (norm_log_eulerPerturbation_le hζ le_rfl) (eulerLogMajorant_summable hζ))
  refine h.trans_eq ?_
  change (∑' j : ℕ, q ^ (j + 1) / (1 - q)) = q / (1 - q) ^ 2
  have he (j : ℕ) : q ^ (j + 1) / (1 - q) = (q / (1 - q)) * q ^ j := by
    rw [pow_succ]
    ring
  simp_rw [he, tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq]
  field_simp [show 1 - q ≠ 0 by linarith]

theorem exp_eulerProductLog_eq {ζ : ℂ} (hζ : 0 < ζ.re) :
    exp (eulerProductLog ζ) = eulerProduct ζ := by
  have hlog : Summable (fun j : ℕ => log (1 + eulerPerturbation j ζ)) :=
    (summable_norm_eulerProductLog_terms hζ).of_norm
  have hn (j : ℕ) : 1 + eulerPerturbation j ζ ≠ 0 := by
    have hj := (norm_eulerPerturbation_le hζ le_rfl j).2.trans_lt
      (Real.exp_lt_one_iff.mpr (by linarith : -ζ.re < 0))
    intro he
    have hc := eq_neg_of_add_eq_zero_right he
    simp [hc] at hj
  change exp (∑' j : ℕ, log (1 + eulerPerturbation j ζ)) = _
  rw [cexp_tsum_eq_tprod hn hlog, eulerProduct]
  rfl

/-- On each closed half-plane with strictly positive real part, the
principal logarithms converge uniformly. -/
theorem continuousOn_eulerProductLog_half {u : ℝ} (hu : 0 < u) :
    ContinuousOn eulerProductLog {ζ : ℂ | u ≤ ζ.re} := by
  change ContinuousOn (fun ζ : ℂ => ∑' j : ℕ, log (1 + eulerPerturbation j ζ))
    {ζ : ℂ | u ≤ ζ.re}
  apply continuousOn_tsum (u := fun j : ℕ => (Real.exp (-u))^(j+1) / (1 - Real.exp (-u)))
  · intro j ζ hζ
    have hf : Continuous (fun z : ℂ => 1 + eulerPerturbation j z) := by unfold eulerPerturbation; fun_prop
    have hnorm := (norm_eulerPerturbation_le hu (show u ≤ ζ.re from hζ) j).2.trans_lt
      (Real.exp_lt_one_iff.mpr (by linarith : -u < 0))
    have hz : 1 + eulerPerturbation j ζ ∈ slitPlane := by
      rw [mem_slitPlane_iff, Complex.add_re, Complex.one_re]
      exact Or.inl (by linarith [(abs_le.mp (Complex.abs_re_le_norm (eulerPerturbation j ζ))).1])
    have hcont : ContinuousAt (fun z : ℂ => 1 + eulerPerturbation j z) ζ := hf.continuousAt
    exact (((continuousAt_clog hz).comp (f := fun z : ℂ => 1 + eulerPerturbation j z))
      hcont).continuousWithinAt
  · exact eulerLogMajorant_summable hu
  · exact fun j ζ hζ => norm_log_eulerPerturbation_le hu hζ j

theorem continuousOn_eulerProduct_right :
    ContinuousOn eulerProduct {ζ : ℂ | 0 < ζ.re} := by
  intro ζ hζ
  have hζ₀ : 0 < ζ.re := hζ
  let u := ζ.re / 2
  have hu : 0 < u := by dsimp only [u]; positivity
  have hx : u < ζ.re := by dsimp only [u]; linarith
  have hN : {z : ℂ | u ≤ z.re} ∈ 𝓝 ζ :=
    mem_of_superset ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx)
      (fun _ h => le_of_lt h)
  have hC : ContinuousOn eulerProduct {z : ℂ | u ≤ z.re} :=
    (Complex.continuous_exp.comp_continuousOn (continuousOn_eulerProductLog_half hu)).congr
      (fun z hz => (exp_eulerProductLog_eq (hu.trans_le hz)).symm)
  exact ((hC ζ hx.le).continuousAt hN).continuousWithinAt

theorem continuous_eulerProduct_vertical {u : ℝ} (hu : 0 < u) :
    Continuous (fun v : ℝ => eulerProduct (verticalPoint u v)) := by
  have hv : Continuous (verticalPoint u) := by unfold verticalPoint; fun_prop
  exact continuousOn_univ.mp (continuousOn_eulerProduct_right.comp hv.continuousOn
    (fun v _ => by simpa only [mem_ofPred_eq, verticalPoint_re] using hu))

end DurfeeCCS.Step09
