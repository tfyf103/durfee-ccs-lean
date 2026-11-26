module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.LinearCombination

/-! Decreasing polynomial-exponential majorants. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open Real Set

/-- A polynomial times an exponential decays after its derivative changes sign. -/
theorem power_mul_exp_antitoneOn {x₀ a b : ℝ} (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hx₀ : 0 ≤ x₀) (ha : 0 ≤ a)
    (h : (n : ℝ) ≤ a * k * x₀ ^ k) :
    AntitoneOn (fun x : ℝ => x ^ n * exp (-a * x ^ k + b)) (Ici x₀) := by
  let f := fun x : ℝ => x ^ n * exp (-a * x ^ k + b)
  have hf (x : ℝ) : HasDerivAt f
      (x ^ (n - 1) * exp (-a * x ^ k + b) * ((n : ℝ) - a * k * x ^ k)) x := by
    have he := (((hasDerivAt_pow k x).const_mul (-a)).add_const b).exp
    have hd := (hasDerivAt_pow n x).mul he
    convert hd using 1
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hpn : x ^ n = x ^ (n - 1) * x := by
      calc
        x ^ n = x ^ ((n - 1) + 1) := by rw [hn']
        _ = _ := pow_succ x (n - 1)
    have hpk : x ^ k = x ^ (k - 1) * x := by
      calc
        x ^ k = x ^ ((k - 1) + 1) := by rw [hk']
        _ = _ := pow_succ x (k - 1)
    linear_combination
      a * k * x ^ (k - 1) * exp (-a * x ^ k + b) * hpn -
        a * k * x ^ (n - 1) * exp (-a * x ^ k + b) * hpk
  apply antitoneOn_of_deriv_nonpos (convex_Ici x₀)
  · exact (fun x hx => (hf x).continuousAt.continuousWithinAt)
  · exact (fun x hx => (hf x).differentiableAt.differentiableWithinAt)
  · intro x hx
    rw [(hf x).deriv]
    have hx' : x₀ ≤ x := interior_subset hx
    have hpow : x₀ ^ k ≤ x ^ k := pow_le_pow_left₀ hx₀ hx' _
    have hbound := h.trans (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ a * k))
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg (hx₀.trans hx') _) (exp_pos _).le) (sub_nonpos.mpr hbound)

end DurfeeCCS.Step07
