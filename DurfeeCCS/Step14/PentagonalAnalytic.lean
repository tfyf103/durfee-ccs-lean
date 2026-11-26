module

public import DurfeeCCS.Step06.Theta
public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
import Mathlib.Tactic

/-! Euler's pentagonal identity, as a specialization of the Jacobi triple product. -/

@[expose] public section
namespace DurfeeCCS.Step14

open Complex Filter Finset Step06
open scoped Topology

private theorem prod_range_three {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    (∏ j ∈ range (3 * n), f j) =
      (∏ j ∈ range n, f (3 * j)) * (∏ j ∈ range n, f (3 * j + 1)) *
        (∏ j ∈ range n, f (3 * j + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = ((3 * n + 1) + 1) + 1 by omega]
    rw [prod_range_succ, prod_range_succ, prod_range_succ, ih]
    simp only [prod_range_succ]
    ac_rfl

private theorem tprod_three {f : ℕ → ℂ} (hf : Multipliable f)
    (h0 : Multipliable (fun j : ℕ => f (3 * j)))
    (h1 : Multipliable (fun j : ℕ => f (3 * j + 1)))
    (h2 : Multipliable (fun j : ℕ => f (3 * j + 2))) :
    (∏' j, f j) = (∏' j, f (3 * j)) * (∏' j, f (3 * j + 1)) *
      (∏' j, f (3 * j + 2)) := by
  have h := (h0.hasProd.tendsto_prod_nat.mul h1.hasProd.tendsto_prod_nat).mul h2.hasProd.tendsto_prod_nat
  have h3 : Tendsto (fun j : ℕ => 3 * j) atTop atTop :=
    tendsto_atTop_mono (fun j => by omega : ∀ j : ℕ, j ≤ 3 * j) tendsto_id
  exact tendsto_nhds_unique (hf.hasProd.tendsto_prod_nat.comp h3)
    (h.congr (fun n => (prod_range_three f n).symm))

private theorem theta_pentagonal_parameter_ne_zero (ζ : ℂ) :
    -exp (ζ / 2) ≠ 0 := neg_ne_zero.mpr (exp_ne_zero _)

private theorem theta_pentagonal_term (ζ : ℂ) (k : ℤ) :
    (-exp (ζ / 2)) ^ k * exp (-(3 * ζ) * (k : ℂ) ^ 2 / 2) =
      (-1 : ℂ) ^ k * exp (-(pentagonal k : ℂ) * ζ) := by
  have hExp := Complex.exp_int_mul (ζ / 2) k
  have hTwo := congrArg (fun a : ℤ => (a : ℂ)) (two_mul_natCast_pentagonal k)
  push_cast at hTwo
  rw [show -exp (ζ / 2) = -1 * exp (ζ / 2) from by ring, mul_zpow,
    ← hExp, mul_assoc, ← Complex.exp_add]
  congr 2
  linear_combination (ζ / 2) * hTwo

/-- Euler's pentagonal number theorem on the right half-plane. -/
theorem eulerProduct_eq_pentagonal_tsum {ζ : ℂ} (hζ : 0 < ζ.re) :
    eulerProduct ζ = ∑' k : ℤ, (-1 : ℂ) ^ k * exp (-(pentagonal k : ℂ) * ζ) := by
  have hζ' : 0 < ((3 : ℂ) * ζ).re := by simpa using mul_pos (by norm_num : (0 : ℝ) < 3) hζ
  have hprod := theta_triple_product hζ' (theta_pentagonal_parameter_ne_zero ζ)
  have hm (j : ℕ) : -exp (ζ / 2) * exp (-((j : ℂ) + 1 / 2) * (3 * ζ)) =
      -exp (-((3 * j + 1 : ℕ) : ℂ) * ζ) := by
    rw [neg_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hp (j : ℕ) : (-exp (ζ / 2))⁻¹ * exp (-((j : ℂ) + 1 / 2) * (3 * ζ)) =
      -exp (-((3 * j + 2 : ℕ) : ℂ) * ζ) := by
    rw [inv_neg, ← Complex.exp_neg, neg_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have he (j : ℕ) : exp (-((j : ℂ) + 1) * (3 * ζ)) =
      exp (-((3 * j + 3 : ℕ) : ℂ) * ζ) := by
    congr 1
    push_cast
    ring
  let f (j : ℕ) : ℂ := 1 - exp (-((j : ℂ) + 1) * ζ)
  have hf : Multipliable f := eulerProduct_multipliable hζ
  have hq : ‖exp (-ζ)‖ < 1 := by rw [Complex.norm_exp, Complex.neg_re, Real.exp_lt_one_iff]; linarith
  have hs : Summable (fun j : ℕ => ‖exp (-((j : ℂ) + 1) * ζ)‖) := by
    have ht := (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)
    refine ht.congr fun j => ?_
    rw [← norm_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hmod (a : ℕ) : Multipliable (fun j : ℕ => f (3 * j + a)) := by
    exact multipliable_one_sub_of_summable (hs.comp_injective (i := fun j : ℕ => 3 * j + a)
      (by intro x y h; change 3 * x + a = 3 * y + a at h; omega))
  have hmod0 : Multipliable (fun j : ℕ => f (3 * j)) := by simpa using hmod 0
  have heuler : eulerProduct (3 * ζ) = ∏' j, f (3 * j + 2) := by
    unfold eulerProduct
    apply tprod_congr
    intro j
    rw [he]
    have hidx : ((3 * j + 3 : ℕ) : ℂ) = (↑(3 * j + 2 : ℕ) : ℂ) + 1 := by
      exact_mod_cast (show 3 * j + 3 = (3 * j + 2) + 1 by omega)
    rw [hidx]
  have hpair : (∏' j : ℕ, ((1 + -exp (ζ / 2) * exp (-((j : ℂ) + 1 / 2) * (3 * ζ))) *
      (1 + (-exp (ζ / 2))⁻¹ * exp (-((j : ℂ) + 1 / 2) * (3 * ζ))))) =
      (∏' j, f (3 * j)) * (∏' j, f (3 * j + 1)) := by
    simp_rw [hm, hp, ← sub_eq_add_neg]
    have hh (j : ℕ) : (1 - exp (-((3 * j + 1 : ℕ) : ℂ) * ζ)) *
        (1 - exp (-((3 * j + 2 : ℕ) : ℂ) * ζ)) = f (3 * j) * f (3 * j + 1) := by
      have h1 : ((3 * j + 1 : ℕ) : ℂ) = (↑(3 * j : ℕ) : ℂ) + 1 := by push_cast; ring
      have h2 : ((3 * j + 2 : ℕ) : ℂ) = (↑(3 * j + 1 : ℕ) : ℂ) + 1 := by
        exact_mod_cast (show 3 * j + 2 = (3 * j + 1) + 1 by omega)
      exact congrArg₂ (fun a b : ℂ => (1 - exp (-a * ζ)) * (1 - exp (-b * ζ))) h1 h2
    simp_rw [hh]
    exact hmod0.tprod_mul (hmod 1)
  unfold thetaSeries at hprod
  simp_rw [theta_pentagonal_term] at hprod
  rw [heuler, hpair] at hprod
  exact (tprod_three hf hmod0 (hmod 1) (hmod 2)).trans (by rw [hprod, mul_comm])

end DurfeeCCS.Step14
