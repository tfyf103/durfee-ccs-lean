module

public import DurfeeCCS.Step06.RademacherGenerating
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Unit multipliers of the squared eta function at all reduced rational cusps. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step06

open Complex ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

private theorem continuous_eta_upperHalfPlane : Continuous (fun τ : ℍ => ModularForm.eta (τ : ℂ)) := by
  have hc : ContinuousOn ModularForm.eta upperHalfPlaneSet := fun z hz =>
    (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).continuousAt.continuousWithinAt
  exact hc.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.2)

private theorem eta_pow_twentyFour_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.eta (γ • τ : ℍ) ^ 24 = denom γ τ ^ 12 * ModularForm.eta τ ^ 24 := by
  have h := congrFun (SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant
    discriminant_T_invariant γ) τ
  rw [SL_slash_apply] at h
  change ModularForm.eta (γ • τ : ℍ) ^ 24 * denom γ τ ^ (-12 : ℤ) = ModularForm.eta τ ^ 24 at h
  rw [zpow_neg, ← div_eq_mul_inv] at h
  exact ((div_eq_iff (pow_ne_zero _ (denom_ne_zero γ τ))).mp h).trans (mul_comm _ _)

/-- The squared eta function transforms with weight one and a constant unit multiplier.
Taking the twelfth power reduces the assertion to modularity of the discriminant. -/
theorem eta_square_smul_exists_unit (γ : SL(2, ℤ)) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ τ : ℍ,
      ModularForm.eta (γ • τ : ℍ) ^ 2 = ε * (denom γ τ * ModularForm.eta τ ^ 2) := by
  let F (τ : ℍ) : ℂ := ModularForm.eta (γ • τ : ℍ) ^ 2 / (denom γ τ * ModularForm.eta τ ^ 2)
  have hd (τ : ℍ) : denom γ τ * ModularForm.eta τ ^ 2 ≠ 0 :=
    mul_ne_zero (denom_ne_zero γ τ) (pow_ne_zero _ (eta_ne_zero τ.2))
  have hF (τ : ℍ) : F τ ^ 12 = 1 := by
    dsimp only [F]
    rw [div_pow, mul_pow, ← pow_mul, ← pow_mul,
      show 2 * 12 = 24 by norm_num, eta_pow_twentyFour_smul,
      div_self (mul_ne_zero (pow_ne_zero _ (denom_ne_zero γ τ))
        (pow_ne_zero _ (eta_ne_zero τ.2)))]
  have hF_cont : Continuous F := by
    apply Continuous.div _ _ hd
    · have hg : Continuous (fun τ : ℍ => γ • τ) :=
        continuous_const_smul (γ : GL (Fin 2) ℝ)
      exact (continuous_eta_upperHalfPlane.comp hg).pow 2
    · apply Continuous.mul _ (continuous_eta_upperHalfPlane.pow 2)
      unfold denom
      fun_prop
  let R : Set ℂ := {w | w ^ 12 = 1}
  have hR : R.Finite := by
    let p : Polynomial ℂ := Polynomial.X ^ 12 - 1
    have hp : p ≠ 0 := by
      intro he
      have hc := congrArg (fun f : Polynomial ℂ => f.eval 0) he
      norm_num [p] at hc
    convert Polynomial.finite_setOfPred_isRoot hp using 1
    ext w
    simp [R, p, Polynomial.IsRoot, sub_eq_zero]
  let ε := F UpperHalfPlane.I
  have hε : ‖ε‖ = 1 := by
    have he := congrArg norm (hF UpperHalfPlane.I)
    rw [norm_pow, norm_one, ← one_pow 12 (M := ℝ)] at he
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by norm_num : (12 : ℕ) ≠ 0)).mp he
  refine ⟨ε, hε, fun τ => ?_⟩
  exact (div_eq_iff (hd τ)).mp
    (isPreconnected_univ.constant_of_mapsTo hR.isDiscrete hF_cont.continuousOn
      (fun x _ => hF x) (Set.mem_univ τ) (Set.mem_univ UpperHalfPlane.I))

private theorem twoColourGenerating_eta_q (τ : ℂ) :
    twoColourGenerating (exp (2 * (Real.pi : ℂ) * I * τ)) =
      exp ((Real.pi : ℂ) * I * τ / 6) * (ModularForm.eta τ)⁻¹ ^ 2 := by
  let ζ := -(2 * (Real.pi : ℂ) * I * τ)
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hτ : I * ζ / (2 * (Real.pi : ℂ)) = τ := by
    rw [div_eq_iff (mul_ne_zero (by norm_num) hπ)]
    dsimp [ζ]
    calc
      _ = -(2 * (Real.pi : ℂ) * I ^ 2 * τ) := by ring
      _ = τ * (2 * (Real.pi : ℂ)) := by rw [I_sq]; ring
  have hζ : -ζ / 12 = (Real.pi : ℂ) * I * τ / 6 := by dsimp [ζ]; ring
  have h := twoColourGenerating_exp_neg_eq_eta ζ
  rw [hτ, hζ] at h
  simpa only [ζ, neg_neg] using h

/-- At a reduced cusp, the inverse eta-square generating function has a unit phase
which is independent of the displacement (z). The numerator of the transformed cusp
is a negative modular inverse of the original numerator. -/
theorem twoColourGenerating_cusp_exists_unit {h : ℤ} {k : ℕ} (hk : 0 < k) (hhk : Int.gcd h k = 1) :
    ∃ (a : ℤ) (ε : ℂ), ‖ε‖ = 1 ∧ ∀ {z : ℂ}, 0 < z.re →
      twoColourGenerating
        (exp (2 * (Real.pi : ℂ) * I * ((h : ℂ) / k + I * z / (k : ℂ)^2))) =
      ε * (z / (k : ℂ)) * exp ((Real.pi : ℂ) / (6 * z) - (Real.pi : ℂ) * z / (6 * (k : ℂ)^2)) *
        twoColourGenerating (exp (2 * (Real.pi : ℂ) * I * ((a : ℂ) / k + I / z))) := by
  let a : ℤ := -Int.gcdA h k
  let b : ℤ := -Int.gcdB h k
  have hdet : a * (-(h : ℤ)) - b * (k : ℤ) = 1 := by
    have hh := Int.gcd_eq_gcd_ab h k
    rw [hhk, Nat.cast_one] at hh
    dsimp [a,b]
    linarith only [hh, show -Int.gcdA h k * -(h : ℤ) - -Int.gcdB h k * (k : ℤ) =
      (h : ℤ) * Int.gcdA h k + (k : ℤ) * Int.gcdB h k by ring]
  let γ : SL(2, ℤ) := ⟨!![a,b; (k : ℤ), -(h : ℤ)], by simpa [Matrix.det_fin_two_of] using hdet⟩
  obtain ⟨e, he, heη⟩ := eta_square_smul_exists_unit γ
  let ε := e * I * exp (((Real.pi / 6 * (((h : ℝ) - a) / k) : ℝ) : ℂ) * I)
  refine ⟨a, ε, ?_, ?_⟩
  · dsimp only [ε]
    rw [norm_mul, norm_mul, he, norm_I, norm_exp_ofReal_mul_I, one_mul, one_mul]
  · intro z hz
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have hz₀ : z ≠ 0 := by intro hh; simp [hh] at hz
    let τ₀ : ℂ := (h : ℂ) / k + I * z / (k : ℂ)^2
    have hτ : 0 < τ₀.im := by
      have h : τ₀ = ((h : ℝ) / (k : ℝ) : ℝ) + (I * z) / (((k : ℝ) ^ 2 : ℝ) : ℂ) := by
        simp [τ₀]
      rw [h, add_im, ofReal_im, zero_add]
      have he : ((I * z) / (((k : ℝ) ^ 2 : ℝ) : ℂ)).im = z.re / (k : ℝ)^2 := by
        rw [div_ofReal_im, I_mul_im]
      rw [he]
      positivity
    let τ : ℍ := ⟨τ₀,hτ⟩
    have hp : (k : ℂ) * τ₀ - h = I * z / (k : ℂ) := by
      dsimp [τ₀]
      field_simp
      ring
    have hden : denom γ τ = I * z / (k : ℂ) := by
      rw [ModularGroup.denom_apply]
      simpa [γ, τ, sub_eq_add_neg] using hp
    have hγ : ((γ • τ : ℍ) : ℂ) = (a : ℂ) / k + I / z := by
      rw [coe_specialLinearGroup_apply]
      have he : ((↑(algebraMap ℤ ℝ (γ 0 0)) : ℂ) * (τ : ℂ) +
          (↑(algebraMap ℤ ℝ (γ 0 1)) : ℂ)) = (a : ℂ) * τ₀ + b := by
        simp [γ, algebraMap_int_eq, τ]
      have hf : ((↑(algebraMap ℤ ℝ (γ 1 0)) : ℂ) * (τ : ℂ) +
          (↑(algebraMap ℤ ℝ (γ 1 1)) : ℂ)) = I * z / (k : ℂ) := by
        simpa [γ, algebraMap_int_eq, τ, sub_eq_add_neg] using hp
      rw [he, hf]
      have hC : (a : ℂ) * (-(h : ℂ)) - (b : ℂ) * (k : ℂ) = 1 := by exact_mod_cast hdet
      dsimp [τ₀]
      rw [div_eq_iff (div_ne_zero (mul_ne_zero I_ne_zero hz₀) hk₀)]
      field_simp [hk₀, hz₀, I_ne_zero]
      linear_combination -(k : ℂ) * hC - (k : ℂ) * Complex.I_sq
    have hη := heη τ
    rw [hden] at hη
    change ModularForm.eta ((γ • τ : ℍ) : ℂ) ^ 2 = _ at hη
    rw [hγ] at hη
    have hηInv : (ModularForm.eta τ₀)⁻¹ ^ 2 =
      e * (I * z / (k : ℂ)) * (ModularForm.eta ((a : ℂ) / k + I / z))⁻¹ ^ 2 := by
      rw [inv_pow, inv_pow]
      change _ = e * (I * z / (k : ℂ) * ModularForm.eta τ₀ ^ 2) at hη
      rw [hη, mul_assoc, mul_inv_rev, mul_inv_rev]
      field_simp [pow_ne_zero 2 (eta_ne_zero hτ), I_ne_zero,
        show e ≠ 0 by intro hh; simp [hh] at he]
    let δ : ℂ := ((Real.pi / 6 * (((h : ℝ) - a) / k) : ℝ) : ℂ) * I
    let B : ℂ := (Real.pi : ℂ) / (6 * z) - (Real.pi : ℂ) * z / (6 * (k : ℂ)^2)
    let C : ℂ := (Real.pi : ℂ) * I * ((a : ℂ) / k + I / z) / 6
    have hExp : exp δ * exp B * exp C = exp ((Real.pi : ℂ) * I * τ₀ / 6) := by
      rw [← exp_add, ← exp_add]
      congr 1
      dsimp [δ, B, C, τ₀]
      push_cast
      field_simp
      ring_nf
      simp only [I_sq]
      ring
    rw [twoColourGenerating_eta_q, twoColourGenerating_eta_q,
      show (h : ℂ) / k + I * z / (k : ℂ)^2 = τ₀ from rfl, hηInv]
    change exp ((Real.pi : ℂ) * I * τ₀ / 6) *
        (e * (I * z / (k : ℂ)) * (ModularForm.eta ((a : ℂ) / k + I / z))⁻¹ ^ 2) =
      e * I * exp δ * (z / (k : ℂ)) * exp B *
        (exp C * (ModularForm.eta ((a : ℂ) / k + I / z))⁻¹ ^ 2)
    rw [← hExp]
    ring

end DurfeeCCS.Step06
