module

public import DurfeeCCS.Step14.RademacherDedekind
public import DurfeeCCS.Step06.RademacherExactModular
public import DurfeeCCS.Step06.Branches
public import DurfeeCCS.Step06.RademacherExactPolar
import all DurfeeCCS.Step06.RademacherExactModular
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The explicit multiplier of the squared eta function by Euclidean descent. -/

public noncomputable section

namespace DurfeeCCS.Step14

open Complex ModularForm DurfeeCCS.Step06
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm BigOperators

private def phase (x : ℝ) : ℂ :=
  exp (((2 * Real.pi * x : ℝ) : ℂ) * I)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  rw [phase, phase, phase, ← exp_add]
  congr 1
  push_cast
  ring

private theorem phase_ne_zero (x : ℝ) : phase x ≠ 0 := exp_ne_zero _

private theorem phase_neg_quarter : phase (-1 / 4) = -I := by
  rw [phase, exp_mul_I]
  have he : (2 * Real.pi * (-1 / 4) : ℝ) = -(Real.pi / 2) := by ring
  rw [he, ofReal_neg, cos_neg, sin_neg, ← ofReal_cos, ← ofReal_sin]
  simp

private def etaMultiplier (γ : SL(2, ℤ)) : ℂ :=
  (eta_square_smul_exists_unit γ).choose

private theorem etaMultiplier_spec (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.eta ((γ • τ : ℍ) : ℂ) ^ 2 = etaMultiplier γ * (denom γ τ * ModularForm.eta τ ^ 2) :=
  (eta_square_smul_exists_unit γ).choose_spec.2 τ

private theorem etaMultiplier_eq (γ : SL(2, ℤ)) (τ : ℍ) {e : ℂ}
    (he : ModularForm.eta ((γ • τ : ℍ) : ℂ) ^ 2 = e * (denom γ τ * ModularForm.eta τ ^ 2)) :
    etaMultiplier γ = e := by
  apply mul_right_cancel₀ (mul_ne_zero (denom_ne_zero γ τ) (pow_ne_zero 2 (eta_ne_zero τ.2)))
  rw [← etaMultiplier_spec, he]

private theorem etaMultiplier_mul (γ δ : SL(2, ℤ)) :
    etaMultiplier (γ * δ) = etaMultiplier γ * etaMultiplier δ := by
  let τ : ℍ := UpperHalfPlane.I
  have hden : denom (γ * δ) τ = denom γ (δ • τ : ℍ) * denom δ τ := by
    rw [denom_cocycle_σ]
    simp [UpperHalfPlane.σ]
  apply etaMultiplier_eq _ τ
  rw [mul_smul, etaMultiplier_spec γ, etaMultiplier_spec δ]
  simp only [map_mul] at hden ⊢
  rw [hden]
  ring

private theorem eta_translation (τ : ℂ) (q : ℤ) :
    ModularForm.eta (τ + q) = phase ((q : ℝ) / 24) * ModularForm.eta τ := by
  have hx : exp (2 * (Real.pi : ℂ) * I * (τ + q)) = exp (2 * (Real.pi : ℂ) * I * τ) := by
    rw [mul_add, exp_add, mul_comm (2 * (Real.pi : ℂ) * I) (q : ℂ),
      exp_int_mul_two_pi_mul_I, mul_one]
  have hp : tprod (fun n : ℕ => 1 - eta_q n (τ + q)) =
      tprod (fun n : ℕ => 1 - eta_q n τ) := by
    apply tprod_congr
    intro n
    rw [eta_q_eq_pow, eta_q_eq_pow, hx]
  unfold ModularForm.eta
  rw [hp]
  unfold Function.Periodic.qParam phase
  rw [← mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

private theorem etaMultiplier_Tpow (q : ℤ) :
    etaMultiplier (ModularGroup.T ^ q) = phase ((q : ℝ) / 12) := by
  let τ : ℍ := UpperHalfPlane.I
  apply etaMultiplier_eq _ τ
  rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]
  simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    Int.cast_zero, zero_mul, zero_add, Int.cast_one, one_mul]
  rw [modular_T_zpow_smul, coe_vadd, Complex.ofReal_intCast, add_comm, eta_translation, mul_pow, pow_two (phase _),
    ← phase_add]
  congr 3
  ring

private theorem etaMultiplier_S :
    etaMultiplier ModularGroup.S = phase (-1 / 4) := by
  let τ : ℍ := UpperHalfPlane.I
  apply etaMultiplier_eq _ τ
  rw [ModularGroup.denom_S, modular_S_smul]
  have hη : ModularForm.eta (-(τ : ℂ)⁻¹) = (sqrt I)⁻¹ * (sqrt τ * ModularForm.eta τ) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv τ.2
  have hI : (sqrt I) ^ 2 = I := principalSqrt_sq _
  have hτ : (sqrt (τ : ℂ)) ^ 2 = (τ : ℂ) := principalSqrt_sq _
  change ModularForm.eta ((-(τ : ℂ))⁻¹) ^ 2 = _
  rw [inv_neg, hη, mul_pow, mul_pow, inv_pow, hI, hτ, phase_neg_quarter, inv_I]

private def dedekindMultiplierArgument (γ : SL(2, ℤ)) : ℝ :=
  ((γ 0 0 : ℤ) + (γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℤ)) -
    dedekindSum (γ 1 1) (γ 1 0).toNat - 1 / 4

private theorem matrix_det_entries (γ : SL(2, ℤ)) :
    γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe γ

private theorem matrix_coprime_entries (γ : SL(2, ℤ)) :
    (γ 1 1).natAbs.Coprime (γ 1 0).natAbs := by
  change Int.gcd (γ 1 1) (γ 1 0) = 1
  have hd' : (Int.gcd (γ 1 1) (γ 1 0) : ℤ) ∣ γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 :=
    dvd_sub (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) _)
  have hd : (Int.gcd (γ 1 1) (γ 1 0) : ℤ) ∣ 1 := by
    simpa only [matrix_det_entries] using hd'
  have hh := Int.eq_one_of_dvd_one (Int.natCast_nonneg _) hd
  exact_mod_cast hh

private theorem argument_mul_Tpow (γ : SL(2, ℤ)) (hγ : 0 < γ 1 0) (q : ℤ) :
    dedekindMultiplierArgument (γ * ModularGroup.T ^ q) =
      dedekindMultiplierArgument γ + (q : ℝ) / 12 := by
  have hc : (γ * ModularGroup.T ^ q) 1 0 = γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
      Fin.sum_univ_two]
  have ha : (γ * ModularGroup.T ^ q) 0 0 = γ 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
      Fin.sum_univ_two]
  have hd : (γ * ModularGroup.T ^ q) 1 1 = γ 1 1 + q * γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
      Fin.sum_univ_two]
    ring
  have hk : 0 < (γ 1 0).toNat := by omega
  have hcast : ((γ 1 0).toNat : ℤ) = γ 1 0 := Int.toNat_of_nonneg hγ.le
  have hs := dedekindSum_add_mul (γ 1 1) q hk
  rw [hcast] at hs
  simp only [dedekindMultiplierArgument, hc, ha, hd, hs]
  have hC : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast hγ.ne'
  push_cast
  field_simp
  ring

private theorem argument_mul_S (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (hd : 0 < γ 1 1) :
    dedekindMultiplierArgument (γ * ModularGroup.S) = dedekindMultiplierArgument γ - 1 / 4 := by
  have h00 : (γ * ModularGroup.S) 0 0 = γ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply,
      Fin.sum_univ_two]
  have h10 : (γ * ModularGroup.S) 1 0 = γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply,
      Fin.sum_univ_two]
  have h11 : (γ * ModularGroup.S) 1 1 = -(γ 1 0) := by
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply,
      Fin.sum_univ_two]
  let c := (γ 1 0).toNat
  let d := (γ 1 1).toNat
  have hc' : (c : ℤ) = γ 1 0 := Int.toNat_of_nonneg hc.le
  have hd' : (d : ℤ) = γ 1 1 := Int.toNat_of_nonneg hd.le
  have hg := matrix_coprime_entries γ
  rw [← hd', ← hc', Int.natAbs_natCast, Int.natAbs_natCast] at hg
  have hc₁ : 0 < c := by dsimp [c]; omega
  have hd₁ : 0 < d := by dsimp [d]; omega
  rw [dedekindMultiplierArgument, dedekindMultiplierArgument, h00, h10, h11]
  push_cast
  change ((γ 0 1 : ℤ) + (-(γ 1 0 : ℤ)) : ℝ) / (12 * (γ 1 1 : ℤ)) -
    dedekindSum (-(γ 1 0)) d - 1 / 4 =
    ((γ 0 0 : ℤ) + (γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℤ)) -
    dedekindSum (γ 1 1) c - 1 / 4 - 1 / 4
  rw [← hc', ← hd', dedekindSum_neg_nat hd₁ hg.symm]
  have hrec := dedekindSum_reciprocity hd₁ hc₁ hg
  have hdet := congrArg (fun x : ℤ => (x : ℝ)) (matrix_det_entries γ)
  rw [← hd', ← hc'] at hdet
  push_cast at hdet ⊢
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc₁.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd₁.ne'
  field_simp [hcR, hdR] at hrec ⊢
  linear_combination hrec - 4 * hdet

private theorem multiplier_of_normalized_zero (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hd : γ 1 1 = 0) :
    etaMultiplier γ = phase (dedekindMultiplierArgument γ) := by
  have hdet := matrix_det_entries γ
  rw [hd, mul_zero, zero_sub] at hdet
  have hcn : γ 1 0 ∣ 1 := ⟨-(γ 0 1), by linear_combination -hdet⟩
  have hc1 := Int.eq_one_of_dvd_one hc.le hcn
  have hb1 : γ 0 1 = -1 := by
    rw [hc1, mul_one] at hdet
    omega
  have hγ : γ = ModularGroup.T ^ (γ 0 0) * ModularGroup.S := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, ModularGroup.coe_S,
        hb1, hc1, hd]
  have harg : dedekindMultiplierArgument γ = (γ 0 0 : ℝ) / 12 - 1 / 4 := by
    simp [dedekindMultiplierArgument, hc1, hd]
  rw [harg]
  conv_lhs => rw [hγ]
  rw [etaMultiplier_mul, etaMultiplier_Tpow, etaMultiplier_S, ← phase_add, sub_eq_add_neg]
  congr 1
  ring

private theorem etaMultiplier_eq_dedekind (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = phase (dedekindMultiplierArgument γ) := by
  suffices h : ∀ k : ℕ, ∀ g : SL(2, ℤ), (g 1 0).toNat = k → 0 < g 1 0 →
      etaMultiplier g = phase (dedekindMultiplierArgument g) by
    exact h _ γ rfl hc
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro g hk hc
    let q := -(g 1 1 / g 1 0)
    let g' := g * ModularGroup.T ^ q
    have hc' : g' 1 0 = g 1 0 := by
      simp [g', Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
        Matrix.mul_apply, Fin.sum_univ_two]
    have hd' : g' 1 1 = g 1 1 % g 1 0 := by
      simp [g', q, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
        Matrix.mul_apply, Fin.sum_univ_two]
      have he := Int.emod_add_mul_ediv (g 1 1) (g 1 0)
      linarith only [he]
    have hcn : 0 < g' 1 0 := by rw [hc']; exact hc
    have hdn : 0 ≤ g' 1 1 := by rw [hd']; exact Int.emod_nonneg _ hc.ne'
    have hdl : g' 1 1 < g' 1 0 := by rw [hd', hc']; exact Int.emod_lt_of_pos _ hc
    have hg' : etaMultiplier g' = phase (dedekindMultiplierArgument g') := by
      by_cases hd0 : g' 1 1 = 0
      · exact multiplier_of_normalized_zero g' hcn hd0
      · have hdpos : 0 < g' 1 1 := lt_of_le_of_ne hdn (Ne.symm hd0)
        have hs : (g' * ModularGroup.S) 1 0 = g' 1 1 := by
          simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
            Matrix.mul_apply, Fin.sum_univ_two]
        have hlt : ((g' * ModularGroup.S) 1 0).toNat < k := by
          rw [hs, ← hk, ← hc']
          omega
        have hSpos : 0 < (g' * ModularGroup.S) 1 0 := by rw [hs]; exact hdpos
        have hS := ih _ hlt (g' * ModularGroup.S) rfl hSpos
        rw [etaMultiplier_mul, etaMultiplier_S, argument_mul_S g' hcn hdpos,
          sub_eq_add_neg, phase_add] at hS
        rw [neg_div] at hS
        exact mul_right_cancel₀ (phase_ne_zero _) hS
    dsimp only [g'] at hg'
    rw [etaMultiplier_mul, etaMultiplier_Tpow, argument_mul_Tpow g hc, phase_add] at hg'
    exact mul_right_cancel₀ (phase_ne_zero _) hg'

/-- The squared eta function has the explicit Dedekind multiplier when the lower-left
matrix entry is positive. -/
theorem eta_square_smul_dedekind (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    ModularForm.eta ((γ • τ : ℍ) : ℂ) ^ 2 =
      Complex.exp (((2 * Real.pi *
        (((γ 0 0 : ℤ) + (γ 1 1 : ℤ) : ℝ) / (12 * (γ 1 0 : ℤ)) -
          dedekindSum (γ 1 1) (γ 1 0).toNat - 1 / 4) : ℝ) : ℂ) * I) *
        (denom γ τ * ModularForm.eta τ ^ 2) := by
  rw [etaMultiplier_spec, etaMultiplier_eq_dedekind γ hc]
  rfl

/-- At a reduced rational cusp, the weight-one factor of the two-colour
partition product has exactly the Dedekind phase appearing in (14).
The inverse coordinate is in the right half-plane. -/
theorem twoColourGenerating_inverse_cusp_dedekind {h k : ℕ} (hk : 0 < k)
    (hg : h.Coprime k) :
    ∃ a : ℤ, ∀ {w : ℂ}, 0 < w.re →
      twoColourGenerating
          (exp (2 * (Real.pi : ℂ) * I * ((h : ℂ) / k + I / ((k : ℂ) ^ 2 * w)))) =
        exp (((2 * Real.pi * dedekindSum h k : ℝ) : ℂ) * I) *
          (1 / ((k : ℂ) * w)) *
          exp ((Real.pi : ℂ) * w / 6 - (Real.pi : ℂ) / (6 * (k : ℂ) ^ 2 * w)) *
          twoColourGenerating (exp (2 * (Real.pi : ℂ) * I * ((a : ℂ) / k + I * w))) := by
  let a : ℤ := -Int.gcdA (h : ℤ) (k : ℤ)
  let b : ℤ := -Int.gcdB (h : ℤ) (k : ℤ)
  have hd : a * (-(h : ℤ)) - b * (k : ℤ) = 1 := by
    have hg' : Int.gcd (h : ℤ) (k : ℤ) = 1 := by simpa using hg.gcd_eq_one
    have hh := Int.gcd_eq_gcd_ab (h : ℤ) (k : ℤ)
    rw [hg', Nat.cast_one] at hh
    dsimp [a, b]
    linear_combination -hh
  let γ : SL(2, ℤ) := ⟨!![a,b; (k : ℤ), -(h : ℤ)], by simpa [Matrix.det_fin_two_of] using hd⟩
  refine ⟨a, ?_⟩
  intro w hw
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hw₀ : w ≠ 0 := fun he => by simp [he] at hw
  let τ₀ : ℂ := (h : ℂ) / k + I / ((k : ℂ) ^ 2 * w)
  let τ₁ : ℂ := (a : ℂ) / k + I * w
  have hτ : 0 < τ₀.im := by
    have hp : 0 < (w⁻¹).re := by
      rw [Complex.inv_re]
      exact div_pos hw (Complex.normSq_pos.mpr hw₀)
    have he : τ₀ =
        (((h : ℝ) / (k : ℝ) : ℝ) : ℂ) +
          (I * w⁻¹) / ((((k : ℝ) ^ 2 : ℝ)) : ℂ) := by
      dsimp only [τ₀]
      push_cast
      field_simp [hkC, hw₀]
    rw [he, add_im, ofReal_im, zero_add, div_ofReal_im, I_mul_im]
    positivity
  let τ : ℍ := ⟨τ₀, hτ⟩
  have hp : (k : ℂ) * τ₀ - h = I / ((k : ℂ) * w) := by
    dsimp only [τ₀]
    field_simp
    ring
  have hden : denom γ τ = I / ((k : ℂ) * w) := by
    rw [ModularGroup.denom_apply]
    simpa [γ, τ, sub_eq_add_neg] using hp
  have hγ : ((γ • τ : ℍ) : ℂ) = τ₁ := by
    rw [coe_specialLinearGroup_apply]
    have hn : ((↑(algebraMap ℤ ℝ (γ 0 0)) : ℂ) * (τ : ℂ) +
        (↑(algebraMap ℤ ℝ (γ 0 1)) : ℂ)) = (a : ℂ) * τ₀ + b := by
      simp [γ, algebraMap_int_eq, τ]
    have hD : ((↑(algebraMap ℤ ℝ (γ 1 0)) : ℂ) * (τ : ℂ) +
        (↑(algebraMap ℤ ℝ (γ 1 1)) : ℂ)) = I / ((k : ℂ) * w) := by
      simpa [γ, algebraMap_int_eq, τ, sub_eq_add_neg] using hp
    rw [hn, hD]
    have hC : (a : ℂ) * (-(h : ℂ)) - (b : ℂ) * (k : ℂ) = 1 := by exact_mod_cast hd
    dsimp only [τ₀, τ₁]
    rw [div_eq_iff (div_ne_zero I_ne_zero (mul_ne_zero hkC hw₀))]
    field_simp [hkC, hw₀, I_ne_zero]
    linear_combination -(k : ℂ) * w * hC - (k : ℂ) * w * Complex.I_sq
  have hc : 0 < γ 1 0 := by simpa [γ] using (show (0 : ℤ) < (k : ℤ) by exact_mod_cast hk)
  have harg : dedekindMultiplierArgument γ =
      dedekindSum h k + (((a : ℝ) - h) / (12 * k)) + -1 / 4 := by
    simp [dedekindMultiplierArgument, γ, dedekindSum_neg_nat hk hg]
    ring
  let e := phase (dedekindMultiplierArgument γ)
  have hη : ModularForm.eta τ₁ ^ 2 = e * (I / ((k : ℂ) * w) * ModularForm.eta τ₀ ^ 2) := by
    rw [← hγ, ← hden, etaMultiplier_spec, etaMultiplier_eq_dedekind γ hc]
  have he : e ≠ 0 := phase_ne_zero _
  have hInv : (ModularForm.eta τ₀)⁻¹ ^ 2 =
      e * (I / ((k : ℂ) * w)) * (ModularForm.eta τ₁)⁻¹ ^ 2 := by
    rw [inv_pow, inv_pow, hη, mul_assoc, mul_inv_rev, mul_inv_rev]
    field_simp [pow_ne_zero 2 (eta_ne_zero hτ), I_ne_zero]
  have hphase : e * (I / ((k : ℂ) * w)) =
      phase (dedekindSum h k) * phase (((a : ℝ) - h) / (12 * k)) *
        (1 / ((k : ℂ) * w)) := by
    dsimp only [e]
    rw [harg, phase_add, phase_add, phase_neg_quarter]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hE : exp ((Real.pi : ℂ) * I * τ₀ / 6) * phase (((a : ℝ) - h) / (12 * k)) =
      exp ((Real.pi : ℂ) * w / 6 - (Real.pi : ℂ) / (6 * (k : ℂ) ^ 2 * w)) *
        exp ((Real.pi : ℂ) * I * τ₁ / 6) := by
    rw [phase, ← exp_add, ← exp_add]
    congr 1
    dsimp only [τ₀, τ₁]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [show (h : ℂ) / k + I / ((k : ℂ) ^ 2 * w) = τ₀ from rfl]
  rw [show (a : ℂ) / k + I * w = τ₁ from rfl]
  rw [twoColourGenerating_eta_q, twoColourGenerating_eta_q, hInv, hphase]
  change _ = phase (dedekindSum h k) * _ * _ * _
  linear_combination (phase (dedekindSum h k) * (1 / ((k : ℂ) * w)) *
    (ModularForm.eta τ₁)⁻¹ ^ 2) * hE

/-- The Fourier coefficient kernel after the inverse Ford-coordinate substitution.
The weight here corresponds to the orientation of the real inverse parameter. -/
theorem twoColourCoefficient_inverse_cusp_dedekind (n : ℕ) {h k : ℕ}
    (hk : 0 < k) (hg : h.Coprime k) :
    ∃ a : ℤ, ∀ {w : ℂ}, 0 < w.re →
      let τ := (h : ℂ) / k + I / ((k : ℂ) ^ 2 * w)
      (exp (-(2 * (Real.pi : ℂ) * I * (n : ℂ) * τ)) *
        twoColourGenerating (exp (2 * (Real.pi : ℂ) * I * τ))) /
          ((k : ℂ) ^ 2 * w ^ 2) =
        twoColourPhase n h k *
          (rademacherPolarKernel (Real.pi / 6) (2 * Real.pi * ((n : ℝ) - 1 / 12) / (k : ℝ) ^ 2)
            w / (k : ℂ) ^ 3) *
          twoColourGenerating (exp (2 * (Real.pi : ℂ) * I * ((a : ℂ) / k + I * w))) := by
  obtain ⟨a, hMod⟩ := twoColourGenerating_inverse_cusp_dedekind hk hg
  refine ⟨a, ?_⟩
  intro w hw
  dsimp only
  rw [hMod hw]
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hw₀ : w ≠ 0 := fun he => by simp [he] at hw
  unfold twoColourPhase rademacherPolarKernel
  have hArg : -(2 * (Real.pi : ℂ) * I * (n : ℂ) *
      ((h : ℂ) / k + I / ((k : ℂ) ^ 2 * w))) +
      ((↑(2 * Real.pi * dedekindSum h k : ℝ) : ℂ) * I) +
      ((Real.pi : ℂ) * w / 6 - (Real.pi : ℂ) / (6 * (k : ℂ) ^ 2 * w)) =
      (↑(2 * Real.pi * (dedekindSum h k - (n : ℝ) * h / k) : ℝ) : ℂ) * I +
      ((↑(Real.pi / 6 : ℝ) : ℂ) * w +
        (↑(2 * Real.pi * ((n : ℝ) - 1 / 12) / (k : ℝ) ^ 2 : ℝ) : ℂ) / w) := by
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hE := congrArg exp hArg
  rw [exp_add, exp_add, exp_add] at hE
  set G := twoColourGenerating (exp (2 * (Real.pi : ℂ) * I * ((a : ℂ) / k + I * w)))
  calc
    _ = (exp (-(2 * (Real.pi : ℂ) * I * (n : ℂ) *
          ((h : ℂ) / k + I / ((k : ℂ) ^ 2 * w)))) *
          exp ((↑(2 * Real.pi * dedekindSum h k : ℝ) : ℂ) * I) *
          exp ((Real.pi : ℂ) * w / 6 - (Real.pi : ℂ) / (6 * (k : ℂ) ^ 2 * w))) * G /
          ((k : ℂ) ^ 3 * w ^ 3) := by
      field_simp [hk₀, hw₀]
    _ = _ := by
      rw [hE]
      field_simp [hk₀, hw₀]

end DurfeeCCS.Step14
