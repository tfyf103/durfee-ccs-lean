module

public import DurfeeCCS.Step06.RademacherGenerating
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-! The full Euler product calculation preceding equation (66). -/

@[expose] public section
namespace DurfeeCCS.Step13

open Step06

private theorem zeta_two_positive_indices :
    HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := hasSum_zeta_two.summable.tsum_eq_zero_add
  rw [hasSum_zeta_two.tsum_eq] at h
  change Real.pi ^ 2 / 6 = 1 / ((0 : ℕ) : ℝ)^2 +
    ∑' k : ℕ, (1 : ℝ) / ((k + 1 : ℕ) : ℝ)^2 at h
  norm_num only [Nat.cast_zero, zero_pow, OfNat.ofNat_ne_zero, div_zero, zero_add] at h
  have hs : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) :=
    (hasSum_zeta_two.summable.comp_injective Nat.succ_injective).congr (fun k => by
      change (1 : ℝ) / ((Nat.succ k : ℕ) : ℝ)^2 = _
      rw [Nat.cast_succ])
  rw [h]
  simpa only [Nat.cast_add, Nat.cast_one] using hs.hasSum

private theorem hasSum_twoColour_geometric (u : ℝ) (hu : 0 < u) (k : ℕ) :
    HasSum (fun j : ℕ => (Real.exp (-u) ^ (j + 1)) ^ (k + 1) / ((k : ℝ) + 1))
      (1 / (((k : ℝ) + 1) * (Real.exp (((k : ℝ) + 1) * u) - 1))) := by
  let v := ((k : ℝ) + 1) * u
  let w := Real.exp (-v)
  have hv : 0 < v := by dsimp [v]; positivity
  have hw₀ : 0 < w := Real.exp_pos _
  have hw₁ : w < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hv)
  have he (j : ℕ) : (Real.exp (-u) ^ (j + 1)) ^ (k + 1) / ((k : ℝ) + 1) =
      w / ((k : ℝ) + 1) * w ^ j := by
    dsimp [w, v]
    rw [← pow_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [he]
  have hs := (hasSum_geometric_of_lt_one hw₀.le hw₁).mul_left (w / ((k : ℝ) + 1))
  convert hs using 1
  change 1 / (((k : ℝ) + 1) * (Real.exp v - 1)) = w / ((k : ℝ) + 1) * (1 - w)⁻¹
  have hd : 0 < Real.exp v - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hv)
  have hk : 0 < (k : ℝ) + 1 := by positivity
  dsimp only [w]
  rw [Real.exp_neg]
  have h' : (1 - (Real.exp v)⁻¹) ≠ 0 := by
    rw [← Real.exp_neg]
    exact (sub_pos.mpr hw₁).ne'
  field_simp [Real.exp_ne_zero, hd.ne', hk.ne', h']

/-- The logarithm of the entire reciprocal-square Euler product, including the
convergence needed to exchange the two infinite sums. -/
theorem twoColourEuler_log {u : ℝ} (hu : 0 < u) :
    let P := ∏' ν : ℕ, (1 - Real.exp (-((ν : ℝ) + 1) * u))⁻¹ ^ (2 : ℕ)
    let L := fun k : ℕ => 1 / (((k : ℝ) + 1) * (Real.exp (((k : ℝ) + 1) * u) - 1))
    0 < P ∧ Summable L ∧ Real.log P = 2 * (∑' k, L k) ∧
      Real.log P ≤ Real.pi ^ 2 / (3 * u) := by
  let q := Real.exp (-u)
  let P (j : ℕ) := (1 - q ^ (j + 1))⁻¹ ^ (2 : ℕ)
  let L (k : ℕ) := 1 / (((k : ℝ) + 1) * (Real.exp (((k : ℝ) + 1) * u) - 1))
  let F (k j : ℕ) := 2 * ((q ^ (j + 1)) ^ (k + 1) / ((k : ℝ) + 1))
  have hq₀ : 0 < q := Real.exp_pos _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have hqPow (j : ℕ) : q ^ (j + 1) < 1 := pow_lt_one₀ hq₀.le hq₁ (Nat.succ_ne_zero j)
  have hpn (j : ℕ) : 0 < 1 - q ^ (j + 1) := sub_pos.mpr (hqPow j)
  have hpos (j : ℕ) : 0 < P j := pow_pos (inv_pos.mpr (hpn j)) 2
  have hL₀ (k : ℕ) : 0 ≤ L k := by
    dsimp [L]
    have hv : 0 < ((k : ℝ) + 1) * u := by positivity
    have hd := sub_pos.mpr (Real.one_lt_exp_iff.mpr hv)
    positivity
  have hL_le (k : ℕ) : L k ≤ (1 / u) * (1 / ((k : ℝ) + 1)^2) := by
    let v := ((k : ℝ) + 1) * u
    have hk : 0 < (k : ℝ) + 1 := by positivity
    have hv : 0 < v := by dsimp [v]; positivity
    change 1 / (((k : ℝ) + 1) * (Real.exp v - 1)) ≤ _
    calc
      _ ≤ 1 / (((k : ℝ) + 1) * v) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp v]) hk.le
      _ = _ := by dsimp [v]; field_simp [hu.ne', hk.ne']
  have hL : Summable L :=
    (zeta_two_positive_indices.summable.mul_left (1 / u)).of_nonneg_of_le hL₀ hL_le
  have hGeom (k : ℕ) : HasSum (F k) (2 * L k) :=
    (hasSum_twoColour_geometric u hu k).mul_left 2
  have hLog (j : ℕ) : HasSum (fun k => F k j) (Real.log (P j)) := by
    have hp : |q ^ (j + 1)| < 1 := by
      rw [abs_of_nonneg (pow_nonneg hq₀.le _)]
      exact hqPow j
    have hs := (Real.hasSum_pow_div_log_of_abs_lt_one hp).mul_left 2
    simpa [F, P, Real.log_pow, Real.log_inv, mul_neg, ← neg_mul] using hs
  have hF : Summable (fun p : ℕ × ℕ => F p.1 p.2) := by
    refine (summable_prod_of_nonneg (fun p => ?_)).mpr
      ⟨fun k => (hGeom k).summable, (hL.mul_left 2).congr (fun k => (hGeom k).tsum_eq.symm)⟩
    dsimp [F]
    positivity
  have hLogs : Summable fun j => Real.log (P j) :=
    (hF.prod_symm.prod).congr (fun j => (hLog j).tsum_eq)
  have hsum : (∑' j, Real.log (P j)) = 2 * (∑' k, L k) := by
    rw [← tsum_mul_left]
    simp_rw [← (hLog _).tsum_eq, ← (hGeom _).tsum_eq]
    exact hF.tsum_comm
  have hprod := Real.rexp_tsum_eq_tprod hpos hLogs
  have hP (j : ℕ) : P j = (1 - Real.exp (-((j : ℝ) + 1) * u))⁻¹ ^ (2 : ℕ) := by
    dsimp [P, q]
    rw [← Real.exp_nat_mul]
    push_cast
    congr 4
    ring
  simp_rw [← hP]
  refine ⟨hprod ▸ Real.exp_pos _, hL, ?_, ?_⟩
  · rw [← hprod, Real.log_exp]
    exact hsum
  · rw [← hprod, Real.log_exp, hsum]
    have h := hL.tsum_le_tsum hL_le (zeta_two_positive_indices.summable.mul_left (1 / u))
    rw [tsum_mul_left, zeta_two_positive_indices.tsum_eq] at h
    calc
      _ ≤ 2 * (1 / u * (Real.pi ^ 2 / 6)) := by linarith
      _ = _ := by ring

/-- The coefficient estimate from the positive two-colour generating series at any
positive real contour parameter. -/
theorem twoColour_exp_bound_param (t : ℕ) {u : ℝ} (hu : 0 < u) :
    (twoColourPartitionCount t : ℝ) ≤ Real.exp (u * t + Real.pi ^ 2 / (3 * u)) := by
  let q := Real.exp (-u)
  have hq₀ : 0 < q := Real.exp_pos _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have hq : ‖(q : ℂ)‖ < 1 := by simpa [abs_of_pos hq₀] using hq₁
  let P (j : ℕ) : ℝ := (1 - q ^ (j + 1))⁻¹ ^ (2 : ℕ)
  let A (j : ℕ) : ℂ := 1 - (q : ℂ) ^ (j + 1)
  have hmA : Multipliable A := ModularForm.multipliable_one_sub_pow hq
  have hPow (j : ℕ) : ‖(q : ℂ) ^ (j + 1)‖ < 1 :=
    norm_pow (q : ℂ) (j + 1) ▸ pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero j)
  have ha (j : ℕ) : A j ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    simpa only [he, norm_one, lt_self_iff_false] using hPow j
  have hsPow : Summable (fun j : ℕ => ‖-((q : ℂ) ^ (j + 1))‖) := by
    simp_rw [norm_neg, norm_pow]
    exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)
  have htA : (∏' j, A j) ≠ 0 := by
    simpa only [A, ← sub_eq_add_neg] using
      tprod_one_add_ne_zero_of_summable (f := fun j => -((q : ℂ) ^ (j + 1)))
        (fun j => by simpa only [← sub_eq_add_neg] using ha j) hsPow
  have hP : ((↑(∏' j, P j) : ℂ)) = twoColourGenerating (q : ℂ) := by
    have hMap : (↑(∏' j, P j) : ℂ) = ∏' j, (P j : ℂ) :=
      Complex.isometry_ofReal.isClosedEmbedding.map_tprod P (g := Complex.ofRealHom)
    rw [hMap]
    have hHas := (hmA.hasProd.inv₀ htA).pow 2
    simpa only [P, A, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, twoColourGenerating] using hHas.tprod_eq
  have hqexp (j : ℕ) : q ^ (j + 1) = Real.exp (-((j : ℝ) + 1) * u) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    ring
  have hb₀ := twoColourEuler_log hu
  dsimp only at hb₀
  simp_rw [← hqexp] at hb₀
  have hb : (∏' j, P j) ≤ Real.exp (Real.pi ^ 2 / (3 * u)) :=
    (Real.log_le_log_iff hb₀.1 (Real.exp_pos _)).mp (by rw [Real.log_exp]; exact hb₀.2.2.2)
  have hs : HasSum (fun j : ℕ => (twoColourPartitionCount j : ℂ) * (q : ℂ)^j)
      (twoColourGenerating (q : ℂ)) := by
    rw [twoColourGenerating_eq_tsum hq]
    exact (summable_norm_twoColourGenerating hq).of_norm.hasSum
  have hReal : HasSum (fun j : ℕ => (twoColourPartitionCount j : ℝ) * q^j) (∏' j, P j) := by
    have hR := Complex.hasSum_re hs
    rw [← hP, Complex.ofReal_re] at hR
    simpa only [← Complex.ofReal_intCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re] using hR
  have hCount (j : ℕ) : 0 ≤ (twoColourPartitionCount j : ℝ) := by
    exact_mod_cast (by rw [twoColourPartitionCount_eq_convolution]; positivity :
      0 ≤ twoColourPartitionCount j)
  have h := (hReal.summable.le_tsum t (fun j _ => mul_nonneg (hCount j) (pow_nonneg hq₀.le _))).trans_eq
    hReal.tsum_eq
  have hqPow : q ^ t = Real.exp (-(u * t)) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hqPow, ← le_div_iff₀ (Real.exp_pos _)] at h
  have h' := h.trans (div_le_div_of_nonneg_right hb (Real.exp_pos (-(u * t))).le)
  rwa [← Real.exp_sub, sub_neg_eq_add, add_comm] at h'

end DurfeeCCS.Step13
