module

public import DurfeeCCS.Step06.RademacherExactBounds
public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The coefficient contour and its deformation within the upper half-plane. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step14

open Complex Set MeasureTheory
open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)
open DurfeeCCS.Step06
open scoped Topology

/-- The integrand for the (n)-th coefficient in the upper half-plane coordinate. -/
def twoColourFareyIntegrand (n : ℕ) (τ : ℂ) : ℂ :=
  twoColourGenerating (exp (2 * (Real.pi : ℂ) * I * τ)) *
    exp (-(2 * (Real.pi : ℂ) * I) * (n : ℂ) * τ)

theorem differentiableOn_twoColourFareyIntegrand (n : ℕ) :
    DifferentiableOn ℂ (twoColourFareyIntegrand n) upperHalfPlaneSet := by
  intro τ hτ
  let q := Function.Periodic.qParam 1
  have hq : q τ ∈ Metric.ball 0 1 := by
    simpa [q] using Function.Periodic.norm_qParam_lt_one (h := 1) one_pos hτ
  have hprod : DifferentiableAt ℂ (fun z : ℂ => ∏' j : ℕ, (1 - q z ^ (j + 1))) τ :=
    (ModularForm.differentiableOn_tprod_one_sub_pow.differentiableAt
      (Metric.isOpen_ball.mem_nhds hq)).comp τ (Function.Periodic.differentiable_qParam (h := 1) τ)
  have hne : (∏' j : ℕ, (1 - q τ ^ (j + 1))) ≠ 0 := ModularForm.eta_tprod_ne_zero hτ
  have hgen : DifferentiableAt ℂ (fun z => twoColourGenerating (q z)) τ :=
    (hprod.inv hne).pow 2
  have hexp : DifferentiableAt ℂ
      (fun z : ℂ => exp (-(2 * (Real.pi : ℂ) * I) * (n : ℂ) * z)) τ := by fun_prop
  have hgen' : DifferentiableAt ℂ
      (fun z : ℂ => twoColourGenerating (exp (2 * (Real.pi : ℂ) * I * z))) τ := by
    simpa only [q, Function.Periodic.qParam, ofReal_one, div_one] using hgen
  unfold twoColourFareyIntegrand
  exact (hgen'.mul hexp).differentiableWithinAt

/-- Additivity of the wedge integral with a fixed start in the upper half-plane. -/
private theorem upper_wedge_sub_eq {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) {c z w : ℂ}
    (hc : c ∈ upperHalfPlaneSet) (hz : z ∈ upperHalfPlaneSet) (hw : w ∈ upperHalfPlaneSet) :
    wedgeIntegral c w f - wedgeIntegral c z f = wedgeIntegral z w f := by
  change 0 < c.im at hc
  change 0 < z.im at hz
  change 0 < w.im at hw
  let p : ℂ := z.re + c.im * I
  let q : ℂ := w.re + z.im * I
  have hrect : Rectangle p q ⊆ upperHalfPlaneSet := by
    apply (convex_halfSpace_im_gt 0).rectangle_subset
    · simpa [p, upperHalfPlaneSet] using hc
    · simpa [q, upperHalfPlaneSet] using hz
    · simpa [p, q, upperHalfPlaneSet] using hz
    · simpa [p, q, upperHalfPlaneSet] using hc
  have hzRect := wedgeIntegral_add_wedgeIntegral_eq (f := f) p q
  rw [hf.isConservativeOn p q hrect, neg_add_cancel] at hzRect
  have hzero :
      (∫ t : ℝ in z.re..w.re, f (t + c.im * I)) -
        (∫ t : ℝ in z.re..w.re, f (t + z.im * I)) +
        I • (∫ t : ℝ in c.im..z.im, f (w.re + t * I)) -
        I • (∫ t : ℝ in c.im..z.im, f (z.re + t * I)) = 0 := by
    simpa [p, q] using hzRect.symm
  have hH (a b y : ℝ) (hy : 0 < y) :
      IntervalIntegrable (fun t : ℝ => f (t + y * I)) volume a b := by
    have hline : ContinuousOn (fun t : ℝ => (t : ℂ) + y * I) (uIcc a b) := by fun_prop
    have hcH : ContinuousOn (fun t : ℝ => f (t + y * I)) (uIcc a b) :=
      hf.continuousOn.comp hline (fun _ _ => by simpa [upperHalfPlaneSet] using hy)
    exact hcH.intervalIntegrable
  have hV (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
      IntervalIntegrable (fun t : ℝ => f (x + t * I)) volume a b :=
    (hf.continuousOn.comp (by fun_prop) (fun t ht => by
      simpa [upperHalfPlaneSet] using (lt_min ha hb).trans_le ht.1)).intervalIntegrable
  have hre :
      (∫ t : ℝ in c.re..w.re, f (t + c.im * I)) =
        (∫ t : ℝ in c.re..z.re, f (t + c.im * I)) +
        (∫ t : ℝ in z.re..w.re, f (t + c.im * I)) :=
    (intervalIntegral.integral_add_adjacent_intervals (hH _ _ _ hc) (hH _ _ _ hc)).symm
  have him :
      (∫ t : ℝ in c.im..w.im, f (w.re + t * I)) =
        (∫ t : ℝ in c.im..z.im, f (w.re + t * I)) +
        (∫ t : ℝ in z.im..w.im, f (w.re + t * I)) :=
    (intervalIntegral.integral_add_adjacent_intervals (hV _ _ _ hc hz) (hV _ _ _ hz hw)).symm
  calc
    _ = wedgeIntegral z w f +
        ((∫ t : ℝ in z.re..w.re, f (t + c.im * I)) -
           (∫ t : ℝ in z.re..w.re, f (t + z.im * I)) +
           I • (∫ t : ℝ in c.im..z.im, f (w.re + t * I)) -
           I • (∫ t : ℝ in c.im..z.im, f (z.re + t * I))) := by
      simp only [wedgeIntegral, hre, him, smul_add]
      abel
    _ = _ := by rw [hzero, add_zero]

theorem isExactOn_twoColourFareyIntegrand (n : ℕ) :
    IsExactOn (twoColourFareyIntegrand n) upperHalfPlaneSet := by
  let f := twoColourFareyIntegrand n
  let G := fun z : ℂ => wedgeIntegral I z f
  have hf := differentiableOn_twoColourFareyIntegrand n
  refine ⟨G, fun z hz => ?_⟩
  have hz' : 0 < z.im := hz
  have hball : Metric.ball z z.im ⊆ upperHalfPlaneSet := by
    intro w hw
    have h : |(w - z).im| < z.im :=
      (Complex.abs_im_le_norm (w - z)).trans_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
    change 0 < w.im
    have h₁ := (abs_lt.mp h).1
    rw [sub_im] at h₁
    linarith
  have hcenter : z ∈ Metric.ball z z.im := Metric.mem_ball_self hz'
  have hder : HasDerivAt (fun w => wedgeIntegral z w f) (f z) z :=
    (hf.mono hball).isConservativeOn.hasDerivAt_wedgeIntegral (hf.continuousOn.mono hball) hcenter
  apply (hder.add_const (G z)).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  exact sub_eq_iff_eq_add.mp (upper_wedge_sub_eq hf (by simp [upperHalfPlaneSet]) hz hw)

private theorem twoColourFareyIntegrand_eq_horizontal (n : ℕ) (ρ x : ℝ) :
    twoColourFareyIntegrand n ((x : ℂ) + (ρ : ℂ) * I) =
      twoColourCoefficientIntegrand n ρ x := by
  unfold twoColourFareyIntegrand twoColourCoefficientIntegrand
  dsimp only
  have he : (2 * (Real.pi : ℂ)) * ((ρ : ℂ) - (x : ℂ) * I) =
      -(2 * (Real.pi : ℂ) * I * ((x : ℂ) + (ρ : ℂ) * I)) := by
    linear_combination (2 * (Real.pi : ℂ) * (ρ : ℂ)) * Complex.I_sq
  rw [he, neg_neg, mul_comm]
  congr 1
  congr 1
  ring

/-- The integrand has period one, including its coefficient-extraction factor. -/
theorem twoColourFareyIntegrand_periodic (n : ℕ) :
    Function.Periodic (twoColourFareyIntegrand n) 1 := by
  intro τ
  unfold twoColourFareyIntegrand
  simp only [mul_add, mul_one, exp_add, exp_two_pi_mul_I]
  rw [show -(2 * (Real.pi : ℂ) * I) * (n : ℂ) =
    -((n : ℂ) * (2 * (Real.pi : ℂ) * I)) by ring]
  rw [exp_neg, exp_nat_mul_two_pi_mul_I, inv_one, mul_one]

private theorem integral_twoColourFareyIntegrand_eq_sub {n : ℕ} {G : ℂ → ℂ}
    (hG : ∀ z ∈ upperHalfPlaneSet, HasDerivAt G (twoColourFareyIntegrand n z) z)
    {a b : ℝ} {γ γ' : ℝ → ℂ}
    (hupper : MapsTo γ (uIcc a b) upperHalfPlaneSet)
    (hγ : ∀ t ∈ uIcc a b, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (uIcc a b)) :
    (∫ t in a..b, twoColourFareyIntegrand n (γ t) * γ' t) = G (γ b) - G (γ a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G ∘ γ)
  · intro t ht
    simpa only [smul_eq_mul, mul_comm] using (hG (γ t) (hupper ht)).scomp t (hγ t ht)
  · exact (((differentiableOn_twoColourFareyIntegrand n).continuousOn.comp
      (fun t ht => (hγ t ht).continuousAt.continuousWithinAt) hupper).mul hγ').intervalIntegrable

/-- Moving a unit-width coefficient contour horizontally does not change its integral. -/
theorem twoColourPartitionCount_eq_farey_horizontal_integral (n : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) (x : ℝ) :
    (twoColourPartitionCount n : ℂ) =
      ∫ t in x..x + 1, twoColourFareyIntegrand n ((t : ℂ) + (ρ : ℂ) * I) := by
  have hp : Function.Periodic (fun t : ℝ => twoColourFareyIntegrand n ((t : ℂ) + (ρ : ℂ) * I)) 1 := by
    intro t
    dsimp only
    rw [Complex.ofReal_add, Complex.ofReal_one, add_right_comm, twoColourFareyIntegrand_periodic n]
  rw [hp.intervalIntegral_add_eq x (-(1 / 2)), show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  simp_rw [twoColourFareyIntegrand_eq_horizontal]
  exact twoColourPartitionCount_eq_horizontal_integral n hρ

/-- The coefficient integral along any finite chain of smoothly parametrized arcs
in the upper half-plane, between points one unit apart on the same horizontal line.
In particular, this applies to a Ford-circle contour once the arc endpoints and
positive heights have been established. -/
theorem twoColourPartitionCount_eq_farey_arc_sum (n N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ)
    (vertex : ℕ → ℂ) (a b : ℕ → ℝ) (γ γ' : ℕ → ℝ → ℂ)
    (hstart : vertex 0 = (x : ℂ) + (ρ : ℂ) * I)
    (hend : vertex N = ((x + 1 : ℝ) : ℂ) + (ρ : ℂ) * I)
    (ha : ∀ j < N, γ j (a j) = vertex j)
    (hb : ∀ j < N, γ j (b j) = vertex (j + 1))
    (hupper : ∀ j < N, MapsTo (γ j) (uIcc (a j) (b j)) upperHalfPlaneSet)
    (hγ : ∀ j < N, ∀ t ∈ uIcc (a j) (b j), HasDerivAt (γ j) (γ' j t) t)
    (hγ' : ∀ j < N, ContinuousOn (γ' j) (uIcc (a j) (b j))) :
    (twoColourPartitionCount n : ℂ) = ∑ j ∈ Finset.range N,
      ∫ t in a j..b j, twoColourFareyIntegrand n (γ j t) * γ' j t := by
  obtain ⟨G, hG⟩ := isExactOn_twoColourFareyIntegrand n
  have hline : (∫ t in x..x + 1, twoColourFareyIntegrand n ((t : ℂ) + (ρ : ℂ) * I)) =
      G (vertex N) - G (vertex 0) := by
    rw [hstart, hend]
    simpa only [mul_one] using
      (integral_twoColourFareyIntegrand_eq_sub hG
        (a := x) (b := x + 1) (γ := fun t : ℝ => (t : ℂ) + (ρ : ℂ) * I) (γ' := fun _ => 1)
        (fun _ _ => by simpa [upperHalfPlaneSet] using hρ)
        (fun t _ => ((hasDerivAt_id (t : ℂ)).comp_ofReal).add_const ((ρ : ℂ) * I))
        continuousOn_const)
  calc
    _ = G (vertex N) - G (vertex 0) := (twoColourPartitionCount_eq_farey_horizontal_integral n hρ x).trans hline
    _ = ∑ j ∈ Finset.range N, (G (vertex (j + 1)) - G (vertex j)) :=
      (Finset.sum_range_sub (G ∘ vertex) N).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [integral_twoColourFareyIntegrand_eq_sub hG (hupper j hj') (hγ j hj') (hγ' j hj'),
        ha j hj', hb j hj']

end DurfeeCCS.Step14
