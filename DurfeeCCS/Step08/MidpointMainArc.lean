module

public import DurfeeCCS.Step08.LogArcMean
public import DurfeeCCS.Step08.PhaseGap
public import DurfeeCCS.Step08.SaddleBesselAverage
public import DurfeeCCS.Step08.SaddleNormalization
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! The rescaled first-saddle error integral in (41). -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06 MeasureTheory

def firstSaddleMainArcKernel (n : ℕ) (r η θ : ℝ) : ℝ :=
  let u := saddleU n r
  let ζ := verticalPoint u (u * η)
  Real.exp (-saddleOmega n r * saddleGap r θ η) *
    (Real.exp ‖pairedLog r θ ζ - saddleG r θ / ζ‖ - 1)

def firstSaddleMainArcBudget (n : ℕ) (r : ℝ) : ℝ :=
  3 * saddleOmega n r / (4 * Real.pi) *
    ∫ η in (0 : ℝ)..16, ∫ θ in -Real.pi..Real.pi, firstSaddleMainArcKernel n r η θ

theorem verticalPoint_mul (u η : ℝ) :
    verticalPoint u (u * η) = (u : ℂ) * (1 + (η : ℂ) * I) := by
  unfold verticalPoint
  push_cast
  ring

theorem continuous_firstSaddleMainArcKernel {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (hr₁ : r ≤ 1) :
    Continuous (fun p : ℝ × ℝ => firstSaddleMainArcKernel n r p.1 p.2) := by
  let u := saddleU n r
  have hu : 0 < u := saddleU_pos hn hr
  have hr' : |r| ≤ 1 := by simpa [abs_of_pos hr] using hr₁
  have hg : Continuous (fun p : ℝ × ℝ => saddleG r p.2) :=
    (continuous_saddleG hr').comp continuous_snd
  have hgr : Continuous (fun p : ℝ × ℝ => (saddleG r p.2).re) := continuous_re.comp hg
  have hgi : Continuous (fun p : ℝ × ℝ => (saddleG r p.2).im) := continuous_im.comp hg
  have hpar : Continuous (fun p : ℝ × ℝ => (u * p.1, p.2)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hlog : Continuous (fun p : ℝ × ℝ => pairedLog r p.2 (verticalPoint u (u * p.1))) := by
    have h := (continuous_pairedLog_vertical r hr' hu).comp hpar
    simpa only [Function.comp_def] using h
  have hζ : Continuous (fun p : ℝ × ℝ => verticalPoint u (u * p.1)) := by
    unfold verticalPoint
    exact continuous_const.add ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst)).mul continuous_const)
  have hquot : Continuous (fun p : ℝ × ℝ => saddleG r p.2 / verticalPoint u (u * p.1)) :=
    hg.div hζ (fun p => verticalPoint_ne_zero hu (u * p.1))
  have hgap : Continuous (fun p : ℝ × ℝ => saddleGap r p.2 p.1) := by
    unfold saddleGap
    apply continuous_const.sub
    have ha : 0 < (saddleS r).re := (saddleS_components hr).1.trans (saddleS_components hr).2
    refine (hgr.add (continuous_fst.mul hgi)).div ?_ ?_
    · exact continuous_const.mul (continuous_const.add (continuous_fst.pow 2))
    · intro p
      exact (mul_pos (sq_pos_of_pos ha) (add_pos_of_pos_of_nonneg one_pos (sq_nonneg p.1))).ne'
  have hphase : Continuous (fun p : ℝ × ℝ =>
      Real.exp (-saddleOmega n r * saddleGap r p.2 p.1)) :=
    Real.continuous_exp.comp (continuous_const.mul hgap)
  have hnorm : Continuous (fun p : ℝ × ℝ =>
      ‖pairedLog r p.2 (verticalPoint u (u * p.1)) -
        saddleG r p.2 / verticalPoint u (u * p.1)‖) := (hlog.sub hquot).norm
  have herror : Continuous (fun p : ℝ × ℝ =>
      Real.exp ‖pairedLog r p.2 (verticalPoint u (u * p.1)) -
        saddleG r p.2 / verticalPoint u (u * p.1)‖ - 1) :=
    (Real.continuous_exp.comp hnorm).sub continuous_const
  simpa only [firstSaddleMainArcKernel, u, Pi.mul_def] using hphase.mul herror

theorem firstSaddleMainArcKernel_nonneg (n : ℕ) (r η θ : ℝ) :
    0 ≤ firstSaddleMainArcKernel n r η θ := by
  unfold firstSaddleMainArcKernel
  exact mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr (Real.one_le_exp (norm_nonneg _)))

end DurfeeCCS.Step08
