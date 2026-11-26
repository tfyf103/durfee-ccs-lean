module

public import DurfeeCCS.Step08.SaddleBesselJacobian
public import DurfeeCCS.Step08.SaddleBesselCentral
public import DurfeeCCS.Step08.SaddleBesselModel
public import DurfeeCCS.Step08.ExpRemainder
public import DurfeeCCS.Step08.PhaseGapCentral
import DurfeeCCS.Step08.PhaseGap

/-! The central-arc estimate in Lemma 3.4. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex Set MeasureTheory DurfeeCCS.Step06 DurfeeCCS.Step07

private theorem saddleCentral_weighted_error {A B T : ℂ} {ω γ ψ : ℝ}
    (hω : 0 < ω) (hψ : 0 ≤ ψ) (hψ' : ψ ≤ 0.3)
    (hAB : ‖A - B‖ ≤ 2.46 * ω * ψ ^ 2)
    (hRe : max A.re B.re ≤ -(γ * ω) * ψ) (hT : ‖T - 1‖ ≤ 0.87 * ψ) :
    ‖T * Complex.exp A‖ * (2.2 / ω) + ‖T * Complex.exp A - Complex.exp B‖ ≤
      Real.exp (-(γ * ω) * ψ) * (2.46 * ω * ψ ^ 2 + 0.87 * ψ + 2.7742 / ω) := by
  let e := Real.exp (-(γ * ω) * ψ)
  have hA : ‖Complex.exp A‖ ≤ e := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((le_max_left _ _).trans hRe)
  have hE : ‖Complex.exp A - Complex.exp B‖ ≤ e * (2.46 * ω * ψ ^ 2) := by
    rw [mul_comm e]
    exact (norm_exp_sub_exp_le _ _).trans
      (mul_le_mul hAB (Real.exp_le_exp.mpr hRe) (Real.exp_nonneg _) (by positivity))
  have hTN : ‖T‖ ≤ 1 + 0.87 * ψ := by
    calc
      _ = ‖(T - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖T - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_one, add_comm]; exact add_le_add le_rfl hT
  have hste : ‖T * Complex.exp A‖ * (2.2 / ω) ≤ e * (2.7742 / ω) := by
    rw [norm_mul]
    calc
      _ ≤ ((1 + 0.87 * 0.3) * e) * (2.2 / ω) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul (hTN.trans ?_) hA (norm_nonneg _) (by positivity)) (by positivity)
        linarith
      _ = _ := by ring
  have hdiff : ‖T * Complex.exp A - Complex.exp B‖ ≤
      e * (0.87 * ψ) + e * (2.46 * ω * ψ ^ 2) := by
    rw [show T * Complex.exp A - Complex.exp B =
      (T - 1) * Complex.exp A + (Complex.exp A - Complex.exp B) by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hE)
    rw [norm_mul, mul_comm e]
    exact mul_le_mul hT hA (norm_nonneg _) (by positivity)
  exact (add_le_add hste hdiff).trans_eq (by ring)

/-- The leading Bessel kernel after multiplying by the constant in the angular Jacobian. -/
private theorem saddleBesselCentral_kernel_model {n : ℕ} (hn : 0 < n) {r : ℝ} {p : ℂ}
    (hs : 0 < (saddleS r).re) (hp : 0 < p.re) (hq : 0 < (p / saddleS r).re) :
    (Real.sqrt 2 : ℂ) * (((Real.pi : ℂ)⁻¹) * (p / (Real.sqrt n : ℂ)) *
      (Complex.exp (2 * (Real.sqrt n : ℂ) * p) /
        (2 * (Real.pi : ℂ) * (2 * (Real.sqrt n : ℂ) * p)).sqrt)) =
      saddleBesselPrefactor n r * (p / saddleS r).sqrt *
        Complex.exp (2 * (Real.sqrt n : ℂ) * (p - saddleS r)) := by
  let s := saddleS r
  let q := p / s
  let v := Real.sqrt n
  have hs₀ : s ≠ 0 := fun he => by simp [s, he] at hs
  have hp₀ : p ≠ 0 := fun he => by simp [he] at hp
  have hpsq : p.sqrt ^ 2 = p := principalSqrt_sq _
  have hps : p.sqrt ≠ 0 := fun he => by
    rw [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hpsq
    exact hp₀ hpsq.symm
  have hv : 0 < v := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hv₀ : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hπ₀ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hvS : (Real.sqrt v : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  have hπS : (Real.sqrt Real.pi : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h₂S : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast
    (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)).ne'
  have h₂sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num), Complex.ofReal_ofNat]
  have hsroot : p.sqrt = s.sqrt * q.sqrt := by
    have he : p = s * q := by dsimp [q]; field_simp
    conv_lhs => rw [he]
    apply sqrt_mul_right_half_planes hs hq
  have hDen :
      (2 * (Real.pi : ℂ) * (2 * (v : ℂ) * p)).sqrt =
        (2 * (Real.sqrt Real.pi : ℂ) * (Real.sqrt v : ℂ)) * p.sqrt := by
    rw [show 2 * (Real.pi : ℂ) * (2 * (v : ℂ) * p) = ((4 * Real.pi * v : ℝ) : ℂ) * p by
      push_cast; ring, sqrt_ofReal_mul _ (by positivity), Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by
        simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    ring
  have hExp : Complex.exp (2 * (v : ℂ) * p) =
      Complex.exp (2 * (v : ℂ) * s) * Complex.exp (2 * (v : ℂ) * (p - s)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  change (Real.sqrt 2 : ℂ) * (((Real.pi : ℂ)⁻¹) * (p / (v : ℂ)) *
      (Complex.exp (2 * (v : ℂ) * p) /
        (2 * (Real.pi : ℂ) * (2 * (v : ℂ) * p)).sqrt)) =
      saddleBesselPrefactor n r * q.sqrt * Complex.exp (2 * (v : ℂ) * (p - s))
  rw [hDen, hExp, saddleBesselPrefactor, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_mul]
  change _ = (s.sqrt * Complex.exp (2 * (v : ℂ) * s) / _) * q.sqrt * _
  have hR : s.sqrt * Complex.exp (2 * (v : ℂ) * s) /
      ((Real.pi : ℂ) * ((Real.sqrt 2 : ℂ) * (Real.sqrt Real.pi : ℂ)) * (v : ℂ) * (Real.sqrt v : ℂ)) *
      q.sqrt =
      p.sqrt * Complex.exp (2 * (v : ℂ) * s) /
        ((Real.pi : ℂ) * ((Real.sqrt 2 : ℂ) * (Real.sqrt Real.pi : ℂ)) * (v : ℂ) * (Real.sqrt v : ℂ)) := by
    rw [hsroot]
    ring
  rw [hR]
  field_simp
  ring_nf
  rw [h₂sq, hpsq]
  ring

private theorem saddleBessel_central_exponent_bounds {n : ℕ} (hn : 0 < n)
    {r θ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hθ : |θ| ≤ Real.pi / 2)
    (hcut : 1 - Real.cos θ ≤ 0.3) :
    let ψ := 1 - Real.cos θ
    let A := 2 * (Real.sqrt n : ℂ) * ((saddleG r θ).sqrt - saddleS r)
    let B := -saddleBesselRate n r * (ψ : ℂ)
    ‖A - B‖ ≤ 2.46 * saddleOmega n r * ψ ^ 2 ∧
      max A.re B.re ≤ -(saddleGamma r * saddleOmega n r) * ψ := by
  let s := saddleS r
  let p := (saddleG r θ).sqrt
  let v := Real.sqrt n
  let ψ := 1 - Real.cos θ
  let A := 2 * (v : ℂ) * (p - s)
  let B := -saddleBesselRate n r * (ψ : ℂ)
  let γ := saddleGamma r
  let ω := saddleOmega n r
  have hv := Real.sqrt_pos.mpr (show 0 < (n : ℝ) by exact_mod_cast hn)
  have hω : 0 < ω := saddleOmega_pos hn hr
  have hψ : 0 ≤ ψ := sub_nonneg.mpr (Real.cos_le_one θ)
  have ha := (saddleS_components hr).1.trans (saddleS_components hr).2
  have ha₀ : ((saddleS r).re : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hs₀ : saddleS r ≠ 0 := by intro h; simp [h] at ha
  have hγ := saddleGamma_bounds r
  constructor
  · have h := (saddleG_central_errors hr hr₁ hcut).1
    change ‖2 * (p - s) / (s.re : ℂ) +
      (2 * saddleBesselSlope r) * (ψ : ℂ) / ((s.re : ℂ) * s)‖ ≤ 2.46 * ψ ^ 2 at h
    have hEq : A - B = (ω : ℂ) * (2 * (p - s) / (s.re : ℂ) +
      (2 * saddleBesselSlope r) * (ψ : ℂ) / ((s.re : ℂ) * s)) := by
      dsimp only [A, B, ω, s]
      unfold saddleBesselRate saddleOmega
      push_cast
      field_simp
      ring
    rw [hEq, norm_mul, Complex.norm_of_nonneg hω.le]
    exact (mul_le_mul_of_nonneg_left h hω.le).trans_eq (by ring)
  · apply max_le
    · have hGap := saddleG_sqrt_re_le hr hr₁ hθ
      change p.re ≤ s.re * Real.sqrt (1 - γ * ψ) at hGap
      have hψγ : γ * ψ ≤ 0.3 :=
        (mul_le_of_le_one_left hψ hγ.2).trans hcut
      have hSqrt : Real.sqrt (1 - γ * ψ) ≤ 1 - γ * ψ / 2 := by
        apply (Real.sqrt_le_left (by linarith)).mpr
        nlinarith [sq_nonneg (γ * ψ)]
      have hG := hGap.trans (mul_le_mul_of_nonneg_left hSqrt ha.le)
      have hG' := mul_le_mul_of_nonneg_left hG (show 0 ≤ 2 * v by positivity)
      have hA : A.re = 2 * v * (p.re - s.re) := by
        change ((2 * (v : ℂ)) * (p - s)).re = _
        rw [show 2 * (v : ℂ) = ((2 * v : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
          Complex.sub_re]
      rw [hA]
      change _ ≤ -(γ * (s.re * v)) * ψ
      nlinarith only [hG']
    · change (-saddleBesselRate n r * (ψ : ℂ)).re ≤ -(γ * ω) * ψ
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.neg_re]
      exact mul_le_mul_of_nonneg_right (neg_le_neg (saddleBesselRate_bounds hr hr₁).1) hψ

/-- The normalized Bessel kernel written in the variable `ψ` of (36). -/
def saddleBesselCentralDensity (n : ℕ) (r ψ : ℝ) : ℂ :=
  (Real.sqrt 2 : ℂ) * ((Real.pi : ℂ)⁻¹ *
    saddleBesselKernel n (saddleG r (Real.arccos (1 - ψ)))) /
      ((Real.sqrt ψ * Real.sqrt (1 - ψ / 2) : ℝ) : ℂ)

private theorem norm_saddleBesselCentralDensity_sub_model {n : ℕ} (hn : 0 < n)
    {r ψ : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hψ : 0 < ψ) (hψ' : ψ ≤ 0.3) :
    ‖saddleBesselCentralDensity n r ψ - saddleBesselModel n r ψ‖ ≤
      ‖saddleBesselPrefactor n r‖ * saddleCentralErrorDensity (saddleOmega n r) (saddleGamma r) ψ := by
  let θ := Real.arccos (1 - ψ)
  let s := saddleS r
  let p := (saddleG r θ).sqrt
  let v := Real.sqrt n
  let z := 2 * (v : ℂ) * p
  let t := Real.sqrt (1 - ψ / 2)
  let u := Real.sqrt ψ
  let C := saddleBesselPrefactor n r
  let A := 2 * (v : ℂ) * (p - s)
  let B := -saddleBesselRate n r * (ψ : ℂ)
  let T := (p / s).sqrt / (t : ℂ)
  let D := Complex.exp z / (2 * (Real.pi : ℂ) * z).sqrt
  let X := (Real.sqrt 2 : ℂ) * (Real.pi : ℂ)⁻¹ * (p / (v : ℂ)) / ((u * t : ℝ) : ℂ)
  let ω := saddleOmega n r
  let γ := saddleGamma r
  have hv : 0 < v := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hω : 0 < ω := saddleOmega_pos hn hr
  have hθ' : 1 - Real.cos θ = ψ := by
    dsimp [θ]
    rw [Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hcut : 1 - Real.cos θ ≤ 0.3 := by rw [hθ']; exact hψ'
  have hθ : |θ| ≤ Real.pi / 2 := by
    rw [abs_of_nonneg (Real.arccos_nonneg _)]
    exact Real.arccos_le_pi_div_two.mpr (by linarith)
  obtain ⟨hz, hzr⟩ := saddleG_central_bessel_arguments hr hr₁ hcut hv
  have hzp : 0 < z.re := (show 0 < 1.35 * ω by positivity).trans_le hzr
  have hp : 0 < p.re := by
    change 0 < ((2 * (v : ℂ)) * p).re at hzp
    rw [show 2 * (v : ℂ) = ((2 * v : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul] at hzp
    exact pos_of_mul_pos_right hzp (by positivity)
  have hs := (saddleS_components hr).1.trans (saddleS_components hr).2
  have hqr : 0 < (p / s).re := (saddleG_central_sqrt_ratio hr hr₁ hcut).2
  have hX : saddleBesselCentralDensity n r ψ = X * besselI 1 z := by
    unfold saddleBesselCentralDensity
    rw [saddleBesselKernel_eq_besselI hn]
    dsimp only [X, p, z, θ, u, t, v]
    ring
  have hXD : X * D = C / (u : ℂ) * (T * Complex.exp A) := by
    have he := saddleBesselCentral_kernel_model hn hs hp hqr
    change (Real.sqrt 2 : ℂ) * ((Real.pi : ℂ)⁻¹ * (p / (v : ℂ)) * D) =
      C * (p / s).sqrt * Complex.exp A at he
    calc
      _ = ((Real.sqrt 2 : ℂ) * ((Real.pi : ℂ)⁻¹ * (p / (v : ℂ)) * D)) /
          ((u * t : ℝ) : ℂ) := by unfold X; ring
      _ = _ := by rw [he, Complex.ofReal_mul]; unfold T; ring
  have hM : saddleBesselModel n r ψ = C / (u : ℂ) * Complex.exp B := by
    unfold saddleBesselModel
    dsimp only [C, u, B]
    ring
  have hshift := saddleBessel_central_exponent_bounds hn hr hr₁ hθ hcut
  dsimp only at hshift
  rw [hθ'] at hshift
  have hT := (saddleG_central_errors hr hr₁ hcut).2
  rw [hθ'] at hT
  have hrel := besselI_one_central_error hω hz hzr
  have hBess : ‖X * (besselI 1 z - D)‖ ≤
      ‖C / (u : ℂ)‖ * (‖T * Complex.exp A‖ * (2.2 / ω)) := by
    calc
      _ ≤ ‖X‖ * (‖D‖ * (2.2 / ω)) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hrel (norm_nonneg _)
      _ = _ := by rw [← mul_assoc, ← norm_mul, hXD, norm_mul, mul_assoc]
  rw [hX, hM, show X * besselI 1 z - C / (u : ℂ) * Complex.exp B =
    X * (besselI 1 z - D) + (X * D - C / (u : ℂ) * Complex.exp B) by ring, hXD, ← mul_sub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul (C / (u : ℂ))]
  refine (add_le_add hBess le_rfl).trans ?_
  rw [← mul_add]
  refine (mul_le_mul_of_nonneg_left
    (saddleCentral_weighted_error hω hψ.le hψ' hshift.1 hshift.2 hT) (norm_nonneg _)).trans_eq ?_
  rw [norm_div, Complex.norm_of_nonneg (Real.sqrt_nonneg _), saddleCentralErrorDensity]
  change ‖C‖ / Real.sqrt ψ *
      (Real.exp (-(γ * ω) * ψ) * (2.46 * ω * ψ ^ 2 + 0.87 * ψ + 2.7742 / ω)) =
    ‖C‖ * (Real.exp (-(γ * ω) * ψ) * ψ ^ (-1 / 2 : ℝ) *
      (2.46 * ω * ψ ^ 2 + 0.87 * ψ + 2.7742 / ω))
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hψ.le]
  ring

/-- The first term on the right in (37), bounded by the central Gamma integral. -/
theorem saddleBessel_central_cutoff_error {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    ‖(∫ θ in -saddleBesselCutoff..saddleBesselCutoff,
      (Real.pi : ℂ)⁻¹ * saddleBesselKernel n (saddleG r θ)) -
      (∫ ψ in (0 : ℝ)..0.3, saddleBesselModel n r ψ)‖ ≤
      saddleAmplitude n r * (firstSaddleC (saddleGamma r) / saddleOmega n r) := by
  let K (θ : ℝ) := (Real.pi : ℂ)⁻¹ * saddleBesselKernel n (saddleG r θ)
  let F := saddleBesselCentralDensity n r
  let m := saddleBesselModel n r
  let c := saddleBesselCutoff
  let C := saddleBesselPrefactor n r
  let ω := saddleOmega n r
  let γ := saddleGamma r
  let G := saddleCentralErrorDensity ω γ
  let U := Ioc (0 : ℝ) 0.3
  have hR : |r| ≤ 1 := by simpa [abs_of_pos hr] using hr₁
  have hK : Continuous K := continuous_const.mul (continuous_saddleBesselAngular n hR)
  have he : Function.Even K := fun θ => by simp only [K, saddleG_even r θ]
  have hCos : 1 - Real.cos c = 0.3 := by
    dsimp [c, saddleBesselCutoff]
    rw [Real.cos_arccos (by norm_num) (by norm_num)]
    norm_num
  have hJ := integral_saddleBessel_angle_change K hK he saddleBesselCutoff_nonneg saddleBesselCutoff_le
  change (∫ θ in -c..c, K θ) = _ at hJ
  rw [show 1 - Real.cos saddleBesselCutoff = 0.3 from hCos, ← intervalIntegral.integral_const_mul] at hJ
  have hJ' : (∫ θ in -c..c, K θ) = ∫ ψ in (0 : ℝ)..0.3, F ψ := by
    rw [hJ]
    apply intervalIntegral.integral_congr
    intro ψ _
    dsimp [F, K, saddleBesselCentralDensity]
    ring
  have hω : 0 < ω := saddleOmega_pos hn hr
  have hγ : 0 < γ := (by norm_num : (0 : ℝ) < 0.55).trans_le (saddleGamma_bounds r).1
  have hsub : U ⊆ Ioi 0 := fun _ h => h.1
  have hG : IntegrableOn G U := (integrable_saddleCentralErrorDensity hω hγ).mono_set hsub
  have hMG : IntegrableOn (fun ψ => ‖C‖ * G ψ) U := hG.const_mul _
  have hbound : ∀ᵐ ψ ∂volume.restrict U, ‖F ψ - m ψ‖ ≤ ‖C‖ * G ψ := by
    filter_upwards [ae_restrict_mem (μ := volume) (show MeasurableSet U from measurableSet_Ioc)] with ψ hψ
    exact norm_saddleBesselCentralDensity_sub_model hn hr hr₁ hψ.1 hψ.2
  have hFm : Measurable F := by
    change Measurable (fun ψ : ℝ => (Real.sqrt 2 : ℂ) * K (Real.arccos (1 - ψ)) /
      ((Real.sqrt ψ * Real.sqrt (1 - ψ / 2) : ℝ) : ℂ))
    fun_prop
  have hmM : Measurable m := by unfold m saddleBesselModel; fun_prop
  have hD : IntegrableOn (fun ψ => F ψ - m ψ) U :=
    hMG.mono' (hFm.sub hmM).aestronglyMeasurable hbound
  have hm : IntegrableOn m U :=
    (integrable_saddleBesselModel (saddleBesselRate_re_pos hn hr hr₁)).mono_set hsub
  have hF : IntegrableOn F U := by
    convert hD.add hm using 1
    ext ψ
    change F ψ = F ψ - m ψ + m ψ
    abel
  have hPos : 0 ≤ ∫ ψ in U, G ψ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) (show MeasurableSet U from measurableSet_Ioc)] with ψ hψ
    have hψ' : 0 ≤ ψ := hψ.1.le
    dsimp [G, saddleCentralErrorDensity]
    positivity
  rw [hJ', intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num)]
  change ‖(∫ ψ in U, F ψ) - (∫ ψ in U, m ψ)‖ ≤ _
  rw [← integral_sub hF hm]
  calc
    _ ≤ ∫ ψ in U, ‖C‖ * G ψ := norm_integral_le_of_norm_le hMG hbound
    _ = ‖C‖ * ∫ ψ in U, G ψ := integral_const_mul _ _
    _ ≤ (saddleAmplitude n r * Real.sqrt (1.5 * ω / Real.pi)) * ∫ ψ in U, G ψ :=
      mul_le_mul_of_nonneg_right (norm_saddleBesselPrefactor_le hn hr hr₁) hPos
    _ ≤ _ := by
      rw [mul_assoc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 0.3)]
      exact mul_le_mul_of_nonneg_left (integral_saddleCentralErrorDensity_truncated hω hγ)
        (saddleAmplitude_pos hn hr).le

/-- The third term of (37), with the central model's tail constant. -/
theorem norm_saddleBesselModel_tail {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) :
    ‖∫ ψ in Ioi (0.3 : ℝ), saddleBesselModel n r ψ‖ ≤
      saddleAmplitude n r *
        ((2.4 / Real.sqrt (saddleOmega n r)) *
          Real.exp (-0.3 * saddleGamma r * saddleOmega n r)) := by
  let ω := saddleOmega n r
  let γ := saddleGamma r
  let k := saddleBesselRate n r
  let C := saddleBesselPrefactor n r
  let f (ψ : ℝ) := Real.exp (-(γ * ω) * ψ) / Real.sqrt ψ
  have hγ : 0.55 ≤ γ := (saddleGamma_bounds r).1
  have hω : 0 < ω := saddleOmega_pos hn hr
  have ha : 0 < γ * ω := mul_pos ((by norm_num : (0 : ℝ) < 0.55).trans_le hγ) hω
  have hi : IntegrableOn f (Ioi 0.3) := by
    have hi₀ := real_laplace_moment_integrable ha (p := -1 / 2) (by norm_num)
    refine (hi₀.mono_set (show Ioi (0.3 : ℝ) ⊆ Ioi 0 from
      fun x h => (by norm_num : (0 : ℝ) < 0.3).trans h)).congr ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with ψ hψ
    have hψ' : 0 < ψ := (by norm_num : (0 : ℝ) < 0.3).trans hψ
    dsimp [f]
    simp only [Real.sqrt_eq_rpow, div_eq_mul_inv]
    rw [← Real.rpow_neg hψ'.le]
    norm_num
  have hf : 0 ≤ ∫ ψ in Ioi (0.3 : ℝ), f ψ := by
    apply integral_nonneg
    intro ψ
    unfold f
    positivity
  have hbound : ‖∫ ψ in Ioi (0.3 : ℝ), saddleBesselModel n r ψ‖ ≤
      ∫ ψ in Ioi (0.3 : ℝ), ‖C‖ * f ψ := by
    apply norm_integral_le_of_norm_le (hi.const_mul _)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with ψ hψ
    have hψ' : 0 < ψ := (by norm_num : (0 : ℝ) < 0.3).trans hψ
    unfold saddleBesselModel f
    rw [norm_mul, norm_div, Complex.norm_exp, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
      Complex.mul_re, Complex.neg_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    gcongr
    exact (saddleBesselRate_bounds hr hr₁).1
  rw [integral_const_mul] at hbound
  refine hbound.trans ((mul_le_mul_of_nonneg_right (norm_saddleBesselPrefactor_le hn hr hr₁) hf).trans ?_)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (saddleModel_tail_le hω hγ) (saddleAmplitude_pos hn hr).le

/-- The three-region estimate (31) once the two outer angular intervals are bounded. -/
theorem saddleBessel_error_of_outer_cutoff {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hOuter :
      let K (θ : ℝ) := (Real.pi : ℂ)⁻¹ * saddleBesselKernel n (saddleG r θ)
      let ω := saddleOmega n r
      let γ := saddleGamma r
      (∫ θ in (-Real.pi / 2)..-saddleBesselCutoff, ‖K θ‖) +
        (∫ θ in saddleBesselCutoff..(Real.pi / 2), ‖K θ‖) ≤
        saddleAmplitude n r * ((11.1 / γ) / Real.sqrt ω * Real.exp (-0.3 * γ * ω) +
          19 * ω ^ 2 * Real.exp (-ω))) :
    |saddleBesselAverage n r - saddleAmplitude n r * Real.cos (saddlePhase n r)| ≤
      saddleAmplitude n r * firstSaddleE (saddleOmega n r) (saddleGamma r) := by
  have hR : |r| ≤ 1 := by simpa [abs_of_pos hr] using hr₁
  have hRate := saddleBesselRate_re_pos hn hr hr₁
  have hsplit := saddleBesselAverage_cutoff_error n hR saddleBesselCutoff_le
    (by norm_num : (0 : ℝ) ≤ 0.3) (saddleBesselModel n r) (integrable_saddleBesselModel hRate)
  dsimp only at hsplit hOuter
  rw [integral_saddleBesselModel_re hn hr hRate] at hsplit
  refine hsplit.trans ((add_le_add (add_le_add (saddleBessel_central_cutoff_error hn hr hr₁) hOuter)
    (norm_saddleBesselModel_tail hn hr hr₁)).trans_eq ?_)
  unfold firstSaddleE
  ring

end DurfeeCCS.Step08
