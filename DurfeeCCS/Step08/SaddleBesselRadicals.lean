module

public import DurfeeCCS.Step06.Branches

/-! Bounds for the radicals that occur in the central saddle approximation. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step08

open Complex DurfeeCCS.Step06

theorem principalSqrt_re_eq (z : ℂ) :
    z.sqrt.re = Real.sqrt ((‖z‖ + z.re) / 2) := by
  rw [Complex.sqrt_eq_real_add_ite]
  split_ifs <;> simp [Complex.mul_re]

theorem norm_sqrt_one_add_sub_one (w : ℂ) :
    ‖(1 + w).sqrt - 1‖ ≤ ‖w‖ / (1 + Real.sqrt (1 - ‖w‖)) := by
  let q := (1 + w).sqrt
  have hq : q.re = Real.sqrt ((‖1 + w‖ + (1 + w).re) / 2) := principalSqrt_re_eq _
  have hqre : Real.sqrt (1 - ‖w‖) ≤ q.re := by
    rw [hq]
    apply Real.sqrt_le_sqrt
    have h₁ := Complex.re_le_norm (1 + w)
    have h₂ := (abs_le.mp (Complex.abs_re_le_norm w)).1
    simp only [Complex.add_re, Complex.one_re] at h₁ ⊢
    linarith
  have hfactor : (q - 1) * (q + 1) = w := by
    calc
      _ = q ^ 2 - 1 := by ring
      _ = _ := by dsimp only [q]; rw [principalSqrt_sq]; ring
  apply (le_div_iff₀ (by positivity)).mpr
  have hplus : 1 + Real.sqrt (1 - ‖w‖) ≤ ‖q + 1‖ := by
    refine le_trans ?_ (Complex.re_le_norm (q + 1))
    simp only [Complex.add_re, Complex.one_re]
    linarith
  calc
    _ ≤ ‖q - 1‖ * ‖q + 1‖ := mul_le_mul_of_nonneg_left hplus (norm_nonneg _)
    _ = ‖w‖ := by rw [← norm_mul, hfactor]

/-- The square-root remainder has an exact algebraic form on the principal branch. -/
theorem sqrt_one_add_remainder (w : ℂ) :
    (1 + w).sqrt - 1 - w / 2 = -((1 + w).sqrt - 1) ^ 2 / 2 := by
  have h := principalSqrt_sq (1 + w)
  linear_combination h / 2

/-- A practical linear bound for the square-root perturbation on the central interval. -/
theorem saddleCentral_sqrt_perturbation {w : ℂ} {ψ : ℝ} (hψ : 0 ≤ ψ) (hψ' : ψ ≤ 0.3)
    (hw : ‖w‖ ≤ 1.34 * ψ) :
    ‖(1 + w).sqrt - 1‖ ≤ 0.76 * ψ := by
  have hw' : ‖w‖ ≤ 0.402 := by linarith
  have hs : (0.77 : ℝ) ≤ Real.sqrt (1 - ‖w‖) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  refine (norm_sqrt_one_add_sub_one w).trans ?_
  apply (div_le_iff₀ (by positivity)).mpr
  refine hw.trans ?_
  nlinarith [mul_nonneg hψ (sub_nonneg.mpr hs)]

/-- The corresponding perturbation for the iterated square root. -/
theorem saddleCentral_fourthRoot_perturbation {w : ℂ} {ψ : ℝ} (hψ : 0 ≤ ψ) (hψ' : ψ ≤ 0.3)
    (hw : ‖w‖ ≤ 1.34 * ψ) :
    ‖(1 + w).sqrt.sqrt - 1‖ ≤ 0.42 * ψ := by
  let u := (1 + w).sqrt - 1
  have hu : ‖u‖ ≤ 0.76 * ψ := saddleCentral_sqrt_perturbation hψ hψ' hw
  have hst : (0.87 : ℝ) ≤ Real.sqrt (1 - ‖u‖) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  rw [show (1 + w).sqrt = 1 + u by dsimp [u]; ring]
  refine (norm_sqrt_one_add_sub_one u).trans ?_
  apply (div_le_iff₀ (by positivity)).mpr
  refine hu.trans ?_
  nlinarith [mul_nonneg hψ (sub_nonneg.mpr hst)]

/-- The central amplitude estimate in (33) from the bound on the normalized phase. -/
theorem saddleCentral_amplitude_error {w : ℂ} {ψ : ℝ} (hψ : 0 ≤ ψ) (hψ' : ψ ≤ 0.3)
    (hw : ‖w‖ ≤ 1.34 * ψ) :
    ‖(1 + w).sqrt.sqrt / (Real.sqrt (1 - ψ / 2) : ℂ) - 1‖ ≤ 0.87 * ψ := by
  let q := (1 + w).sqrt.sqrt
  let t := Real.sqrt (1 - ψ / 2)
  have htlo : 0.92 ≤ t := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have ht : 0 < t := (by norm_num : (0 : ℝ) < 0.92).trans_le htlo
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have ht' : t ≤ 1 := by
    dsimp [t]
    simpa using Real.sqrt_le_sqrt (show 1 - ψ / 2 ≤ 1 by linarith)
  have ht2 : t ^ 2 = 1 - ψ / 2 := Real.sq_sqrt (by linarith)
  have htdiff : 1 - t ≤ 0.27 * ψ := by
    have hfac : (1 - t) * (1 + t) = ψ / 2 := by nlinarith
    have hle := mul_le_mul_of_nonneg_left
      (show (1.92 : ℝ) ≤ 1 + t by linarith) (sub_nonneg.mpr ht')
    linarith
  have hq : ‖q - 1‖ ≤ 0.42 * ψ := saddleCentral_fourthRoot_perturbation hψ hψ' hw
  change ‖q / (t : ℂ) - 1‖ ≤ 0.87 * ψ
  rw [show q / (t : ℂ) - 1 = ((q - 1) + (1 - (t : ℂ))) / (t : ℂ) by field_simp; ring,
    norm_div, Complex.norm_of_nonneg ht.le]
  apply (div_le_iff₀ ht).mpr
  refine (norm_add_le _ _).trans ?_
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_nonneg.mpr ht')]
  change ‖q - 1‖ + (1 - t) ≤ 0.87 * ψ * t
  nlinarith [mul_nonneg hψ (sub_nonneg.mpr htlo)]

theorem norm_principalSqrt (z : ℂ) : ‖z.sqrt‖ = Real.sqrt ‖z‖ := by
  rw [← Real.sqrt_sq (norm_nonneg z.sqrt), ← norm_pow, principalSqrt_sq]

/-- Principal square-root multiplication for a positive-real-part saddle and a small
perturbation of its square. -/
theorem saddleCentral_sqrt_mul {s w : ℂ} {ψ : ℝ} (hs : 0 < s.re)
    (hs' : ‖s‖ ≤ 1.415 * s.re) (hψ : 0 ≤ ψ) (hψ' : ψ ≤ 0.3)
    (hw : ‖w‖ ≤ 1.34 * ψ) :
    (s ^ 2 * (1 + w)).sqrt = s * (1 + w).sqrt := by
  let q := (1 + w).sqrt
  let z := (s ^ 2 * (1 + w)).sqrt
  have hq : ‖q - 1‖ ≤ 0.76 * ψ := saddleCentral_sqrt_perturbation hψ hψ' hw
  have hbound : ‖s * (q - 1)‖ ≤ (1.415 * s.re) * (0.76 * 0.3) := by
    rw [norm_mul]
    refine mul_le_mul hs' (hq.trans ?_) (norm_nonneg _) (by positivity)
    linarith
  have he : 0 < (s * q).re := by
    have ha := (abs_le.mp (Complex.abs_re_le_norm (s * (q - 1)))).1
    have hb : (s * q).re = s.re + (s * (q - 1)).re := by
      rw [mul_sub, mul_one, Complex.sub_re]
      ring
    linarith
  have hz : 0 ≤ z.re := by
    dsimp only [z]
    rw [principalSqrt_re_eq]
    positivity
  have hsq : z ^ 2 = (s * q) ^ 2 := by
    dsimp only [z, q]
    rw [principalSqrt_sq, mul_pow, principalSqrt_sq]
  have hh : (z - s * q) * (z + s * q) = 0 := by
    calc _ = z ^ 2 - (s * q) ^ 2 := by ring
         _ = _ := sub_eq_zero.mpr hsq
  refine sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right ?_)
  intro hn
  have hn' := congrArg Complex.re hn
  simp only [Complex.add_re, Complex.zero_re] at hn'
  linarith

/-- The numerical Bessel-argument bounds following (33). -/
theorem saddleCentral_bessel_arguments {s w : ℂ} {ψ : ℝ} {v : ℝ} (hs : 0 < s.re)
    (hs' : ‖s‖ ≤ 1.4143 * s.re) (hψ : 0 ≤ ψ) (hψ' : ψ ≤ 0.3)
    (hw : ‖w‖ ≤ 1.34 * ψ) (hv : 0 < v) :
    let z := (2 * (v : ℂ)) * (s ^ 2 * (1 + w)).sqrt
    ‖z‖ ≤ 3.35 * (s.re * v) ∧ 1.35 * (s.re * v) ≤ z.re := by
  have hs'' : ‖s‖ ≤ 1.415 * s.re := by linarith
  let q := (1 + w).sqrt
  have hq : ‖q‖ ≤ 1.1841 := by
    have hw' : ‖w‖ ≤ 0.402 := by linarith
    change ‖(1 + w).sqrt‖ ≤ 1.1841
    rw [norm_principalSqrt]
    apply (Real.sqrt_le_left (by norm_num)).mpr
    have hb := norm_add_le (1 : ℂ) w
    norm_num at hb
    nlinarith
  have hd : ‖q - 1‖ ≤ 0.76 * ψ := saddleCentral_sqrt_perturbation hψ hψ' hw
  simp only [saddleCentral_sqrt_mul hs hs'' hψ hψ' hw]
  change ‖(2 * (v : ℂ)) * (s * q)‖ ≤ 3.35 * (s.re * v) ∧
    1.35 * (s.re * v) ≤ ((2 * (v : ℂ)) * (s * q)).re
  constructor
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_of_nonneg hv.le, Complex.norm_ofNat]
    have hh := mul_le_mul hs' hq (norm_nonneg q) (by positivity : 0 ≤ 1.4143 * s.re)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * v by positivity)
    nlinarith [mul_nonneg hs.le hv.le]
  · have hbound : ‖s * (q - 1)‖ ≤ (1.4143 * s.re) * (0.76 * 0.3) := by
      rw [norm_mul]
      refine mul_le_mul hs' (hd.trans ?_) (norm_nonneg _) (by positivity)
      linarith
    have ha := (abs_le.mp (Complex.abs_re_le_norm (s * (q - 1)))).1
    have he : (s * q).re = s.re + (s * (q - 1)).re := by
      rw [mul_sub, mul_one, Complex.sub_re]
      ring
    have hb : 0.675 * s.re ≤ (s * q).re := by linarith
    rw [show (2 * (v : ℂ)) = (((2 * v : ℝ)) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * v by positivity)
    linarith

/-- The exponent estimate in (33) from the two bounds on the phase before taking its root. -/
theorem saddleCentral_exponent_error {s g L : ℂ} {r ψ : ℝ} (hs : 0 < s.re)
    (hs' : ‖s‖ ≤ 1.415 * s.re) (hratio : r / (s.re * ‖s‖) ≤ 0.75)
    (hψ : 0 ≤ ψ) (hψ' : ψ ≤ 0.3) (hw : ‖g / s ^ 2 - 1‖ ≤ 1.34 * ψ)
    (hR : ‖g - s ^ 2 + L * (ψ : ℂ)‖ ≤ r * ψ ^ 2 / (1 - ψ)) :
    ‖2 * (g.sqrt - s) / (s.re : ℂ) + L * (ψ : ℂ) / ((s.re : ℂ) * s)‖ ≤ 2.46 * ψ ^ 2 := by
  have hs0 : s ≠ 0 := by intro hz; simp [hz] at hs
  have has : (s.re : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  let w := g / s ^ 2 - 1
  let q := (1 + w).sqrt
  have hge : g = s ^ 2 * (1 + w) := by
    dsimp only [w]
    field_simp
    ring
  have hroot : g.sqrt = s * q := by
    conv_lhs => rw [hge]
    exact saddleCentral_sqrt_mul hs hs' hψ hψ' hw
  have hq : ‖q - 1‖ ≤ 0.76 * ψ := saddleCentral_sqrt_perturbation hψ hψ' hw
  have hq2 : 2 * (q - 1) = w - (q - 1) ^ 2 := by
    have h := sqrt_one_add_remainder w
    change q - 1 - w / 2 = -(q - 1) ^ 2 / 2 at h
    linear_combination 2 * h
  have he :
      2 * (g.sqrt - s) / (s.re : ℂ) + L * (ψ : ℂ) / ((s.re : ℂ) * s) =
        (g - s ^ 2 + L * (ψ : ℂ)) / ((s.re : ℂ) * s) -
          (s / (s.re : ℂ)) * (q - 1) ^ 2 := by
    calc
      _ = (s / (s.re : ℂ)) * (2 * (q - 1)) + L * (ψ : ℂ) / ((s.re : ℂ) * s) := by
        rw [hroot]
        ring
      _ = _ := by
        rw [hq2]
        dsimp only [w]
        field_simp
        ring
  have hb₁ : ‖(g - s ^ 2 + L * (ψ : ℂ)) / ((s.re : ℂ) * s)‖ ≤
      (0.75 / 0.7 : ℝ) * ψ ^ 2 := by
    have hpa : 0 < s.re * ‖s‖ := mul_pos hs (norm_pos_iff.mpr hs0)
    have hp : (0.7 : ℝ) ≤ 1 - ψ := by linarith
    rw [norm_div, norm_mul, Complex.norm_of_nonneg hs.le]
    calc
      _ ≤ (r * ψ ^ 2 / (1 - ψ)) / (s.re * ‖s‖) :=
        div_le_div_of_nonneg_right hR hpa.le
      _ = (r / (s.re * ‖s‖)) * (ψ ^ 2 / (1 - ψ)) := by ring
      _ ≤ 0.75 * (ψ ^ 2 / 0.7) :=
        mul_le_mul hratio
          (div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hp) (by positivity) (by norm_num)
      _ = _ := by ring
  have hb₂ : ‖(s / (s.re : ℂ)) * (q - 1) ^ 2‖ ≤
      1.415 * (0.76 * ψ) ^ 2 := by
    rw [norm_mul, norm_div, Complex.norm_of_nonneg hs.le, norm_pow]
    exact mul_le_mul ((div_le_iff₀ hs).mpr hs') (pow_le_pow_left₀ (norm_nonneg _) hq 2)
      (sq_nonneg _) (by norm_num)
  rw [he]
  refine (norm_sub_le _ _).trans ((add_le_add hb₁ hb₂).trans ?_)
  nlinarith [sq_nonneg ψ]

end DurfeeCCS.Step08
