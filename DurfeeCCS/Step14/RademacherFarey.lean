module

public import DurfeeCCS.Step06.RademacherExactArc

/-! Farey mediants and normalized Ford chords in Rademacher's argument.
The determinant convention is qb - as = 1 for neighbors a/q < b/s. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step14

open Complex Set DurfeeCCS.Step06

/-- An intermediate fraction between two unimodular neighbors has denominator
at least the sum of their denominators. -/
theorem farey_denominator_add_le {a q b s c t : ℤ}
    (hq : 0 < q) (hs : 0 < s) (ht : 0 < t) (hdet : q * b - a * s = 1)
    (hl : (a : ℝ) / q < (c : ℝ) / t) (hr : (c : ℝ) / t < (b : ℝ) / s) :
    q + s ≤ t := by
  have hqc : (0 : ℝ) < q := by exact_mod_cast hq
  have hsc : (0 : ℝ) < s := by exact_mod_cast hs
  have htc : (0 : ℝ) < t := by exact_mod_cast ht
  have hl' : (0 : ℤ) < q * c - a * t := by
    exact_mod_cast (show (0 : ℝ) < (q : ℝ) * c - a * t by
      linarith only [(div_lt_div_iff₀ hqc htc).mp hl])
  have hr' : (0 : ℤ) < b * t - s * c := by
    exact_mod_cast (show (0 : ℝ) < (b : ℝ) * t - s * c by
      linarith only [(div_lt_div_iff₀ htc hsc).mp hr])
  calc
    q + s ≤ q * (b * t - s * c) + s * (q * c - a * t) := by
      simpa only [mul_one] using add_le_add
        (mul_le_mul_of_nonneg_left (show 1 ≤ b * t - s * c by omega) hq.le)
        (mul_le_mul_of_nonneg_left (show 1 ≤ q * c - a * t by omega) hs.le)
    _ = t := by linear_combination t * hdet

/-- The two distances from a mediant to its neighbors. -/
theorem farey_mediant_distances {a q b s : ℤ} (hq : 0 < q) (hs : 0 < s)
    (hdet : q * b - a * s = 1) :
    let m := ((a : ℝ) + b) / ((q : ℝ) + s)
    m - (a : ℝ) / q = 1 / ((q : ℝ) * (q + s)) ∧
      (b : ℝ) / s - m = 1 / ((s : ℝ) * (q + s)) := by
  have hqc : (0 : ℝ) < q := by exact_mod_cast hq
  have hsc : (0 : ℝ) < s := by exact_mod_cast hs
  have hdetc : (q : ℝ) * b - a * s = 1 := by exact_mod_cast hdet
  dsimp only
  constructor <;> field_simp [hqc.ne', hsc.ne', (add_pos hqc hsc).ne']
    <;> linarith only [hdetc]

/-- The horizontal mediant widths are bounded by the reciprocal of N times the
denominator at the corresponding endpoint. -/
theorem farey_mediant_width_lt {N a q b s : ℤ} (hN : 0 < N) (hq : 0 < q) (hs : 0 < s)
    (hdet : q * b - a * s = 1) (horder : N < q + s) :
    let m := ((a : ℝ) + b) / ((q : ℝ) + s)
    m - (a : ℝ) / q < 1 / ((q : ℝ) * N) ∧
      (b : ℝ) / s - m < 1 / ((s : ℝ) * N) := by
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hqc : (0 : ℝ) < q := by exact_mod_cast hq
  have hsc : (0 : ℝ) < s := by exact_mod_cast hs
  have horderc : (N : ℝ) < (q : ℝ) + (s : ℝ) := by exact_mod_cast horder
  obtain ⟨hl, hr⟩ := farey_mediant_distances hq hs hdet
  dsimp only at hl hr ⊢
  rw [hl, hr]
  exact ⟨one_div_lt_one_div_of_lt (mul_pos hqc hNc) (mul_lt_mul_of_pos_left horderc hqc),
    one_div_lt_one_div_of_lt (mul_pos hsc hNc) (mul_lt_mul_of_pos_left horderc hsc)⟩

/-- Every point of the unit interval belongs to a bracketing pair of Farey
neighbors at order N. By the denominator obstruction, there is no fraction of
denominator at most N in the open bracket. -/
theorem exists_farey_bracket {N : ℤ} (hN : 1 ≤ N) {x : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    ∃ a q b s : ℤ,
      0 < q ∧ q ≤ N ∧ 0 < s ∧ s ≤ N ∧ 0 ≤ a ∧ a ≤ q ∧ 0 ≤ b ∧ b ≤ s ∧
      q * b - a * s = 1 ∧ N < q + s ∧ (a : ℝ) / q ≤ x ∧ x ≤ (b : ℝ) / s := by
  let goal := ∃ a q b s : ℤ,
    0 < q ∧ q ≤ N ∧ 0 < s ∧ s ≤ N ∧ 0 ≤ a ∧ a ≤ q ∧ 0 ≤ b ∧ b ≤ s ∧
    q * b - a * s = 1 ∧ N < q + s ∧ (a : ℝ) / q ≤ x ∧ x ≤ (b : ℝ) / s
  have refineBracket (d : ℕ) :
      ∀ a q b s : ℤ, 0 < q → q ≤ N → 0 < s → s ≤ N → 0 ≤ a → a ≤ q →
        0 ≤ b → b ≤ s → q * b - a * s = 1 →
        (a : ℝ) / q ≤ x → x ≤ (b : ℝ) / s → (2 * N - q - s).toNat = d → goal := by
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro a q b s hq hqN hs hsN ha haq hb hbs hdet hl hr hmeasure
      by_cases hsum : N < q + s
      · exact ⟨a, q, b, s, hq, hqN, hs, hsN, ha, haq, hb, hbs, hdet, hsum, hl, hr⟩
      · have hsum' : q + s ≤ N := by omega
        have hpos : 0 < q + s := by omega
        have hab : 0 ≤ a + b := by omega
        have hab' : a + b ≤ q + s := by omega
        have hcast : (((a + b : ℤ) : ℝ) / ((q + s : ℤ) : ℝ)) =
            ((a : ℝ) + b) / ((q : ℝ) + s) := by push_cast; rfl
        by_cases hm : x ≤ ((a : ℝ) + b) / ((q : ℝ) + s)
        · have hd : (2 * N - q - (q + s)).toNat < d := by omega
          exact ih _ hd a q (a + b) (q + s) hq hqN hpos hsum' ha haq hab hab'
            (by linear_combination hdet) hl (by simpa only [hcast] using hm) rfl
        · have hd : (2 * N - (q + s) - s).toNat < d := by omega
          exact ih _ hd (a + b) (q + s) b s hpos hsum' hs hsN hab hab' hb hbs
            (by linear_combination hdet) (by simpa only [hcast] using (le_of_not_ge hm)) hr rfl
  exact refineBracket _ 0 1 1 1 (by decide) hN (by decide) hN (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simpa using hx₀) (by simpa using hx₁) rfl

/-- A normalized Ford endpoint. A positive signed denominator is the endpoint
coming from the previous fraction. -/
def fordEndpoint (k d : ℝ) : ℂ :=
  (k ^ 2 / (k ^ 2 + d ^ 2) : ℝ) + (k * d / (k ^ 2 + d ^ 2) : ℝ) * I

@[simp] theorem fordEndpoint_re (k d : ℝ) :
    (fordEndpoint k d).re = k ^ 2 / (k ^ 2 + d ^ 2) := by
  simp only [fordEndpoint, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

@[simp] theorem fordEndpoint_im (k d : ℝ) :
    (fordEndpoint k d).im = k * d / (k ^ 2 + d ^ 2) := by
  simp only [fordEndpoint, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

private theorem fordEndpoint_normSq_eq_re {k : ℝ} (hk : 0 < k) (d : ℝ) :
    normSq (fordEndpoint k d) = (fordEndpoint k d).re := by
  simp only [normSq_apply, fordEndpoint_re, fordEndpoint_im]
  field_simp [show k ^ 2 + d ^ 2 ≠ 0 by positivity]

/-- Inverting the normalized Ford endpoint gives the vertical line with real
part 1 and ordinate minus the signed denominator ratio. -/
theorem fordEndpoint_inv {k : ℝ} (hk : 0 < k) (d : ℝ) :
    (fordEndpoint k d)⁻¹ = 1 - ((d / k : ℝ) : ℂ) * I := by
  have hsum : k ^ 2 + d ^ 2 ≠ 0 := by positivity
  apply Complex.ext
  · have h : 0 < (fordEndpoint k d).re := by rw [fordEndpoint_re]; positivity
    rw [Complex.inv_re, fordEndpoint_normSq_eq_re hk, div_self h.ne']
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
  · simp only [Complex.inv_im, fordEndpoint_normSq_eq_re hk, fordEndpoint_re, fordEndpoint_im,
      Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_sub]
    field_simp [hsum, hk.ne']

/-- The Ford circle touching the real axis at a/q has this center. -/
def fordCenter (a q : ℤ) : ℂ :=
  ((a : ℝ) / q : ℝ) + (1 / (2 * (q : ℝ) ^ 2) : ℝ) * I

/-- The common contact point for a/q and b/s in the original coordinate. -/
def fordContact (a q b s : ℤ) : ℂ :=
  (((a : ℝ) * q + (b : ℝ) * s) / ((q : ℝ) ^ 2 + (s : ℝ) ^ 2) : ℝ) +
    (1 / ((q : ℝ) ^ 2 + (s : ℝ) ^ 2) : ℝ) * I

private theorem fordContact_re (a q b s : ℤ) :
    (fordContact a q b s).re = ((a : ℝ) * q + (b : ℝ) * s) / ((q : ℝ) ^ 2 + (s : ℝ) ^ 2) := by
  simp only [fordContact, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

private theorem fordContact_im (a q b s : ℤ) :
    (fordContact a q b s).im = 1 / ((q : ℝ) ^ 2 + (s : ℝ) ^ 2) := by
  simp only [fordContact, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

private theorem normalizedFord_re (q : ℤ) (z : ℂ) :
    (-I * (q : ℂ) ^ 2 * z).re = (q : ℝ) ^ 2 * z.im := by
  rw [← Complex.ofReal_intCast, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    zero_add, neg_mul, zero_sub, neg_neg, one_mul]

private theorem normalizedFord_im (q : ℤ) (z : ℂ) :
    (-I * (q : ℂ) ^ 2 * z).im = -(q : ℝ) ^ 2 * z.re := by
  rw [← Complex.ofReal_intCast, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    zero_add, neg_mul, one_mul]

private theorem fordContact_normalized {a q b s : ℤ}
    (hq : 0 < q) (hs : 0 < s) (hdet : q * b - a * s = 1) :
    -I * (q : ℂ) ^ 2 * (fordContact a q b s - (((a : ℝ) / q : ℝ) : ℂ)) =
      fordEndpoint q (-s : ℝ) ∧
    -I * (s : ℂ) ^ 2 * (fordContact a q b s - (((b : ℝ) / s : ℝ) : ℂ)) =
      fordEndpoint s q := by
  have hqc : (0 : ℝ) < q := by exact_mod_cast hq
  have hsc : (0 : ℝ) < s := by exact_mod_cast hs
  have hdetc : (q : ℝ) * b - a * s = 1 := by exact_mod_cast hdet
  have hsum : (q : ℝ) ^ 2 + (s : ℝ) ^ 2 ≠ 0 := by positivity
  have hl : (fordContact a q b s).re - (a : ℝ) / q =
      s / (q * ((q : ℝ) ^ 2 + (s : ℝ) ^ 2)) := by
    rw [fordContact_re]
    field_simp [hqc.ne', hsum]
    linear_combination (s : ℝ) * hdetc
  have hr : (fordContact a q b s).re - (b : ℝ) / s =
      -q / (s * ((q : ℝ) ^ 2 + (s : ℝ) ^ 2)) := by
    rw [fordContact_re]
    field_simp [hsc.ne', hsum]
    linear_combination -(q : ℝ) * hdetc
  constructor <;> apply Complex.ext <;>
    simp only [normalizedFord_re, normalizedFord_im, fordEndpoint_re, fordEndpoint_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, hl, hr,
      fordContact_im, neg_sq, add_comm ((s : ℝ) ^ 2) ((q : ℝ) ^ 2)]
  · ring
  · field_simp [hqc.ne', hsum]
  · ring
  · field_simp [hsc.ne', hsum]

private theorem normSq_sub_half (z : ℂ) :
    normSq (z - (1 / 2 : ℝ)) = normSq z - z.re + 1 / 4 := by
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero]
  ring

theorem fordEndpoint_on_circle {k : ℝ} (hk : 0 < k) (d : ℝ) :
    ‖fordEndpoint k d - (1 / 2 : ℝ)‖ = 1 / 2 := by
  have h : ‖fordEndpoint k d - (1 / 2 : ℝ)‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, normSq_sub_half, fordEndpoint_normSq_eq_re hk d]
    norm_num
  nlinarith only [h, norm_nonneg (fordEndpoint k d - (1 / 2 : ℝ))]

private theorem fordContact_distance {a q : ℤ} {z : ℂ} {d : ℝ} (hq : 0 < q)
    (ht : -I * (q : ℂ) ^ 2 * (z - (((a : ℝ) / q : ℝ) : ℂ)) = fordEndpoint q d) :
    ‖z - fordCenter a q‖ = 1 / (2 * (q : ℝ) ^ 2) := by
  have hqc : (0 : ℝ) < q := by exact_mod_cast hq
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have h : -I * (q : ℂ) ^ 2 * (z - fordCenter a q) = fordEndpoint q d - (1 / 2 : ℝ) := by
    rw [← ht, fordCenter]
    push_cast
    field_simp [hq']
    ring_nf
    simp [Complex.I_sq]
    ring
  have hn := congrArg norm h
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_pow,
    fordEndpoint_on_circle hqc d] at hn
  have hnorm : ‖(q : ℂ)‖ = (q : ℝ) := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqc]
  rw [hnorm] at hn
  apply (eq_div_iff (by positivity)).mpr
  nlinarith only [hn]

/-- The two normalized images of an actual tangency point, with incidences on
the original Ford circles. -/
theorem fordContact_geometry {a q b s : ℤ}
    (hq : 0 < q) (hs : 0 < s) (hdet : q * b - a * s = 1) :
    let z := fordContact a q b s;
    -I * (q : ℂ) ^ 2 * (z - (((a : ℝ) / q : ℝ) : ℂ)) = fordEndpoint q (-s : ℝ) ∧
    -I * (s : ℂ) ^ 2 * (z - (((b : ℝ) / s : ℝ) : ℂ)) = fordEndpoint s q ∧
    ‖z - fordCenter a q‖ = 1 / (2 * (q : ℝ) ^ 2) ∧
    ‖z - fordCenter b s‖ = 1 / (2 * (s : ℝ) ^ 2) := by
  obtain ⟨hl, hr⟩ := fordContact_normalized hq hs hdet
  exact ⟨hl, hr, fordContact_distance hq hl, fordContact_distance hs hr⟩

/-- Endpoint modulus bound at Farey order N, with either sign of d. -/
theorem fordEndpoint_norm_lt {N k d : ℝ} (hN : 0 < N) (hk : 0 < k)
    (hd : N < k + |d|) : ‖fordEndpoint k d‖ < Real.sqrt 2 * k / N := by
  have hsq : N ^ 2 < 2 * (k ^ 2 + d ^ 2) := by
    have hsum : N ^ 2 < (k + |d|) ^ 2 := by
      nlinarith only [hN, hd, mul_pos hN (sub_pos.mpr hd), sq_nonneg (k + |d| - N)]
    nlinarith only [hsum, sq_abs d, sq_nonneg (k - |d|)]
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [Complex.sq_norm, fordEndpoint_normSq_eq_re hk, fordEndpoint_re, div_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_lt_mul_of_pos_left hsq (sq_pos_of_pos hk)]

/-- Positivity, inverse-coordinate bound, and uniform modulus and length bounds
for the Ford chord. The denominator sums are the Farey conditions at order N. -/
theorem fordChord_bounds {N k p q : ℝ} (hN : 0 < N) (hk : 0 < k)
    (hp : 0 < p) (hq : 0 < q) (hkp : N < k + p) (hkq : N < k + q) :
    let z₁ := fordEndpoint k p
    let z₂ := fordEndpoint k (-q)
    (∀ z ∈ segment ℝ z₁ z₂,
      0 < z.re ∧ z.re ≤ 1 ∧ 1 ≤ (z⁻¹).re ∧ ‖z‖ < Real.sqrt 2 * k / N) ∧
    dist z₁ z₂ < 2 * (Real.sqrt 2 * k / N) := by
  dsimp only
  let z₁ := fordEndpoint k p
  let z₂ := fordEndpoint k (-q)
  let R := Real.sqrt 2 * k / N
  have h₁ : ‖z₁‖ < R :=
    fordEndpoint_norm_lt hN hk (by simpa only [abs_of_pos hp] using hkp)
  have h₂ : ‖z₂‖ < R :=
    fordEndpoint_norm_lt hN hk (by simpa only [abs_neg, abs_of_pos hq] using hkq)
  have h₁re : 0 < z₁.re := by dsimp only [z₁]; rw [fordEndpoint_re]; positivity
  have h₂re : 0 < z₂.re := by dsimp only [z₂]; rw [fordEndpoint_re]; positivity
  have hclosed : segment ℝ z₁ z₂ ⊆ Metric.closedBall ((1 / 2 : ℝ) : ℂ) (1 / 2) :=
    (convex_closedBall _ _).segment_subset
      (by rw [Metric.mem_closedBall, dist_eq_norm]; exact (fordEndpoint_on_circle hk p).le)
      (by rw [Metric.mem_closedBall, dist_eq_norm]; exact (fordEndpoint_on_circle hk (-q)).le)
  have hopen : segment ℝ z₁ z₂ ⊆ Metric.ball (0 : ℂ) R :=
    (convex_ball _ _).segment_subset (by simpa [Metric.mem_ball] using h₁)
      (by simpa [Metric.mem_ball] using h₂)
  refine ⟨fun z hz => ?_, ?_⟩
  · have hre : 0 < z.re := by
      obtain ⟨a, b, ha, hb, hab, hz'⟩ := hz
      rw [← hz']
      simp only [Complex.add_re, Complex.smul_re]
      change 0 < a * z₁.re + b * z₂.re
      by_cases ha₀ : a = 0
      · have hb₁ : b = 1 := by linarith
        simpa only [ha₀, hb₁, zero_mul, one_mul, zero_add] using h₂re
      · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha₀)) h₁re)
          (mul_nonneg hb h₂re.le)
    have hnsq : normSq z ≤ z.re := by
      have hc := hclosed hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hc
      have hs := pow_le_pow_left₀ (norm_nonneg _) hc 2
      rw [Complex.sq_norm, normSq_sub_half] at hs
      linarith
    have hre₁ : z.re ≤ 1 := by
      have hs : z.re ^ 2 ≤ z.re := by
        rw [Complex.normSq_apply] at hnsq
        nlinarith only [hnsq, sq_nonneg z.im]
      by_contra! h
      nlinarith only [hs, mul_pos hre (sub_pos.mpr h)]
    have hz₀ : z ≠ 0 := by intro e; simp [e] at hre
    have hinv : 1 ≤ (z⁻¹).re := by
      rw [Complex.inv_re, le_div_iff₀ (Complex.normSq_pos.mpr hz₀), one_mul]
      exact hnsq
    exact ⟨hre, hre₁, hinv, by simpa [Metric.mem_ball] using hopen hz⟩
  · rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans_lt (by linarith)

end DurfeeCCS.Step14
