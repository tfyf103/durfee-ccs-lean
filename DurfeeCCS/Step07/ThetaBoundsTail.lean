module

public import DurfeeCCS.Step07.PowerDecay
public import DurfeeCCS.Step07.ThetaBounds
public meta import DurfeeCCS.Step07.ThetaBoundsIntervals
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-! The logarithmic tail of the page 31 bound, uniformly for `√n ≥ 80`. -/

@[expose] public noncomputable section

namespace DurfeeCCS.Step07

open Real

/-- The manuscript's upper bound for `a`, parametrized by `x = √n`. -/
def theta38Growth (x : ℝ) : ℝ := √((log x + 1) ^ 2 + 3.3)

private theorem log_eighty_lower : 3 < log (80 : ℝ) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  dyadic_interval [prec := 24]

private theorem log_eighty_upper : log (80 : ℝ) < 4.39 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  dyadic_interval [prec := 24]

private theorem theta38Growth_pos (x : ℝ) : 0 < theta38Growth x := by
  unfold theta38Growth
  exact Real.sqrt_pos_of_pos (by nlinarith [sq_nonneg (log x + 1)])

theorem theta38Growth_le {x : ℝ} (hx : 80 ≤ x) :
    theta38Growth x ≤ 5.76 * √(x / 80) := by
  let t := √(x / 80)
  have hy : 1 ≤ x / 80 := (le_div_iff₀ (by norm_num)).2 (by simpa using hx)
  have ht : 1 ≤ t := Real.le_sqrt_of_sq_le (by simpa using hy)
  have ht₀ : 0 < t := by linarith
  have ht₂ : t ^ 2 = x / 80 := Real.sq_sqrt (by linarith)
  have hxt : x = 80 * t ^ 2 := by rw [ht₂]; ring
  have hlog : log x = log 80 + 2 * log t := by
    rw [hxt, Real.log_mul (by norm_num) (pow_ne_zero _ ht₀.ne'), Real.log_pow]
    norm_num
  have hlog_le : log x + 1 ≤ (log 80 + 1) * t := by
    rw [hlog]
    have h₁ := Real.log_le_sub_one_of_pos ht₀
    have h₂ := mul_nonneg (show 0 ≤ log (80 : ℝ) + 1 - 2 by linarith [log_eighty_lower])
      (sub_nonneg.mpr ht)
    nlinarith
  have hlog₀ : 0 ≤ log x + 1 := by linarith [Real.log_nonneg (show 1 ≤ x by linarith)]
  have hbase : (log (80 : ℝ) + 1) ^ 2 + 3.3 ≤ (5.76 : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by linarith [log_eighty_lower] : 0 ≤ log (80 : ℝ) + 1)
      (show log (80 : ℝ) + 1 ≤ 4.39 + 1 by linarith [log_eighty_upper]) 2
    linarith
  apply Real.sqrt_le_iff.mpr
  change 0 ≤ 5.76 * t ∧ (log x + 1) ^ 2 + 3.3 ≤ (5.76 * t) ^ 2
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ((log 80 + 1) * t) ^ 2 + 3.3 * t ^ 2 := by
      gcongr
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ t + 1 by positivity)]
    _ = ((log 80 + 1) ^ 2 + 3.3) * t ^ 2 := by ring
    _ ≤ (5.76 : ℝ) ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right hbase (sq_nonneg _)
    _ = _ := by ring

def theta38TailB : ℝ := 80 * (1.48481 : ℝ) ^ 2 / 5.76

def theta38TailD : ℝ := 80 * 5.29406 * theta38Delta 5.29406 (π / 2)

private theorem theta38TailB_ge : 2 ≤ theta38TailB := by norm_num [theta38TailB]

private theorem theta38TailD_ge : 2 ≤ theta38TailD := by
  have hpi : π ∈ Set.Icc 3.1415926 3.1415927 :=
    ⟨Real.pi_gt_d20.le.trans' (by norm_num), Real.pi_lt_d20.le.trans (by norm_num)⟩
  unfold theta38TailD theta38Delta theta38Rho
  dyadic_interval [prec := 32]

/-- The high-radius error budget substitutes the two growing-scale terms from `E'_J`
into the common finite-row expression. The independent terms are left in the same normalization. -/
def theta38TailError (x : ℝ) : ℝ :=
  theta38Error 5 5.29406 5.76 1.48481 (π / 2) 1 0.547 +
    8 * (√(theta38Growth x * x) *
      (exp (-(1.48481 : ℝ) ^ 2 * x / theta38Growth x) + exp (-theta38TailD * (x / 80))) -
      √(80 * 5.76) * (exp (-theta38TailB) + exp (-theta38TailD)))

private theorem power_two_exp_decay {c t : ℝ} (hc : 2 ≤ c) (ht : 1 ≤ t) :
    t ^ 2 * exp (-c * t) ≤ exp (-c) := by
  have hm := power_mul_exp_antitoneOn (x₀ := 1) (b := 0) (a := c) 2 1
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by simpa using hc)
  simpa using hm (show (1 : ℝ) ∈ Set.Ici 1 from le_rfl) (show t ∈ Set.Ici 1 from ht) ht

theorem theta38_tail_error_lt {x : ℝ} (hx : 80 ≤ x) : theta38TailError x < 0.212 := by
  let t := √(x / 80)
  let B := theta38TailB
  let D := theta38TailD
  have hxt₀ : 0 ≤ x := by linarith
  have ht : 1 ≤ t := Real.le_sqrt_of_sq_le (by
    rw [one_pow, le_div_iff₀ (by norm_num), one_mul]
    exact hx)
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have ht₂ : t ^ 2 = x / 80 := Real.sq_sqrt (by positivity)
  have hxt : x = 80 * t ^ 2 := by rw [ht₂]; ring
  have ht_sq : t ≤ t ^ 2 := by nlinarith [mul_nonneg ht₀ (sub_nonneg.mpr ht)]
  have ha : theta38Growth x ≤ 5.76 * t := theta38Growth_le hx
  have ha₀ := theta38Growth_pos x
  have hB : 2 ≤ B := theta38TailB_ge
  have hD : 2 ≤ D := theta38TailD_ge
  have hbexp : B * t ≤ (1.48481 : ℝ) ^ 2 * x / theta38Growth x := by
    apply (le_div_iff₀ ha₀).2
    calc
      _ ≤ B * t * (5.76 * t) := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = _ := by rw [hxt]; dsimp only [B, theta38TailB]; ring
  have hdexp : D * t ≤ D * (x / 80) := by
    rw [← ht₂]
    exact mul_le_mul_of_nonneg_left ht_sq (by linarith)
  have hroot : √(theta38Growth x * x) ≤ √(80 * 5.76) * t ^ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (80 * 5.76 : ℝ))]
    calc
      _ ≤ (5.76 * t) * x := mul_le_mul_of_nonneg_right ha hxt₀
      _ = (80 * 5.76 : ℝ) * (t * t ^ 2) := by rw [hxt]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [pow_two (t ^ 2)]
        exact mul_le_mul_of_nonneg_right ht_sq (sq_nonneg t)
  have hbig :
      √(theta38Growth x * x) *
        (exp (-(1.48481 : ℝ) ^ 2 * x / theta38Growth x) + exp (-D * (x / 80))) ≤
        √(80 * 5.76) * (exp (-B) + exp (-D)) := by
    calc
      _ ≤ (√(80 * 5.76) * t ^ 2) * (exp (-B * t) + exp (-D * t)) := by
        apply mul_le_mul hroot _ (by positivity) (by positivity)
        refine add_le_add (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_)
        · simpa only [neg_mul, neg_div] using neg_le_neg hbexp
        · simpa only [neg_mul] using neg_le_neg hdexp
      _ = √(80 * 5.76) * (t ^ 2 * exp (-B * t) + t ^ 2 * exp (-D * t)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (power_two_exp_decay hB ht) (power_two_exp_decay hD ht)) (Real.sqrt_nonneg _)
  unfold theta38TailError
  exact (by linarith [hbig] : _ ≤ theta38Error 5 5.29406 5.76 1.48481 (π / 2) 1 0.547)
    |>.trans_lt theta38_error_tail_upper

end DurfeeCCS.Step07
