module

public import DurfeeCCS.Step12.Mode
public import DurfeeCCS.Step12.Probability

/-! # The mode bound for the uniform Durfee side -/

public section

namespace DurfeeCCS

/-- Every mode of the uniform Durfee side is at distance strictly less than one
from its expectation. The mode is allowed to range over all natural numbers. -/
theorem durfee_all_modes_near_mean {n d : ℕ} (hn : 1 ≤ n)
    (hmode : ∀ j, durfeeMass n j ≤ durfeeMass n d) :
    |(d : ℝ) - durfeeMean n| < 1 := by
  have hcount (j : ℕ) : p n j ≤ p n d := by
    have hj := hmode j
    unfold durfeeMass at hj
    exact_mod_cast (div_le_div_iff_of_pos_right (durfeePolynomialReal_eval_one_pos n)).mp hj
  have hdpos : 0 < p n d := by
    have hp1 : 0 < p n 1 := by rw [p_one]; omega
    exact hp1.trans_le (hcount 1)
  have hd : 1 ≤ d := by
    by_contra! h
    have hd0 : d = 0 := by omega
    rw [hd0, p_zero_of_pos hn] at hdpos
    omega
  have htop : d ≤ n.sqrt := by
    by_contra! h
    rw [p_eq_zero_of_sq_gt (Nat.sqrt_lt.mp h)] at hdpos
    omega
  obtain ⟨r, hr, hfac⟩ := durfee_factorization n hn
  rw [(durfeeSide_moments_of_factorization r hr hfac).1]
  exact durfee_all_modes_near_rootMean_of_factorization hn hr hfac
    (fun j _ _ => hcount j) hd htop

/-- The mode bound in the manuscript, valid for every mode of the Durfee distribution. -/
theorem durfee_all_modes_within_one {n d : ℕ} (hn : 1 ≤ n)
    (hmode : ∀ j, durfeeMass n j ≤ durfeeMass n d) :
    |(d : ℝ) - durfeeMean n| ≤ 1 :=
  (durfee_all_modes_near_mean hn hmode).le

end DurfeeCCS
