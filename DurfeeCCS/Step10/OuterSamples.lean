module

public import DurfeeCCS.Step10.OuterGeometryBounds
public import DurfeeCCS.Step10.OuterRho
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

@[expose] public noncomputable section

namespace DurfeeCCS.Step10

open Real Set

/-- The outer phase used to choose the first point of each sign. -/
def outerPhi (y h : ℝ) : ℝ := y * (outerRho h π).im + (outerRho h π).arg

/-- The first index from Corollary 4.4, expressed as a natural ceiling. -/
def outerFirst (n : ℕ) : ℕ := ⌈outerPhi (outerY n) (outerStart n) / π⌉₊

private theorem continuousOn_outerPhi (y : ℝ) :
    ContinuousOn (outerPhi y) (Ioi (0 : ℝ)) := by
  exact (Complex.continuous_im.comp_continuousOn continuousOn_outerRho_pi).const_mul y |>.add
    (Complex.continuousOn_arg.comp continuousOn_outerRho_pi (fun h hh =>
      Complex.mem_slitPlane_iff.mpr (.inl ((show 0 < h from hh).trans (outerRho_re_gt hh)))))

private theorem outerPhi_div_gap {y h : ℝ} (hy : 0 ≤ y) (hh : 0 < h) :
    0 < outerPhi y h / π - outerDelta y h ∧
    outerPhi y h / π - outerDelta y h ≤
      2 * π ^ 4 * y / (3 * h * sqrt (h ^ 2 + outerA) ^ 3) + 1 / h :=
  outerRho_phase_gap hy hh

private theorem le_outerFirst (n : ℕ) : outerPhi (outerY n) (outerStart n) / π ≤ outerFirst n :=
  Nat.le_ceil _

theorem outerFirst_bounds {n : ℕ} (hn : 6401 ≤ n) :
    0.92 * outerY n < outerFirst n ∧ outerFirst n < n.sqrt ∧
      (outerFirst n : ℝ) < outerDelta (outerY n) (outerStart n + 2) := by
  let y := outerY n
  let t := outerStart n
  have ht : 0 < t := lt_trans (by norm_num) (outerStart_gt hn)
  have hy : 0 < y := lt_trans (by norm_num) (eighty_lt_outerY hn)
  obtain ⟨hp, hq⟩ := outerPhi_div_gap hy.le ht
  have hδ := outerDelta_start_lower hn
  have hle := le_outerFirst n
  have hpos : 0 < outerPhi y t / π := by linarith only [hp, hδ, hy]
  have hceil : (outerFirst n : ℝ) < outerPhi y t / π + 1 := Nat.ceil_lt_add_one hpos.le
  have hstep := outerDelta_increment hn
  have hδend := outerDelta_end_lt_degree hn
  have htop : (outerFirst n : ℝ) < outerDelta y (t + 2) := by
    linarith only [hceil, hq, hstep]
  refine ⟨by linarith only [hδ, hp, hle], ?_, htop⟩
  have htop' : (outerFirst n : ℝ) < (n.sqrt : ℝ) := by linarith only [htop, hδend]
  exact_mod_cast htop'

theorem outerFirst_eq_intCeil {n : ℕ} (hn : 6401 ≤ n) :
    (outerFirst n : ℤ) = ⌈outerPhi (outerY n) (outerStart n) / π⌉ := by
  have hp := (outerFirst_bounds hn).1
  have hpos : 0 < outerPhi (outerY n) (outerStart n) / π := by
    have h := (outerPhi_div_gap (y := outerY n) (by unfold outerY; positivity)
      (lt_trans (by norm_num) (outerStart_gt hn))).1
    linarith [outerDelta_start_lower hn, eighty_lt_outerY hn]
  exact Int.natCast_ceil_eq_ceil hpos.le

def firstPhaseHit (f : ℝ → ℝ) (a b c : ℝ) : ℝ :=
  sInf (Icc a b ∩ f ⁻¹' {c})

theorem firstPhaseHit_spec {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (ha : f a ≤ c) (hb : c ≤ f b) :
    IsLeast (Icc a b ∩ f ⁻¹' {c}) (firstPhaseHit f a b c) := by
  obtain ⟨z, hz, hz'⟩ := intermediate_value_Icc hab hcont ⟨ha, hb⟩
  obtain ⟨C, hC, hset⟩ := continuousOn_iff_isClosed.mp hcont {c} isClosed_singleton
  have hcompact : IsCompact (Icc a b ∩ f ⁻¹' {c}) := by
    rw [inter_comm, hset, inter_comm]
    exact isCompact_Icc.inter_right hC
  obtain ⟨w, hw⟩ := hcompact.exists_isLeast ⟨z, hz, hz'⟩
  simpa only [firstPhaseHit, hw.csInf_eq] using hw

/-- Inside the overlap of the two outer estimates, take the first phase crossing.
Farther out, use the stationary point for the corresponding monomial. -/
def outerLogSample (n d : ℕ) : ℝ :=
  if farSample n d ≤ farThreshold n then
    firstPhaseHit (outerPhi (outerY n)) (outerStart n) (farSample n d) (π * (d : ℝ))
  else farSample n d

def outerSample (n d : ℕ) : ℝ := exp (outerLogSample n d)

theorem outerSample_pos (n d : ℕ) : 0 < outerSample n d := exp_pos _

theorem outerLogSample_far_lt {n d : ℕ} (hn : 6401 ≤ n)
    (hd : outerFirst n ≤ d) (hm : d < n.sqrt) : outerStart n < farSample n d := by
  have hy : 0 < outerY n := lt_trans (by norm_num) (eighty_lt_outerY hn)
  have ht : 0 < outerStart n := lt_trans (by norm_num) (outerStart_gt hn)
  have hle := (outerPhi_div_gap hy.le ht).1
  apply (strictMono_outerDelta hy).lt_iff_lt.mp
  rw [outerDelta_farSample hm]
  have hd' : (outerFirst n : ℝ) ≤ d := by exact_mod_cast hd
  linarith only [hle, le_outerFirst n, hd']

private theorem outerLogSample_near_spec {n d : ℕ} (hn : 6401 ≤ n)
    (hd : outerFirst n ≤ d) (hm : d < n.sqrt) (hs : farSample n d ≤ farThreshold n) :
    IsLeast (Icc (outerStart n) (farSample n d) ∩
      outerPhi (outerY n) ⁻¹' ({π * (d : ℝ)} : Set ℝ)) (outerLogSample n d) := by
  have hab := outerLogSample_far_lt hn hd hm
  have ht : 0 < outerStart n := lt_trans (by norm_num) (outerStart_gt hn)
  have hy : 0 < outerY n := lt_trans (by norm_num) (eighty_lt_outerY hn)
  have hc : ContinuousOn (outerPhi (outerY n)) (Icc (outerStart n) (farSample n d)) :=
    (continuousOn_outerPhi _).mono (fun h hh => ht.trans_le hh.1)
  have hle := (outerPhi_div_gap hy.le (ht.trans hab)).1
  rw [outerDelta_farSample hm] at hle
  have hge : outerPhi (outerY n) (outerStart n) / π ≤ d :=
    (le_outerFirst n).trans (by exact_mod_cast hd)
  have hπ := pi_pos
  rw [outerLogSample, ite_eq_left hs]
  apply firstPhaseHit_spec hab.le hc
  · simpa only [mul_comm π] using (div_le_iff₀ hπ).mp hge
  · simpa only [mul_comm π] using (lt_div_iff₀ hπ).mp (by linarith only [hle] :
      (d : ℝ) < outerPhi (outerY n) (farSample n d) / π) |>.le

theorem outerLogSample_near {n d : ℕ} (hn : 6401 ≤ n)
    (hd : outerFirst n ≤ d) (hm : d < n.sqrt) (hs : farSample n d ≤ farThreshold n) :
    outerLogSample n d ∈ Icc (outerStart n) (farSample n d) ∧
      outerPhi (outerY n) (outerLogSample n d) = π * d :=
  (outerLogSample_near_spec hn hd hm hs).1

theorem outerLogSample_far {n d : ℕ} (hs : farThreshold n < farSample n d) :
    outerLogSample n d = farSample n d := by simp only [outerLogSample, ite_eq_right hs.not_ge]

theorem outerFirst_sample {n : ℕ} (hn : 6401 ≤ n) :
    outerStart n ≤ log (outerSample n (outerFirst n)) ∧
      log (outerSample n (outerFirst n)) < outerStart n + 2 ∧
      outerPhi (outerY n) (log (outerSample n (outerFirst n))) = π * outerFirst n := by
  obtain ⟨_, hdm, hδ⟩ := outerFirst_bounds hn
  have hy := lt_trans (by norm_num : 0 < (80 : ℝ)) (eighty_lt_outerY hn)
  have hb : farSample n (outerFirst n) < outerStart n + 2 := by
    apply (strictMono_outerDelta hy).lt_iff_lt.mp
    rw [outerDelta_farSample hdm]
    exact hδ
  have h := outerLogSample_near hn le_rfl hdm
    (hb.trans (outerStart_add_two_lt_farThreshold hn)).le
  simpa only [outerSample, log_exp] using ⟨h.1.1, h.1.2.trans_lt hb, h.2⟩

theorem strictMonoOn_outerSample {n : ℕ} (hn : 6401 ≤ n) :
    StrictMonoOn (outerSample n) (Ico (outerFirst n) n.sqrt) := by
  intro i hi j hj hij
  obtain ⟨hi₁, hi₂⟩ := hi
  obtain ⟨hj₁, hj₂⟩ := hj
  have hf := strictMonoOn_farSample hn hi₂ hj₂ hij
  have ht := lt_trans (by norm_num : 0 < (8.76 : ℝ)) (outerStart_gt hn)
  apply exp_lt_exp.mpr
  by_cases h₂ : farSample n j ≤ farThreshold n
  · have h₁ := hf.le.trans h₂
    have hp := outerLogSample_near hn hi₁ hi₂ h₁
    have hq := outerLogSample_near hn hj₁ hj₂ h₂
    have hStart : outerPhi (outerY n) (outerStart n) ≤ π * (i : ℝ) := by
      have hh := (le_outerFirst n).trans (show (outerFirst n : ℝ) ≤ i by exact_mod_cast hi₁)
      simpa only [mul_comm π] using (div_le_iff₀ pi_pos).mp hh
    have hEnd : π * (i : ℝ) < outerPhi (outerY n) (outerLogSample n j) := by
      rw [hq.2]
      exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) pi_pos
    have hc : ContinuousOn (outerPhi (outerY n)) (Icc (outerStart n) (outerLogSample n j)) :=
      (continuousOn_outerPhi _).mono (fun x hx => ht.trans_le hx.1)
    obtain ⟨z, hz, hza⟩ := intermediate_value_Icc hq.1.1 hc ⟨hStart, hEnd.le⟩
    have hzlt : z < outerLogSample n j := lt_of_le_of_ne hz.2 (by
      intro he
      rw [he] at hza
      exact hEnd.ne' hza)
    by_contra! hnlt
    have hz' : z ∈ Icc (outerStart n) (farSample n i) ∩
        outerPhi (outerY n) ⁻¹' ({π * (i : ℝ)} : Set ℝ) :=
      ⟨⟨hz.1, hzlt.le.trans (hnlt.trans hp.1.2)⟩, hza⟩
    exact (not_lt_of_ge ((outerLogSample_near_spec hn hi₁ hi₂ h₁).2 hz')) (hzlt.trans_le hnlt)
  · have hfar := lt_of_not_ge h₂
    rw [outerLogSample_far hfar]
    by_cases h₁ : farSample n i ≤ farThreshold n
    · exact (outerLogSample_near hn hi₁ hi₂ h₁).1.2.trans_lt hf
    · rwa [outerLogSample_far (lt_of_not_ge h₁)]

end DurfeeCCS.Step10
