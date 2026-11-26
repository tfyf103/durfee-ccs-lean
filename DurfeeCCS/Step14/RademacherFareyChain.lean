module

public import DurfeeCCS.Step14.RademacherFarey
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! Enumerate the Farey fractions in the unit interval and verify all adjacent pairs. -/

@[expose] public noncomputable section
namespace DurfeeCCS.Step14

open Finset

private theorem rat_num_den_of_reduced {a : ℤ} {q : ℕ} (hq : 0 < q)
    (hred : a.natAbs.Coprime q) :
    ((a : ℚ) / (q : ℚ)).num = a ∧ ((a : ℚ) / (q : ℚ)).den = q := by
  let r : ℚ := ⟨a, q, hq.ne', hred⟩
  have h := r.num_div_den
  change (a : ℚ) / (q : ℚ) = r at h
  exact ⟨congrArg Rat.num h, congrArg Rat.den h⟩

/-- The finite set of reduced fractions in `[0,1]` with denominator at most `N`. -/
def fareyVertexSet (N : ℕ) : Finset ℚ :=
  (((Icc (0 : ℤ) (N : ℤ)).product (Icc (1 : ℕ) N)).filter
    (fun ab : ℤ × ℕ => ab.1 ≤ (ab.2 : ℤ) ∧ ab.1.natAbs.Coprime ab.2)).image
      (fun ab : ℤ × ℕ => (ab.1 : ℚ) / (ab.2 : ℚ))

@[simp] theorem mem_fareyVertexSet {N : ℕ} {r : ℚ} :
    r ∈ fareyVertexSet N ↔ 0 ≤ r ∧ r ≤ 1 ∧ r.den ≤ N := by
  constructor
  · intro hr
    obtain ⟨⟨a, q⟩, hpair, rfl⟩ := mem_image.mp hr
    obtain ⟨hbox, haq, hcop⟩ := mem_filter.mp hpair
    obtain ⟨ha, hq⟩ := mem_product.mp hbox
    have hq' : 0 < q := (mem_Icc.mp hq).1
    have hqRat : (0 : ℚ) < q := by exact_mod_cast hq'
    have haRat : (0 : ℚ) ≤ a := by exact_mod_cast (mem_Icc.mp ha).1
    have hleRat : (a : ℚ) ≤ q := by exact_mod_cast haq
    obtain ⟨_, hd⟩ := rat_num_den_of_reduced hq' hcop
    exact ⟨div_nonneg haRat hqRat.le, (div_le_one hqRat).mpr hleRat,
      by change ((a : ℚ) / (q : ℚ)).den ≤ N; rw [hd]; exact (mem_Icc.mp hq).2⟩
  · rintro ⟨h₀, h₁, hN⟩
    have hnum₀ : 0 ≤ r.num := Rat.num_nonneg.mpr h₀
    have hqRat : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
    have hnum : r.num ≤ (r.den : ℤ) := by
      rw [← r.num_div_den] at h₁
      exact_mod_cast (div_le_one hqRat).mp h₁
    apply mem_image.mpr
    refine ⟨(r.num, r.den), mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, hnum, r.reduced⟩,
      r.num_div_den⟩
    · exact mem_Icc.mpr ⟨hnum₀, hnum.trans (by exact_mod_cast hN)⟩
    · exact mem_Icc.mpr ⟨r.den_pos, hN⟩

/-- The complete increasing Farey chain of order `N`. -/
def fareyChain (N : ℕ) : List ℚ := (fareyVertexSet N).sort

@[simp] theorem mem_fareyChain {N : ℕ} {r : ℚ} :
    r ∈ fareyChain N ↔ 0 ≤ r ∧ r ≤ 1 ∧ r.den ≤ N := by
  simp [fareyChain]

@[simp] theorem fareyChain_toFinset (N : ℕ) : (fareyChain N).toFinset = fareyVertexSet N := by
  simp [fareyChain]

theorem fareyChain_sortedLT (N : ℕ) : (fareyChain N).SortedLT :=
  (fareyVertexSet N).sortedLT_sort

theorem fareyChain_nodup (N : ℕ) : (fareyChain N).Nodup := by
  simp [fareyChain]

theorem fareyChain_pos {N : ℕ} (hN : 0 < N) : 0 < (fareyChain N).length := by
  have h0 : (0 : ℚ) ∈ fareyChain N := by simp; omega
  exact List.length_pos_of_mem h0

theorem fareyChain_one_lt_length {N : ℕ} (hN : 0 < N) : 1 < (fareyChain N).length := by
  have hsub : ({0, 1} : Finset ℚ) ⊆ fareyVertexSet N := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp <;> omega
  have hcard := card_le_card hsub
  norm_num at hcard
  simp only [fareyChain, length_sort]
  exact Nat.lt_of_succ_le hcard

theorem fareyChain_first {N : ℕ} (hN : 0 < N) :
    (fareyChain N)[0]'(fareyChain_pos hN) = 0 := by
  have h : 0 < (fareyVertexSet N).sort.length := by simpa only [fareyChain] using fareyChain_pos hN
  have hm := Finset.sorted_zero_eq_min' (s := fareyVertexSet N) (h := h)
  refine hm.trans ?_
  exact le_antisymm (min'_le _ _ (by simp; omega)) (mem_fareyVertexSet.mp (min'_mem _ _)).1

theorem fareyChain_last {N : ℕ} (hN : 0 < N) :
    (fareyChain N)[(fareyChain N).length - 1]'(by have := fareyChain_pos hN; omega) = 1 := by
  have hp : 0 < (fareyVertexSet N).sort.length := by simpa only [fareyChain] using fareyChain_pos hN
  have h : (fareyVertexSet N).sort.length - 1 < (fareyVertexSet N).sort.length := by omega
  have hm := Finset.sorted_last_eq_max' (s := fareyVertexSet N) (h := h)
  refine hm.trans ?_
  exact le_antisymm (mem_fareyVertexSet.mp (max'_mem _ _)).2.1 (le_max' _ _ (by simp; omega))

private theorem coprime_of_int_linear_combination {a q c d : ℤ}
    (h : c * a + d * q = 1) : a.natAbs.Coprime q.natAbs := by
  let g := Nat.gcd a.natAbs q.natAbs
  have ha : (g : ℤ) ∣ a := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hq : (g : ℤ) ∣ q := Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  have hg : (g : ℤ) ∣ (1 : ℤ) := h ▸ dvd_add (dvd_mul_of_dvd_right ha _) (dvd_mul_of_dvd_right hq _)
  exact Nat.dvd_one.mp (by simpa using Int.natCast_dvd.mp hg)

private theorem rat_cast_as_div (r : ℚ) : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
  exact_mod_cast r.num_div_den.symm

private theorem no_between_fareyChain {N i : ℕ} (hi : i + 1 < (fareyChain N).length)
    {x : ℚ} (hx : x ∈ fareyChain N) (hl : (fareyChain N)[i]'(by omega) < x)
    (hr : x < (fareyChain N)[i + 1]) : False := by
  let L := fareyChain N
  have hm := (fareyChain_sortedLT N).strictMono_get
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
  rw [← hj] at hl hr
  have hli : i < L.length := by dsimp only [L]; omega
  have hlj : (⟨i, hli⟩ : Fin L.length) < j := hm.lt_iff_lt.mp hl
  have hrj : j < (⟨i + 1, hi⟩ : Fin L.length) := hm.lt_iff_lt.mp hr
  change i < j.val at hlj
  change j.val < i + 1 at hrj
  omega

/-- Each adjacent pair in the complete chain has determinant one and denominator sum greater
than `N`. The chain contains all reduced fractions, so this is the actual adjacency condition. -/
theorem fareyChain_adjacent {N i : ℕ} (hN : 0 < N) (hi : i + 1 < (fareyChain N).length) :
    let r := (fareyChain N)[i]'(by omega)
    let s := (fareyChain N)[i + 1]
    ((r.den : ℤ) * s.num - r.num * (s.den : ℤ) = 1) ∧ N < r.den + s.den := by
  let r := (fareyChain N)[i]'(by omega)
  let s := (fareyChain N)[i + 1]
  have hri : r ∈ fareyChain N := List.getElem_mem _
  have hsi : s ∈ fareyChain N := List.getElem_mem _
  have ⟨hr₀, hr₁, hrN⟩ := mem_fareyChain.mp hri
  have ⟨hs₀, hs₁, hsN⟩ := mem_fareyChain.mp hsi
  have hrs : r < s := (fareyChain_sortedLT N).getElem_lt_getElem_of_lt (by omega)
  have hrsR : (r : ℝ) < (s : ℝ) := by exact_mod_cast hrs
  let x := ((r : ℝ) + (s : ℝ)) / 2
  have hrx : (r : ℝ) < x := by dsimp [x]; linarith only [hrsR]
  have hxs : x < (s : ℝ) := by dsimp [x]; linarith only [hrsR]
  have hx₀ : 0 ≤ x := hrx.le.trans' (by exact_mod_cast hr₀)
  have hx₁ : x ≤ 1 := hxs.le.trans (by exact_mod_cast hs₁)
  obtain ⟨a, q, b, t, hq, hqN, ht, htN, ha, haq, hb, hbt, hdet, hsum, hl, hh⟩ :=
    exists_farey_bracket (N := (N : ℤ)) (by exact_mod_cast hN) hx₀ hx₁
  let u : ℚ := (a : ℚ) / (q.toNat : ℚ)
  let v : ℚ := (b : ℚ) / (t.toNat : ℚ)
  have hqC : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq.le
  have htC : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht.le
  have hure : (u : ℝ) = (a : ℝ) / (q : ℝ) := by
    simp only [u, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    exact congrArg (fun d : ℝ => (a : ℝ) / d) (by exact_mod_cast hqC)
  have hvre : (v : ℝ) = (b : ℝ) / (t : ℝ) := by
    simp only [v, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    exact congrArg (fun d : ℝ => (b : ℝ) / d) (by exact_mod_cast htC)
  have hqAbs : q.natAbs = q.toNat := by
    simpa only [Int.natAbs_natCast] using (congrArg Int.natAbs hqC).symm
  have htAbs : t.natAbs = t.toNat := by
    simpa only [Int.natAbs_natCast] using (congrArg Int.natAbs htC).symm
  have huCop : a.natAbs.Coprime q.toNat := by
    have h := coprime_of_int_linear_combination (a := a) (q := q) (c := -t) (d := b)
      (by linear_combination hdet)
    rwa [hqAbs] at h
  have hvCop : b.natAbs.Coprime t.toNat := by
    have h := coprime_of_int_linear_combination (a := b) (q := t) (c := q) (d := -a)
      (by linear_combination hdet)
    rwa [htAbs] at h
  have hqNat : 0 < q.toNat := by omega
  have htNat : 0 < t.toNat := by omega
  have ⟨huNum, huDen⟩ := rat_num_den_of_reduced hqNat huCop
  have ⟨hvNum, hvDen⟩ := rat_num_den_of_reduced htNat hvCop
  have huMem : u ∈ fareyChain N := by
    apply mem_fareyChain.mpr
    rw [← Rat.cast_nonneg (K := ℝ), ← Rat.cast_le (K := ℝ), Rat.cast_one, hure]
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    exact ⟨div_nonneg (by exact_mod_cast ha) hqR.le,
      (div_le_one hqR).mpr (by exact_mod_cast haq), show u.den ≤ N by rw [huDen]; omega⟩
  have hvMem : v ∈ fareyChain N := by
    apply mem_fareyChain.mpr
    rw [← Rat.cast_nonneg (K := ℝ), ← Rat.cast_le (K := ℝ), Rat.cast_one, hvre]
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    exact ⟨div_nonneg (by exact_mod_cast hb) htR.le,
      (div_le_one htR).mpr (by exact_mod_cast hbt), show v.den ≤ N by rw [hvDen]; omega⟩
  rw [← hure] at hl
  rw [← hvre] at hh
  have hur : u ≤ r := by
    by_contra! h
    have hus : u < s := by exact_mod_cast hl.trans_lt hxs
    exact no_between_fareyChain hi huMem h hus
  have hsv : s ≤ v := by
    by_contra! h
    have hrv : r < v := by exact_mod_cast hrx.trans_le hh
    exact no_between_fareyChain hi hvMem hrv h
  have hur' : u = r := by
    apply le_antisymm hur
    by_contra! h
    have hUR : (u : ℝ) < (r : ℝ) := by exact_mod_cast h
    have hRV : (r : ℝ) < (v : ℝ) := hrx.trans_le hh
    rw [hure, rat_cast_as_div r] at hUR
    rw [rat_cast_as_div r, hvre] at hRV
    have hd := farey_denominator_add_le hq ht (by exact_mod_cast r.den_pos) hdet hUR hRV
    omega
  have hsv' : s = v := by
    apply le_antisymm hsv
    by_contra! h
    have hUS : (u : ℝ) < (s : ℝ) := hl.trans_lt hxs
    have hSV : (s : ℝ) < (v : ℝ) := by exact_mod_cast h
    rw [hure, rat_cast_as_div s] at hUS
    rw [rat_cast_as_div s, hvre] at hSV
    have hd := farey_denominator_add_le hq ht (by exact_mod_cast s.den_pos) hdet hUS hSV
    omega
  change ((r.den : ℤ) * s.num - r.num * (s.den : ℤ) = 1) ∧ N < r.den + s.den
  rw [← hur', hsv', huNum, huDen, hvNum, hvDen, hqC, htC]
  exact ⟨hdet, by omega⟩

theorem fareyChain_getLast {N : ℕ} (hN : 0 < N) :
    (fareyChain N).getLast (List.ne_nil_of_length_pos (fareyChain_pos hN)) = 1 := by
  rw [List.getLast_eq_getElem]
  exact fareyChain_last hN

@[simp] theorem mem_fareyChain_dropLast {N : ℕ} (hN : 0 < N) {r : ℚ} :
    r ∈ (fareyChain N).dropLast ↔ 0 ≤ r ∧ r < 1 ∧ r.den ≤ N := by
  constructor
  · intro hr
    have hh := (fareyChain_sortedLT N).pairwise.rel_dropLast_getLast hr
    rw [fareyChain_getLast hN] at hh
    have ⟨hr₀, _, hrN⟩ := mem_fareyChain.mp (List.mem_of_mem_dropLast hr)
    exact ⟨hr₀, hh, hrN⟩
  · rintro ⟨hr₀, hr₁, hrN⟩
    apply List.mem_dropLast_of_mem_of_ne_getLast (mem_fareyChain.mpr ⟨hr₀, hr₁.le, hrN⟩)
    rw [fareyChain_getLast hN]
    exact hr₁.ne

/-- All fractions in `[0,1)` with canonical denominator `k`, indexed by the
reduced residues occurring in the Rademacher sum. -/
def fareyResiduesAt (k : ℕ) : Finset ℚ :=
  ((range k).filter (fun h => h.Coprime k)).image (fun h : ℕ => (h : ℚ) / (k : ℚ))

@[simp] theorem mem_fareyResiduesAt {k : ℕ} {r : ℚ} :
    r ∈ fareyResiduesAt k ↔ 0 ≤ r ∧ r < 1 ∧ r.den = k := by
  constructor
  · intro hr
    obtain ⟨h, hh, rfl⟩ := mem_image.mp hr
    obtain ⟨hh, hcop⟩ := mem_filter.mp hh
    have hhK := mem_range.mp hh
    have hk : 0 < k := by omega
    have hkRat : (0 : ℚ) < k := by exact_mod_cast hk
    have hhRat : (h : ℚ) < k := by exact_mod_cast hhK
    have ⟨_, hden⟩ := rat_num_den_of_reduced (a := (h : ℤ)) hk (by simpa using hcop)
    exact ⟨div_nonneg (by positivity) hkRat.le, (div_lt_one hkRat).mpr hhRat,
      by simpa only [Int.cast_natCast] using hden⟩
  · rintro ⟨hr₀, hr₁, rfl⟩
    have hnum₀ : 0 ≤ r.num := Rat.num_nonneg.mpr hr₀
    have hdRat : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
    have hNumDen : r.num < (r.den : ℤ) := by
      rw [← r.num_div_den] at hr₁
      exact_mod_cast (div_lt_one hdRat).mp hr₁
    have hToNat : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg hnum₀
    have habs : r.num.natAbs = r.num.toNat := by
      simpa only [Int.natAbs_natCast] using (congrArg Int.natAbs hToNat).symm
    apply mem_image.mpr
    refine ⟨r.num.toNat, mem_filter.mpr ⟨mem_range.mpr (show r.num.toNat < r.den by omega),
      habs ▸ r.reduced⟩, ?_⟩
    rw [← Int.cast_natCast, hToNat, Rat.num_div_den]

/-- Reindex the chain with its final `1/1` removed by reduced residues. The addend
may depend on both the canonical numerator and the canonical denominator. -/
theorem sum_fareyChain_dropLast {A : Type*} [AddCommMonoid A]
    {N : ℕ} (hN : 0 < N) (f : ℤ → ℕ → A) :
    (∑ r ∈ (fareyChain N).dropLast.toFinset, f r.num r.den) =
      ∑ k ∈ Icc 1 N, ∑ h ∈ (range k).filter (fun h => h.Coprime k), f h k := by
  have hset : (fareyChain N).dropLast.toFinset = (Icc 1 N).biUnion fareyResiduesAt := by
    ext r
    simp only [List.mem_toFinset, mem_fareyChain_dropLast hN, mem_biUnion, mem_Icc,
      mem_fareyResiduesAt]
    constructor
    · rintro ⟨hr₀, hr₁, hrN⟩
      exact ⟨r.den, ⟨r.den_pos, hrN⟩, hr₀, hr₁, rfl⟩
    · rintro ⟨k, ⟨_, hkN⟩, hr₀, hr₁, hden⟩
      exact ⟨hr₀, hr₁, by rw [hden]; exact hkN⟩
  have hdisj : Set.PairwiseDisjoint (↑(Icc 1 N) : Set ℕ) fareyResiduesAt := by
    intro k hk j hj hkj
    apply disjoint_left.mpr
    intro r hr hr'
    exact hkj ((mem_fareyResiduesAt.mp hr).2.2.symm.trans (mem_fareyResiduesAt.mp hr').2.2)
  rw [hset, sum_biUnion hdisj]
  apply sum_congr rfl
  intro k hk
  have hk' : 0 < k := (mem_Icc.mp hk).1
  have hkRat : (0 : ℚ) < k := by exact_mod_cast hk'
  unfold fareyResiduesAt
  rw [sum_image]
  · apply sum_congr rfl
    intro h hh
    obtain ⟨hn, hd⟩ := rat_num_den_of_reduced (a := (h : ℤ)) hk'
      (by simpa using (mem_filter.mp hh).2)
    push_cast at hn hd
    rw [hn, hd]
  · intro a ha b hb hab
    have hEq : (a : ℚ) = b := by
      apply (div_left_inj₀ hkRat.ne').mp
      exact hab
    exact_mod_cast hEq

end DurfeeCCS.Step14
