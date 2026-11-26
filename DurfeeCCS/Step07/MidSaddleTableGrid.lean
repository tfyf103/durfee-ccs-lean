module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fin.Basic

/-! Rational certificates for the finite maximum in (64), page 34.

Each piece groups several of the manuscript's intervals. Its endpoints provide
a common upper bound on y and a common lower bound on each folded sine
argument. The analytic soundness lemmas transfer these rational checks to
the terms of (64).
-/

@[expose] public section

namespace DurfeeCCS.Step07

structure MinorArcData where
  left : ℚ
  right : ℚ
  amplitude : ℚ
  epsLower : ℚ
  epsUpper : ℚ
  target : ℚ
  deriving DecidableEq

/-- The seventeen finite rows, followed by the unbounded final range
whose lower reciprocal-radius enclosure is zero. -/
def minorArcData : Fin 18 → MinorArcData
  | 0 => ⟨0, 0.04, 1.09218, 0.96078943, 1, 0.887⟩
  | 1 => ⟨0.04, 0.08, 1.11497, 0.92311634, 0.96078944, 0.951⟩
  | 2 => ⟨0.08, 0.12, 1.13814, 0.88692043, 0.92311635, 1.007⟩
  | 3 => ⟨0.12, 0.16, 1.16169, 0.85214378, 0.88692044, 1.055⟩
  | 4 => ⟨0.16, 0.20, 1.18560, 0.81873075, 0.85214379, 1.097⟩
  | 5 => ⟨0.20, 0.25, 1.21600, 0.77880078, 0.81873076, 1.143⟩
  | 6 => ⟨0.25, 0.32, 1.25951, 0.72614903, 0.77880079, 1.198⟩
  | 7 => ⟨0.32, 0.40, 1.31054, 0.67032004, 0.72614904, 1.249⟩
  | 8 => ⟨0.40, 0.50, 1.37623, 0.60653065, 0.67032005, 1.301⟩
  | 9 => ⟨0.50, 0.65, 1.47850, 0.52204577, 0.60653066, 1.361⟩
  | 10 => ⟨0.65, 0.85, 1.62127, 0.42741493, 0.52204578, 1.416⟩
  | 11 => ⟨0.85, 1, 1.73266, 0.36787944, 0.42741494, 1.444⟩
  | 12 => ⟨1, 1.5, 2.12575, 0.22313016, 0.36787945, 1.503⟩
  | 13 => ⟨1.5, 2.25, 2.76012, 0.10539922, 0.22313017, 1.537⟩
  | 14 => ⟨2.25, 4, 4.34983, 0.01831563, 0.10539923, 1.571⟩
  | 15 => ⟨4, 5, 5.29407, 0.00673794, 0.01831564, 1.584⟩
  | 16 => ⟨5, 6, 6.25266, 0.00247875, 0.00673795, 1.593⟩
  | _ => ⟨6, 6, 5.76, 0, 0.00247876, 1.593⟩

/-- Integer indices at the endpoints of a common partition for every row. -/
def minorArcGridKnots : List ℕ :=
  [5, 7, 9, 12, 18, 24, 30, 43, 55, 105, 205, 404, 803, 1202, 1401, 1501,
    1551, 1576, 1588, 1600]

def minorArcGridBlock (i : Fin 19) : ℕ × ℕ :=
  (minorArcGridKnots[i.val]!, minorArcGridKnots[i.val + 1]!)

/-- Fold an endpoint index between successive zeros to distance at most π/2. -/
def minorArcFold (a : ℕ) : ℕ := min (a % 3200) (3200 - a % 3200)

/-- A common lower endpoint distance from the nearest zero, in units of π/3200. -/
def minorArcBlockDist (j l u : ℕ) : ℕ :=
  if (j * l) / 3200 = (j * u) / 3200 then min (minorArcFold (j * l)) (minorArcFold (j * u))
  else 0

def minorArcSinLower (j l u : ℕ) : ℚ :=
  let a := 3.141592 * (minorArcBlockDist j l u : ℚ) / 3200
  a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040

def minorArcYmax (a : MinorArcData) : ℚ := min 0.072 (a.amplitude / 80)

def minorArcC (eps y : ℚ) (j : ℕ) : ℚ :=
  2 / j + j * y ^ 2 / 6 - (eps ^ j / j) * (1 - (j * y) ^ 2 / 24)

def minorArcBupper (eps y z : ℚ) (j : ℕ) : ℚ :=
  let x := j * y / 2
  (2 / j + j * y ^ 2 / 6) / (1 + (z * (1 - x ^ 2 / 6) / x) ^ 2) + y * eps ^ j / (2 * z)

def minorArcBlockTerm (a : MinorArcData) (l u j : ℕ) : ℚ :=
  let y := min (minorArcYmax a) (3.141593 * u / 12800)
  let z := minorArcSinLower j l u
  let c := minorArcC a.epsLower y j
  if 0 < z then min c (minorArcBupper a.epsUpper y z j) else c

def minorArcWeight (j : ℕ) : ℚ := 2 * (19 / 20 : ℚ) ^ j / j

def minorArcBlockSum (a : MinorArcData) (l u : ℕ) : ℚ :=
  ((List.range 20).map fun i => minorArcWeight (i + 1) * minorArcBlockTerm a l u (i + 1)).sum

def minorArcSmallSum (a : MinorArcData) : ℚ :=
  let y₀ : ℚ := 3.141593 / 2560
  let w := 0.998 * 8 * (1 - (10 * y₀) ^ 2 / 6)
  ((List.range 20).map fun i =>
    let j := i + 1
    minorArcWeight j * ((2 / j + j * y₀ ^ 2 / 6) / (1 + w ^ 2) +
      a.epsUpper ^ j / (0.998 * 8 * j))).sum

def minorArcFixed (a : MinorArcData) : ℚ :=
  0.2 + (minorArcYmax a) ^ 2 / 48 - 0.1 * a.epsLower +
    4 * 0.006725 + 2 * minorArcYmax a * 0.20195

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- The grid covers all of the elementary intervals beginning at k=5. -/
theorem minorArc_grid_cover :
    ∀ k : Fin 1600, 5 ≤ k.val →
      ∃ b : Fin 19, (minorArcGridBlock b).1 ≤ k.val ∧ k.val + 1 ≤ (minorArcGridBlock b).2 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- The finite integer test and upper bounds for every block, for all 18 ranges. -/
theorem minorArc_block_arithmetic :
    ∀ r : Fin 18, ∀ b : Fin 19,
      minorArcFixed (minorArcData r) +
        minorArcBlockSum (minorArcData r) (minorArcGridBlock b).1 (minorArcGridBlock b).2 <
          (minorArcData r).target := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- The companion finite certificate for the small-angle term q₀. -/
theorem minorArc_small_arithmetic :
    ∀ r : Fin 18, minorArcFixed (minorArcData r) + minorArcSmallSum (minorArcData r) <
      (minorArcData r).target := by
  decide +kernel

def minorArcTailBlock (ν k₀ : ℕ) : ℚ :=
  ((List.range 15).map fun k => (19 / 20 : ℚ) ^ (k + k₀) / ((k + k₀ : ℕ) : ℚ) ^ ν).sum

def minorArcTailResidual (ν : ℕ) : ℚ :=
  (19 / 20 : ℚ) ^ 81 / (81 ^ ν * (1 - 19 / 20))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem minorArc_tail_arithmetic_one :
    minorArcTailBlock 1 21 < 0.138489947 ∧ minorArcTailBlock 1 36 < 0.040684031 ∧
    minorArcTailBlock 1 51 < 0.013828993 ∧ minorArcTailBlock 1 66 < 0.005062682 ∧
    minorArcTailResidual 1 < 0.003873977 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem minorArc_tail_arithmetic_two :
    minorArcTailBlock 2 21 < 0.005373340 ∧ minorArcTailBlock 2 36 < 0.000987032 ∧
    minorArcTailBlock 2 51 < 0.000245052 ∧ minorArcTailBlock 2 66 < 0.000070748 ∧
    minorArcTailResidual 2 < 0.000047827 := by
  decide +kernel

end DurfeeCCS.Step07
