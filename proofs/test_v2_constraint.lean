/-
  Testing v₂ constraint for complete triangles in [0,1]²
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- Test: Triangle with boundary vertices
-- P0 = (1/2, 1): color 0 (on y=1 edge)
-- P1 = (1, 1/2): color 1 (on x=1 edge)
-- P2 = (1, 1): color 2 (corner)
-- 2·Area = (1/2)*(1/2 - 1) + 1*(1 - 1) + 1*(1 - 1/2) = -1/4 + 0 + 1/2 = 1/4
example : padicValRat 2 (1/4 : ℚ) = -2 := by native_decide
-- v₂ = -2 ≤ 0 ✓

-- Test: Triangle with dyadic vertices
-- P0 = (1/4, 1/2): v₂(1/4)=-2, v₂(1/2)=-1, so -2 < -1 → color 0
-- P1 = (1/2, 1/4): v₂(1/2)=-1, v₂(1/4)=-2, so -1 > -2 → color 1
-- P2 = (1/2, 1/2): v₂(1/2)=-1 = v₂(1/2) → color 2
-- 2·Area = (1/4)*(1/4 - 1/2) + (1/2)*(1/2 - 1/2) + (1/2)*(1/2 - 1/4)
--        = (1/4)*(-1/4) + 0 + (1/2)*(1/4) = -1/16 + 1/8 = 1/16
example : padicValRat 2 (1/16 : ℚ) = -4 := by native_decide
-- v₂ = -4 ≤ 0 ✓

-- Counterexample: Triangle with non-dyadic vertices
-- P0 = (2/3, 4/5): v₂=1, v₂=2, so 1 < 2 → color 0
-- P1 = (4/5, 2/3): v₂=2, v₂=1, so 2 > 1 → color 1
-- P2 = (2/3, 2/5): v₂=1 = v₂=1 → color 2
-- This is in [0,1]² but has v₂(2·Area) = 2 > 0
-- So the constraint v₂ ≤ 0 does NOT hold for ALL complete triangles in [0,1]²

-- However, note that these vertices have v₂(coord) > 0
-- For dyadic rationals (k/2^n), v₂ ≤ 0

-- KEY INSIGHT: If all coordinates are dyadic (or have v₂ ≤ 0),
-- then the constraint holds.

-- For a "natural" triangulation of [0,1]² (starting from corners and subdividing),
-- vertices typically have dyadic coordinates, so v₂(coord) ≤ 0.

example : padicValRat 2 (2/3 : ℚ) = 1 := by native_decide  -- > 0
example : padicValRat 2 (1/3 : ℚ) = 0 := by native_decide  -- = 0
example : padicValRat 2 (1/2 : ℚ) = -1 := by native_decide  -- < 0
example : padicValRat 2 (1/4 : ℚ) = -2 := by native_decide  -- < 0
