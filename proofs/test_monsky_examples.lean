/-
  Testing Monsky's Lemma with concrete examples
  
  For a complete triangle with colors 0, 1, 2:
  - Color 0 vertex (a,b): v₂(a) < v₂(b), so a is "dominant"
  - Color 1 vertex (c,d): v₂(c) > v₂(d), so d is "dominant"
  - Color 2 vertex (e,f): v₂(e) = v₂(f)
  
  Monsky's lemma: v₂(2·Area) = v₂(a) + v₂(d) + v₂(f)
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

-- Example 1: Simple complete triangle in [0,1]²
-- P0 = (1/2, 1): v₂(1/2) = -1, v₂(1) = 0, so -1 < 0 → color 0
-- P1 = (1, 1/2): v₂(1) = 0, v₂(1/2) = -1, so 0 > -1 → color 1  
-- P2 = (1, 1): v₂(1) = v₂(1) = 0 → color 2

-- Dominant valuations: v₂(1/2) + v₂(1/2) + v₂(1) = -1 + (-1) + 0 = -2
-- 2·Area = (1/2)*(1/2 - 1) + 1*(1 - 1) + 1*(1 - 1/2) = -1/4 + 0 + 1/2 = 1/4
-- v₂(1/4) = -2 ✓

example : padicValRat 2 (1/4 : ℚ) = -2 := by native_decide

-- Example 2: Another complete triangle
-- P0 = (1/4, 1/2): v₂(1/4) = -2, v₂(1/2) = -1, so -2 < -1 → color 0
-- P1 = (1/2, 1/4): v₂(1/2) = -1, v₂(1/4) = -2, so -1 > -2 → color 1
-- P2 = (1/2, 1/2): v₂(1/2) = v₂(1/2) = -1 → color 2

-- Dominant: v₂(1/4) + v₂(1/4) + v₂(1/2) = -2 + (-2) + (-1) = -5
-- 2·Area = (1/4)*(1/4 - 1/2) + (1/2)*(1/2 - 1/2) + (1/2)*(1/2 - 1/4)
--        = (1/4)*(-1/4) + 0 + (1/2)*(1/4) = -1/16 + 1/8 = 1/16
-- v₂(1/16) = -4 ≠ -5  (formula doesn't match exactly?)

example : padicValRat 2 (1/16 : ℚ) = -4 := by native_decide

-- Hmm, let me recalculate...
-- Actually the formula is more subtle. Let me compute directly.

-- For the unit square triangulation, a key observation:
-- Complete triangles in [0,1]² with coordinates in {k/2^n : k,n ∈ ℕ} 
-- (dyadic rationals) have v₂(2·Area) ≤ 0.

-- For coordinates like 2/3, 4/5 etc. (non-dyadic), v₂ can be positive.
-- But these don't arise naturally in triangulations of [0,1]².

-- The key constraint: For equal-area triangulation with |2·Area| = 2/n,
-- v₂(2/n) = 1 for odd n.
-- This requires v₂(2·Area) = 1 or v₂(2·Area) = 1 (for |·|).

-- For complete triangles in [0,1]² with typical coordinates,
-- v₂(2·Area) tends to be ≤ 0, which contradicts v₂ = 1.
