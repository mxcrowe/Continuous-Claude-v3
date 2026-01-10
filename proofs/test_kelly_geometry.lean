import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- The cross product in 2D (returns a scalar = z-component of 3D cross product)
def cross2D (v w : Plane) : ℝ :=
  v 0 * w 1 - v 1 * w 0

-- Area of triangle with signed orientation
def signedArea (p q r : Plane) : ℝ :=
  cross2D (q -ᵥ p) (r -ᵥ p) / 2

-- Absolute area
def triangleArea (p q r : Plane) : ℝ :=
  |signedArea p q r|

-- Check: Area formula using base and height
#check @EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
#check @EuclideanGeometry.orthogonalProjection_mem
#check @EuclideanGeometry.dist_orthogonalProjection_eq_infDist
#check @EuclideanGeometry.inner_vsub_orthogonalProjection_le

-- Key fact: for p, x, z, where x, z on L and p off L:
-- dist(p, line(x,z)) = 2 * Area(pxz) / dist(x, z)
-- Also: Area(pxz) = (1/2) * dist(x, z) * dist(p, L)
-- So: dist(p, line(x,z)) = dist(p, L) when {x, z} ⊂ L and p off L

-- Now for x, z on L, b on L:
-- dist(b, line(p,z)) = 2 * Area(bpz) / dist(p, z)
-- Area(bpz) = (1/2) * dist(b, z) * dist(p, L)  (base bz on L, height = dist(p, L))
-- So: dist(b, line(p,z)) = dist(b, z) * dist(p, L) / dist(p, z)

-- Let's prove this relationship using inner products
-- The perpendicular distance from b to line(p, z) equals:
-- ‖(b - p) - proj_{z-p}(b - p)‖ = ‖(b - p)‖ * sin(angle)

-- Actually, the simpler formula uses the cross product:
-- dist(b, line(p,z)) = |cross(z - p, b - p)| / ‖z - p‖

lemma cross2D_abs_eq_dist_mul_dist_mul_sin (u v : Plane) :
    |cross2D u v| = ‖u‖ * ‖v‖ * |Real.sin (InnerProductGeometry.angle u v)| := by
  sorry

-- The key lemma: perpendicular distance formula
lemma infDist_eq_cross_div_norm {p z b : Plane} (hpz : p ≠ z) :
    Metric.infDist b (Set.range (fun t : ℝ => p + t • (z -ᵥ p))) =
    |cross2D (z -ᵥ p) (b -ᵥ p)| / ‖z -ᵥ p‖ := by
  sorry

-- The formula we need for Kelly's proof:
-- For b, z on L, p off L at perpendicular height h:
-- infDist(b, line(p,z)) = dist(b, z) * h / dist(p, z)

-- Alternative: prove directly using existing Mathlib machinery
-- Check what's available for line distance

#check @Metric.infDist_le_dist_of_mem
#check @dist_comm
#check @Real.sqrt_lt_sqrt

-- Key relationship: dist(p, z)² = dist(F, z)² + h² where F is foot
-- So dist(p, z) > dist(F, z) > 0

-- For any x, z on L with x between F and z (or closer to F):
-- dist(x, z) ≤ dist(F, z) < dist(p, z)

-- Then: infDist(x, line(p,z)) = dist(x,z) * h / dist(p,z) < h ✓

-- Let's check if we can prove the simple bound:
-- Among 3 points on L, we can find x, z such that dist(x, z) < dist(p, z)

lemma exists_pair_with_smaller_dist {a b c p F : Plane}
    (hL : Collinear ℝ ({a, b, c} : Set Plane))
    (hF_on_abc : F ∈ affineSpan ℝ ({a, b, c} : Set Plane))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h_dist_p : ∀ x ∈ ({a, b, c} : Set Plane), dist p x ^ 2 = dist F x ^ 2 + dist p F ^ 2)
    (h_pos : 0 < dist p F) :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  -- Among {a, b, c}, at least two are on the same side of F
  -- Pick x = closer to F, z = farther from F among those two
  -- Then dist(x, z) ≤ dist(F, z) < dist(p, z)
  sorry

end
