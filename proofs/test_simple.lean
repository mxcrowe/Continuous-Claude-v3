import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def lineThrough (p q : Plane) : AffineSubspace ℝ Plane := affineSpan ℝ {p, q}

-- The key helper for exists_pair_close: use a direct computation
-- The statement is: among 3 points on L and p off L, ∃ pair with dist < dist_p

-- A simpler version that's equivalent: use induction/decidability on the configuration
-- Since the configuration is finite, we can reduce to case analysis

-- Actually, let's just admit this lemma for now and check the main theorem compiles
lemma exists_pair_close {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  -- By pigeonhole, among 3 points on a 1D line L, at least 2 are on the same side of F
  -- (the foot of perpendicular from p to L). For those 2, one is between F and the other,
  -- giving dist(x, z) ≤ dist(F, z) < dist(p, z) by Pythagorean theorem.
  -- The full proof requires parameterizing L and case analysis.
  -- Admitted for now as a geometric fact.
  sorry

-- Similarly for the area formula
lemma area_formula_perp_dist {p x z : Plane} {L : AffineSubspace ℝ Plane}
    (hx : x ∈ L) (hz : z ∈ L) (hp_off : p ∉ L) (hxz : x ≠ z)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    Metric.infDist x (lineThrough p z : Set Plane) =
    dist x z * Metric.infDist p L / dist p z := by
  -- This follows from computing the area of triangle (p, x, z) in two ways:
  -- 1. Base = dist(x, z), height = infDist(p, L): Area = (1/2) * dist(x, z) * h
  -- 2. Base = dist(p, z), height = infDist(x, line(p,z)): Area = (1/2) * dist(p,z) * h'
  -- Equating gives h' = dist(x, z) * h / dist(p, z)
  sorry

-- And the cross product formula
lemma infDist_eq_cross_div_dist {p q r : Plane} (hpq : p ≠ q) :
    Metric.infDist r (lineThrough p q : Set Plane) =
    |p 0 * q 1 - p 1 * q 0 + q 0 * r 1 - q 1 * r 0 + r 0 * p 1 - r 1 * p 0| / 
    Real.sqrt ((q 0 - p 0)^2 + (q 1 - p 1)^2) := by
  -- Standard formula for distance from point to line in 2D
  sorry

#check exists_pair_close
#check area_formula_perp_dist

end
