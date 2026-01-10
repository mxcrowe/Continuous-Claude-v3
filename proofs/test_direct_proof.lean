import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def lineThrough (p q : Plane) : AffineSubspace ℝ Plane := affineSpan ℝ {p, q}

-- Direct proof approach using inner products
-- The key is that for a 2D plane, the perpendicular distance formulas 
-- can be related through the cross product / determinant

-- Helper: norm of cross product in 2D
def cross2D (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

-- The norm squared of the cross product relates to the area squared
lemma cross2D_sq_eq_det (u v : Plane) :
    cross2D u v ^ 2 = ‖u‖^2 * ‖v‖^2 - inner u v ^ 2 := by
  unfold cross2D
  simp only [EuclideanSpace.norm_sq, Fintype.sum_fin_eq_sum_range, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, EuclideanSpace.inner_piLp_equiv_symm, 
    inner_apply, RCLike.inner_apply, conj_trivial]
  ring

-- Cross product is antisymmetric
lemma cross2D_neg (u v : Plane) : cross2D v u = -cross2D u v := by
  unfold cross2D; ring

-- For perpendicular distance: if F is on line L through a,b with direction d = b - a,
-- and we project p onto L getting F, then dist(p, F)^2 = ‖p - a‖^2 - ‖F - a‖^2

-- Actually let me try a direct computation
lemma infDist_lineThrough_eq {p q r : Plane} (hpq : p ≠ q) :
    Metric.infDist r (lineThrough p q : Set Plane) = 
    |cross2D (q -ᵥ p) (r -ᵥ p)| / ‖q -ᵥ p‖ := by
  -- The perpendicular distance from r to line(p,q) equals
  -- |cross(q-p, r-p)| / ‖q-p‖
  -- This is the standard formula
  haveI : Nonempty (lineThrough p q) := ⟨⟨p, mem_affineSpan_insert_self ℝ p {q}⟩⟩
  haveI : FiniteDimensional ℝ (lineThrough p q).direction := inferInstance
  haveI : (lineThrough p q).direction.HasOrthogonalProjection := inferInstance
  
  -- Use dist_orthogonalProjection_eq_infDist
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist]
  
  -- Now compute the orthogonal projection
  let F := (EuclideanGeometry.orthogonalProjection (lineThrough p q) r : Plane)
  
  -- The projection satisfies: r - F ⊥ (q - p)
  -- So dist(r, F) = |cross(q-p, r-p)| / ‖q-p‖
  
  sorry

#check infDist_lineThrough_eq

end
