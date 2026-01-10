import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def lineThrough (p q : Plane) : AffineSubspace ℝ Plane :=
  affineSpan ℝ {p, q}

-- Check if lines have orthogonal projection
#check @Submodule.instHasOrthogonalProjectionFiniteDimensional

-- Check the orthogonal projection for affine subspaces
#check @EuclideanGeometry.orthogonalProjection
#check @EuclideanGeometry.dist_orthogonalProjection_eq_infDist
#check @EuclideanGeometry.orthogonalProjection_mem

-- For a line (1-dimensional), we need direction.HasOrthogonalProjection
example {L : AffineSubspace ℝ Plane} [hL : Nonempty L] 
    (h_dim : Module.finrank ℝ L.direction = 1) :
    L.direction.HasOrthogonalProjection := by
  haveI : FiniteDimensional ℝ L.direction := Module.finite_of_finrank_eq_succ h_dim
  infer_instance

-- Key lemma: dist to projection = infDist
#check @EuclideanGeometry.dist_orthogonalProjection_eq_infDist

-- Triangle inequality and distances
#check @dist_triangle
#check @Metric.infDist_le_dist_of_mem
#check @Metric.infDist_lt_iff

-- For line through p c
example (p c : Plane) (hpc : p ≠ c) : Nonempty (lineThrough p c) :=
  ⟨⟨p, left_mem_affineSpan_pair ℝ p c⟩⟩

-- Check for distance formulas
#check @Real.dist_eq
#check @dist_eq_norm

end
