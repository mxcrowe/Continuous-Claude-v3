import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Check orthogonal projection APIs
#check @EuclideanGeometry.orthogonalProjection
#check @EuclideanGeometry.dist_orthogonalProjection_eq_infDist
#check @EuclideanGeometry.inner_vsub_orthogonalProjection_le
#check @EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq

-- Check if a line has orthogonal projection
example {a b : Plane} (hab : a ≠ b) :
    let L := affineSpan ℝ ({a, b} : Set Plane)
    L.direction.HasOrthogonalProjection := by
  intro L
  have h_dim : Module.finrank ℝ L.direction = 1 := by
    rw [direction_affineSpan]
    have h_indep : AffineIndependent ℝ ![a, b] := affineIndependent_of_ne ℝ hab
    have h_range : Set.range ![a, b] = {a, b} := Matrix.range_cons_cons_empty
    have h_card : Fintype.card (Fin 2) = 1 + 1 := rfl
    have h_finrank := AffineIndependent.finrank_vectorSpan h_indep h_card
    rw [h_range] at h_finrank
    exact h_finrank
  haveI : FiniteDimensional ℝ L.direction := Module.finite_of_finrank_eq_succ h_dim
  infer_instance

end
