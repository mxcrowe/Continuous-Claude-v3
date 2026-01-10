import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def lineThrough (p q : Plane) : AffineSubspace ℝ Plane := affineSpan ℝ {p, q}

-- Try to prove area formula using Pythagorean theorem
-- Key insight: both Metric.infDist x (lineThrough p z) and Metric.infDist p L 
-- can be expressed via orthogonal projections

lemma area_formula_perp_dist {p x z : Plane} {L : AffineSubspace ℝ Plane}
    (hx : x ∈ L) (hz : z ∈ L) (hp_off : p ∉ L) (hxz : x ≠ z)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    Metric.infDist x (lineThrough p z : Set Plane) =
    dist x z * Metric.infDist p L / dist p z := by
  -- Let F be the foot of perpendicular from p to L
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  have hp_ne_z : p ≠ z := fun h => hp_off (h ▸ hz)
  
  -- The infDist from p to L equals dist(p, F)
  have h_infDist_p : Metric.infDist p L = dist p F := by
    exact (EuclideanGeometry.dist_orthogonalProjection_eq_infDist L p).symm
  
  -- For the line through p and z, we need a similar calculation
  -- Let G be the foot of perpendicular from x to line(p,z)
  haveI : Nonempty (lineThrough p z) := ⟨⟨p, subset_affineSpan ℝ _ (mem_insert_self p {z})⟩⟩
  haveI : FiniteDimensional ℝ (lineThrough p z).direction := by
    unfold lineThrough
    infer_instance
  haveI : (lineThrough p z).direction.HasOrthogonalProjection := inferInstance
  
  let G : Plane := ↑(EuclideanGeometry.orthogonalProjection (lineThrough p z) x)
  
  have h_infDist_x : Metric.infDist x (lineThrough p z : Set Plane) = dist x G := by
    exact (EuclideanGeometry.dist_orthogonalProjection_eq_infDist (lineThrough p z) x).symm
  
  rw [h_infDist_p, h_infDist_x]
  
  -- Now we need to relate dist x G to dist x z * dist p F / dist p z
  -- This is the area formula: Area = (1/2) * base * height
  -- Triangle pxz has area = (1/2) * dist(x,z) * dist(p,F) (base xz, height F to xz)
  --                       = (1/2) * dist(p,z) * dist(x,G) (base pz, height G)
  -- So dist(x,G) = dist(x,z) * dist(p,F) / dist(p,z)
  
  sorry

#check area_formula_perp_dist

end
