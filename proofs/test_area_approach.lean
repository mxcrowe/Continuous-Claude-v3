import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def lineThrough (p q : Plane) : AffineSubspace ℝ Plane := affineSpan ℝ {p, q}

-- The key: Plane is 2-dimensional
instance : Fact (Module.finrank ℝ Plane = 2) := ⟨finrank_euclideanSpace_fin⟩

-- Get the standard orientation on Plane
def stdOrientation : Orientation ℝ Plane (Fin 2) :=
  (OrthonormalBasis.fromOrthonormalSet
    (EuclideanSpace.orthonormal_basisFun (Fin 2) ℝ).orthonormal
    (by simp [finrank_euclideanSpace_fin])).toBasis.orientation

-- The area form on Plane
def areaForm2D : Plane →ₗ[ℝ] Plane →ₗ[ℝ] ℝ := stdOrientation.areaForm

-- Key identity: inner² + area² = ‖a‖² * ‖b‖²
lemma inner_sq_add_area_sq (a b : Plane) :
    inner (𝕜 := ℝ) a b ^ 2 + (areaForm2D a b) ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 :=
  stdOrientation.inner_sq_add_areaForm_sq a b

-- The perpendicular distance from a point r to line(p,q) can be expressed using area
-- dist(r, line) = |area(q-p, r-p)| / ‖q-p‖
-- This is because: area = base * height, so height = area / base

-- Let me try to prove the area formula directly
lemma area_formula_attempt {p x z : Plane} {L : AffineSubspace ℝ Plane}
    (hx : x ∈ L) (hz : z ∈ L) (hp_off : p ∉ L) (hxz : x ≠ z)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection]
    (h_dim : Module.finrank ℝ L.direction = 1) :
    Metric.infDist x (lineThrough p z : Set Plane) =
    dist x z * Metric.infDist p L / dist p z := by
  -- Setup
  haveI : Nonempty (lineThrough p z) := ⟨⟨p, subset_affineSpan ℝ _ (mem_insert_self p {z})⟩⟩
  haveI : FiniteDimensional ℝ (lineThrough p z).direction := inferInstance
  haveI : (lineThrough p z).direction.HasOrthogonalProjection := inferInstance

  -- Let F = orthogonal projection of p onto L
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p

  -- Let G = orthogonal projection of x onto lineThrough p z
  let G : Plane := ↑(EuclideanGeometry.orthogonalProjection (lineThrough p z) x)
  have hG_mem : G ∈ lineThrough p z := EuclideanGeometry.orthogonalProjection_mem x

  -- infDist(p, L) = dist(p, F)
  have h_infDist_p : Metric.infDist p L = dist p F :=
    (EuclideanGeometry.dist_orthogonalProjection_eq_infDist L p).symm

  -- infDist(x, lineThrough p z) = dist(x, G)
  have h_infDist_x : Metric.infDist x (lineThrough p z : Set Plane) = dist x G :=
    (EuclideanGeometry.dist_orthogonalProjection_eq_infDist (lineThrough p z) x).symm

  rw [h_infDist_p, h_infDist_x]

  -- Now use the area equality:
  -- |areaForm2D (z -ᵥ x) (p -ᵥ x)| = dist(x, z) * dist(p, F)
  --                                  = dist(p, z) * dist(x, G)
  -- So: dist(x, G) = dist(x, z) * dist(p, F) / dist(p, z)

  -- The area of parallelogram with sides (z - x) and (p - x) is |areaForm2D (z -ᵥ x) (p -ᵥ x)|
  -- This equals base * height for any base choice

  have hp_ne_z : p ≠ z := fun h => hp_off (h ▸ hz)
  have hpz_pos : 0 < dist p z := dist_pos.mpr hp_ne_z
  have hxz_pos : 0 < dist x z := dist_pos.mpr hxz

  -- Key: the signed area of triangle pxz (really parallelogram/2) is the same however computed
  -- |area| = dist(x,z) * h_p = dist(p,z) * h_x where h_p, h_x are perpendicular heights

  -- F is on L, and p - F ⊥ L.direction
  -- Since x, z ∈ L and L is 1-dimensional, the direction of line xz equals L.direction
  -- So p - F ⊥ (z - x), meaning F is the closest point on line xz to p
  -- Actually this is only true if lineThrough x z = L...

  -- Since h_dim : Module.finrank ℝ L.direction = 1 and x ≠ z with x, z ∈ L,
  -- we have affineSpan ℝ {x, z} = L
  have h_span_eq : lineThrough x z = L := by
    unfold lineThrough
    apply le_antisymm
    · apply affineSpan_le.mpr
      intro p' hp'
      simp only [mem_insert_iff, mem_singleton_iff] at hp'
      rcases hp' with rfl | rfl <;> assumption
    · -- L ≤ affineSpan {x, z}
      -- Since L is 1-dimensional and contains x ≠ z, it equals affineSpan {x, z}
      have : affineSpan ℝ ({x, z} : Set Plane) = ⊤ ⊔ᵥ L ⊓ affineSpan ℝ ({x, z} : Set Plane) := by
        sorry
      sorry

  sorry

#check area_formula_attempt

end
