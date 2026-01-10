import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Helper: points in an affine subspace of dim ≤ 1 are collinear
lemma collinear_of_mem_affineSubspace_finrank_le_one {L : AffineSubspace ℝ Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction]
    (h_dim : Module.finrank ℝ L.direction ≤ 1) {x y z : Plane}
    (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) :
    Collinear ℝ ({x, y, z} : Set Plane) := by
  have h_sub : ({x, y, z} : Set Plane) ⊆ (L : Set Plane) := by
    intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> assumption
  -- The vectorSpan of {x, y, z} is contained in L.direction
  have h_dir : vectorSpan ℝ ({x, y, z} : Set Plane) ≤ L.direction := by
    apply vectorSpan_mono
    exact h_sub
  -- finrank of a submodule ≤ finrank of the ambient
  have h_finrank : Module.finrank ℝ (vectorSpan ℝ ({x, y, z} : Set Plane)) ≤ 1 := by
    calc Module.finrank ℝ (vectorSpan ℝ ({x, y, z} : Set Plane))
        ≤ Module.finrank ℝ L.direction := Submodule.finrank_mono h_dir
      _ ≤ 1 := h_dim
  exact collinear_iff_finrank_le_one.mpr h_finrank

#check collinear_of_mem_affineSubspace_finrank_le_one

end
