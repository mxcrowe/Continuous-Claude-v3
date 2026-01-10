import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Use collinear_insert_of_mem_affineSpan_pair
example {L : AffineSubspace ℝ Plane} {F a b : Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction] 
    (hF : F ∈ L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b)
    (h_line : affineSpan ℝ ({a, b} : Set Plane) = L) : 
    Collinear ℝ ({F, a, b} : Set Plane) := by
  rw [Set.insert_comm]
  apply collinear_insert_of_mem_affineSpan_pair
  rw [h_line]
  exact hF

#check collinear_insert_of_mem_affineSpan_pair

end
