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
  have hF_in_span : F ∈ affineSpan ℝ ({a, b} : Set Plane) := by
    rw [h_line]; exact hF
  exact collinear_insert_of_mem_affineSpan_pair hF_in_span

-- But do we have h_line automatically for an affine subspace containing a,b?
-- We need to show that if a ≠ b and L is 1-dimensional, then affineSpan {a, b} = L
-- Actually simpler: use collinear_triple_of_mem_affineSpan_pair

example {F a b p q : Plane}
    (hF : F ∈ affineSpan ℝ ({p, q} : Set Plane))
    (ha : a ∈ affineSpan ℝ ({p, q} : Set Plane))
    (hb : b ∈ affineSpan ℝ ({p, q} : Set Plane)) :
    Collinear ℝ ({F, a, b} : Set Plane) := by
  exact collinear_triple_of_mem_affineSpan_pair hF ha hb

#check collinear_triple_of_mem_affineSpan_pair

end
