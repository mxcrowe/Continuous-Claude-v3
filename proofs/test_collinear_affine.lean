import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Test: can we prove collinearity of subset of affine subspace?
example {L : AffineSubspace ℝ Plane} {F a b : Plane}
    (hF : F ∈ L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : 
    Collinear ℝ ({F, a, b} : Set Plane) := by
  -- affineSpan ℝ {a, b} ≤ L
  have h_span : affineSpan ℝ ({a, b} : Set Plane) ≤ L := by
    apply affineSpan_le.mpr
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> assumption
  -- F ∈ affineSpan ℝ {a, b} since F ∈ L and... no wait, that's the wrong direction
  -- I need to use that L is 1-dimensional
  sorry

-- Alternative: use collinear_triple_of_mem_affineSpan_pair directly
example {L : AffineSubspace ℝ Plane} {F a b : Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction] 
    (h_dim : finrank ℝ L.direction ≤ 1)
    (hF : F ∈ L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : 
    Collinear ℝ ({F, a, b} : Set Plane) := by
  exact?

end
