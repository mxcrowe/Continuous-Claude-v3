import Mathlib

open scoped EuclideanGeometry
open AffineSubspace

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Check the signature of the Pythagorean theorem
#check @EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq

-- Test application
example {L : AffineSubspace ℝ Plane} {p t : Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection]
    (ht : t ∈ L) :
    let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
    dist t p ^ 2 = dist t F ^ 2 + dist p F ^ 2 := by
  intro F
  -- The lemma gives: dist p₁ p₂ * dist p₁ p₂ = dist p₁ (proj p₂) * ... + dist p₂ (proj p₂) * ...
  -- With p₁ = t, p₂ = p, proj = proj L
  have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s := L) p ht
  -- h : dist t p * dist t p = dist t (proj L p) * dist t (proj L p) + dist p (proj L p) * dist p (proj L p)
  simp only [sq]
  convert h using 1
  ring

end
