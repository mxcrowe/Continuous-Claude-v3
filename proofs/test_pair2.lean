import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Key helper: dist from F to any point on L is less than dist from p to that point
lemma dist_proj_lt_dist' {L : AffineSubspace ℝ Plane} {p z : Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection]
    (hz : z ∈ L) (hp_off : p ∉ L) :
    let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
    dist F z < dist p z := by
  intro F
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  have h_pos : 0 < dist p F := by
    rw [dist_pos]
    intro hpF
    exact hp_off (hpF ▸ hF_mem)
  -- Pythagorean: dist(z, p)² = dist(z, F)² + dist(p, F)²
  -- Using the lemma with z as p₁ and p as p₂
  have h_pythag : dist z p ^ 2 = dist z F ^ 2 + dist p F ^ 2 := by
    have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
      (s := L) p hz
    simp only [sq] at h ⊢
    convert h using 1 <;> ring
  -- Rewrite using dist symmetry
  rw [dist_comm z p, dist_comm z F] at h_pythag
  -- From Pythagorean with h > 0, get strict inequality
  have h1 : dist F z ^ 2 < dist p z ^ 2 := by
    calc dist F z ^ 2 < dist F z ^ 2 + dist p F ^ 2 := by linarith [sq_pos_of_pos h_pos]
      _ = dist p z ^ 2 := by linarith [h_pythag]
  -- Conclude dist F z < dist p z
  have h_Fz_nn : 0 ≤ dist F z := dist_nonneg
  have h_pz_nn : 0 ≤ dist p z := dist_nonneg
  have h_pz_pos : 0 < dist p z := by
    by_contra h_pz_zero
    push_neg at h_pz_zero
    have h_eq : dist p z = 0 := le_antisymm h_pz_zero h_pz_nn
    rw [dist_eq_zero] at h_eq
    exact hp_off (h_eq ▸ hz)
  nlinarith [sq_nonneg (dist F z), sq_nonneg (dist p z), sq_abs (dist F z), sq_abs (dist p z)]

#check dist_proj_lt_dist'

end
