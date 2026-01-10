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
  have h_pythag : dist z p ^ 2 = dist z F ^ 2 + dist p F ^ 2 := by
    have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
      (s := L) p hz
    simp only [sq] at h ⊢
    convert h using 1
  rw [dist_comm z p, dist_comm z F] at h_pythag
  have h1 : dist F z ^ 2 < dist p z ^ 2 := by
    calc dist F z ^ 2 < dist F z ^ 2 + dist p F ^ 2 := by linarith [sq_pos_of_pos h_pos]
      _ = dist p z ^ 2 := by linarith [h_pythag]
  have h_Fz_nn : 0 ≤ dist F z := dist_nonneg
  have h_pz_pos : 0 < dist p z := by
    rw [dist_pos]
    intro hpz; exact hp_off (hpz ▸ hz)
  nlinarith [sq_nonneg (dist F z), sq_nonneg (dist p z)]

-- Wbtw means "weakly between" - x is on the segment [a, b]
-- If F is between x and z, then dist(x, z) = dist(x, F) + dist(F, z) ≥ dist(F, z)
-- If F is not between x and z, then one of them is between the other and F,
-- so dist(x, z) ≤ dist(F, z) or dist(x, z) ≤ dist(F, x)

-- Check: among 3 collinear points, one is between the other two
#check @Collinear.wbtw_or_wbtw_or_wbtw

-- Check: Wbtw implies distance decomposition
#check @Wbtw.dist_add_dist

-- Test: Among 3 collinear points on L, can we find a pair?
example {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  
  -- Among {a, b, c}, one is between the other two
  have h_col : Collinear ℝ ({a, b, c} : Set Plane) := by
    rw [collinear_iff_of_mem (Finset.mem_coe.mpr (Finset.mem_insert_self a _))]
    -- All points are on L, so they're collinear
    -- The direction of L is 1-dimensional
    have h_dim : Module.finrank ℝ L.direction = 1 := Module.finrank_eq_one_iff'.mpr ⟨
      ⟨Classical.choose (FiniteDimensional.exists_is_basis_finset (R := ℝ) L.direction), 
       sorry⟩, -- tedious but doable
      sorry⟩
    sorry  -- {a,b,c} ⊆ L → collinear
    
  -- Get the betweenness
  have h_btw := Collinear.wbtw_or_wbtw_or_wbtw h_col hab hac hbc
  
  -- Case analysis based on which point is between
  rcases h_btw with h_wbtw_abc | h_wbtw_bac | h_wbtw_acb
  · -- a is between b and c: Wbtw ℝ b a c
    -- Then dist(b, a) + dist(a, c) = dist(b, c)
    -- So dist(b, a) ≤ dist(b, c)
    -- And dist(F, c) < dist(p, c) by dist_proj_lt_dist'
    -- Need to pick wisely...
    -- If F is between a and c, pick x = a, z = c
    -- If F is not between a and c, one of {a, c} is between F and the other
    sorry
  · -- b is between a and c: Wbtw ℝ a b c
    -- dist(a, b) ≤ dist(a, c)
    sorry
  · -- c is between a and b: Wbtw ℝ a c b
    sorry

end
