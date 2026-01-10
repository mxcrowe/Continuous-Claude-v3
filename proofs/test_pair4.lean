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
  have h_pos : 0 < dist p F := by rw [dist_pos]; intro hpF; exact hp_off (hpF ▸ hF_mem)
  have h_pythag : dist z p ^ 2 = dist z F ^ 2 + dist p F ^ 2 := by
    have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
      (s := L) p hz
    simp only [sq] at h ⊢; convert h using 1
  rw [dist_comm z p, dist_comm z F] at h_pythag
  have h1 : dist F z ^ 2 < dist p z ^ 2 := by
    calc dist F z ^ 2 < dist F z ^ 2 + dist p F ^ 2 := by linarith [sq_pos_of_pos h_pos]
      _ = dist p z ^ 2 := by linarith [h_pythag]
  have h_pz_pos : 0 < dist p z := by rw [dist_pos]; intro hpz; exact hp_off (hpz ▸ hz)
  nlinarith [sq_nonneg (dist F z), sq_nonneg (dist p z), dist_nonneg (x := F) (y := z)]

-- Points on an affine subspace are collinear
lemma collinear_of_mem_affineSubspace {L : AffineSubspace ℝ Plane} {a b c : Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) :
    Collinear ℝ ({a, b, c} : Set Plane) := by
  -- All points in L are collinear via L.direction
  rw [collinear_iff_of_mem (Set.mem_insert a _)]
  use 0  -- dummy direction, will be filled
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  -- This requires showing L is 1-dimensional or using a different approach
  -- Actually, let's use a different approach: L.direction is a submodule,
  -- and all differences of points in L lie in L.direction
  sorry

-- Wbtw implies one distance is less than the sum
lemma dist_le_of_wbtw {x y z : Plane} (h : Wbtw ℝ x y z) : dist x y ≤ dist x z := by
  have h_sum := Wbtw.dist_add_dist h
  linarith [dist_nonneg (x := y) (y := z)]

-- The main lemma using a simpler argument
-- Among 3 distinct points on L, one is "between" the other two
-- The endpoints of this segment have the largest distance
-- So we can pick the endpoint farther from F as z, and the middle point as x
lemma exists_pair_close' {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  
  -- Key: dist(F, t) < dist(p, t) for all t ∈ L
  have h_proj_lt : ∀ t ∈ L, dist F t < dist p t := fun t ht => dist_proj_lt_dist' ht hp_off
  
  -- Three points on L are collinear
  have h_col : Collinear ℝ ({a, b, c} : Set Plane) := collinear_of_mem_affineSubspace ha hb hc
  
  -- One is between the other two
  have h_btw := Collinear.wbtw_or_wbtw_or_wbtw h_col
  
  -- Case analysis
  rcases h_btw with h_wbtw | h_wbtw | h_wbtw
  · -- Wbtw ℝ a b c: b is between a and c
    -- dist(a, b) ≤ dist(a, c), dist(b, c) ≤ dist(a, c)
    -- We'll use dist(b, c) < dist(p, c)
    -- Since dist(b, c) ≤ dist(a, c) might not help directly...
    -- Better: pick z = c, x = b
    -- Need: dist(b, c) < dist(p, c)
    -- But we only know dist(F, c) < dist(p, c)
    -- And dist(b, c) could be larger than dist(F, c) if b is on the wrong side
    -- So this approach doesn't work directly...
    -- 
    -- Better approach: compare distances to F
    -- Among dist(F, a), dist(F, b), dist(F, c), the middle one when b is between a and c
    -- is bounded by the outer ones.
    -- Since Wbtw ℝ a b c means b ∈ segment[a, c], and F could be anywhere,
    -- we have multiple cases.
    --
    -- Simpler: pick z to maximize dist(F, z), then pick x among the others.
    -- For that x: dist(x, z) ≤ dist(F, z) (by triangle ineq in some sense)... no, not quite.
    --
    -- Actually, the simplest is:
    -- If b is between a and c, then:
    --   dist(a, b) ≤ dist(a, c) and dist(b, c) ≤ dist(a, c)
    -- So the maximum pairwise distance is dist(a, c)
    -- Now among {a, c}, pick z = the one farther from F
    -- Then: dist(F, z) = max(dist(F, a), dist(F, c))
    -- And the other one (call it x) satisfies: dist(x, z) = dist(a, c)
    -- But dist(a, c) could be larger than dist(p, z)! Not helpful.
    --
    -- OK, different approach: use F directly
    -- Consider {F, a, b, c} on L (collinear since all in L)
    -- By betweenness, we can order them
    -- Pick x, z adjacent to F in this ordering
    -- Then dist(x, z) = |dist(F, x) - dist(F, z)| (if on same side) 
    --                 = dist(F, x) + dist(F, z) (if on opposite sides)
    -- Hmm, still complicated.
    --
    -- Let me try: among {a, b, c}, pick the two that are on the same side of F
    -- (by pigeonhole, at least 2 are on the same side)
    sorry
  · -- Wbtw ℝ b c a: c is between b and a
    sorry
  · -- Wbtw ℝ c a b: a is between c and b
    sorry

end
