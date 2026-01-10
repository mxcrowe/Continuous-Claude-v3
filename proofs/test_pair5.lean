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

-- Helper: For Wbtw ℝ x y z, we have dist(x, y) ≤ dist(x, z)
lemma dist_le_of_wbtw {x y z : Plane} (h : Wbtw ℝ x y z) : dist x y ≤ dist x z := by
  have h_sum := Wbtw.dist_add_dist h
  linarith [dist_nonneg (x := y) (y := z)]

-- Helper: For Wbtw ℝ x y z, we have dist(y, z) ≤ dist(x, z)
lemma dist_le_of_wbtw' {x y z : Plane} (h : Wbtw ℝ x y z) : dist y z ≤ dist x z := by
  have h_sum := Wbtw.dist_add_dist h
  linarith [dist_nonneg (x := x) (y := y)]

-- Points on L are collinear
lemma collinear_of_mem_affineSubspace' {L : AffineSubspace ℝ Plane} {S : Set Plane}
    (hS : S ⊆ L) : Collinear ℝ S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact collinear_empty ℝ Plane
  · rw [collinear_iff_of_mem hx]
    use 0
    intro y hy
    have hxL := hS hx
    have hyL := hS hy
    -- y - x is in L.direction
    have h := AffineSubspace.vsub_mem_direction hyL hxL
    -- L.direction is a submodule, so there's some t with y - x = t • v for basis v
    -- But we need to show y - x = t • 0 for some t, which is only true if y = x
    -- This approach doesn't work for the general case
    -- Let me use a different approach
    sorry

-- The simplest approach: pick z to be the farthest from F, x to be one of the other two
-- Then use Wbtw to bound dist(x, z)
lemma exists_pair_close'' {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  have h_proj_lt : ∀ t ∈ L, dist F t < dist p t := fun t ht => dist_proj_lt_dist' ht hp_off
  
  -- Strategy: Find z that maximizes dist(F, z), then find x among {a, b, c} \ {z}
  -- such that dist(x, z) ≤ dist(F, z)
  
  -- First, {F, a, b, c} are all on L, hence collinear
  have h_col_Fabc : Collinear ℝ ({F, a, b, c} : Set Plane) := by
    apply collinear_of_mem_affineSubspace'
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
    
  -- Among {F, a, b, c}, consider the "extremes" - the two that contain all others between them
  -- One of these extremes is in {a, b, c}. Pick z = that extreme.
  -- Then F is between the other extreme and z, or between two of {a, b, c}.
  -- In either case, we can find x ∈ {a, b, c} with dist(x, z) ≤ dist(F, z).
  
  -- This requires careful case analysis. Let me use a computational approach instead.
  
  -- Pick z = argmax_{t ∈ {a,b,c}} dist(F, t)
  -- Then for any x ∈ {a, b, c}, x ≠ z:
  --   - If Wbtw ℝ F x z or Wbtw ℝ x F z: dist(x, z) ≤ dist(F, z) ✓
  --   - If Wbtw ℝ F z x: but then dist(F, x) > dist(F, z), contradicting z being the max
  --   - If Wbtw ℝ x z F: same contradiction
  --   - etc.
  
  -- So among any 4 collinear points {F, a, b, c}, if z maximizes dist(F, ·) over {a,b,c},
  -- then for the other two x ∈ {a,b,c}\{z}, we have dist(x, z) ≤ dist(F, z).
  
  -- But wait, this isn't quite right either. Let me think more carefully.
  
  -- On a line, order the 4 points. Say the order is: a < F < b < c (arbitrary example)
  -- Then dist(F, c) is the max over {a, b, c} (since c is farthest from F)
  -- For x = b: dist(b, c) < dist(F, c) (since F < b < c means F is to the left of b)
  --            Actually, dist(b, c) = |b - c| and dist(F, c) = |F - c|
  --            Since F < b < c, we have F - c < b - c < 0, so |F - c| > |b - c|. ✓
  -- For x = a: dist(a, c) = |a - c| and dist(F, c) = |F - c|
  --            Since a < F < c, we have a - c < F - c < 0, so |a - c| > |F - c|. ✗
  --            
  -- So picking z = c (the max) and x = a doesn't work!
  
  -- The correct approach: among {a, b, c}, at least two are on the same side of F.
  -- Pick those two as x and z, with z farther from F.
  -- Then dist(x, z) = |dist(F, z) - dist(F, x)| ≤ dist(F, z) < dist(p, z). ✓
  
  -- Let me implement this pigeonhole argument.
  
  -- First, define "same side of F": t is on the positive side if the signed distance is ≥ 0
  -- We need a direction vector v for L.
  
  -- Actually, simpler: use Wbtw. 
  -- By Collinear.wbtw_or_wbtw_or_wbtw on {F, a, b}, one is between the other two.
  -- Similarly for other triples.
  
  -- Let's do explicit case analysis.
  
  -- Case 1: F is between two of {a, b, c}
  -- Case 2: One of {a, b, c} is between F and another of {a, b, c}
  -- Case 3: etc.
  
  sorry

end
