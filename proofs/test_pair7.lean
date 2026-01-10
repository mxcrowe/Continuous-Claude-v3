import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical InnerProductSpace

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

-- Same side: x and z are on the same side of F on a 1D line
def SameSideOf (F x z : Plane) : Prop :=
  Wbtw ℝ F x z ∨ Wbtw ℝ F z x ∨ x = F ∨ z = F

-- Key property: if x, z are on the same side of F, then dist(x, z) ≤ max(dist(F, x), dist(F, z))
lemma dist_le_max_of_same_side {F x z : Plane} (h : SameSideOf F x z) :
    dist x z ≤ max (dist F x) (dist F z) := by
  rcases h with h_wbtw | h_wbtw | rfl | rfl
  · -- Wbtw ℝ F x z: x is between F and z
    have h_sum := Wbtw.dist_add_dist h_wbtw
    have h1 : dist x z ≤ dist F z := by
      rw [dist_comm F x] at h_sum
      linarith [dist_nonneg (x := x) (y := F)]
    exact le_max_of_le_right h1
  · -- Wbtw ℝ F z x: z is between F and x
    have h_sum := Wbtw.dist_add_dist h_wbtw
    have h1 : dist x z ≤ dist F x := by
      rw [dist_comm F z, dist_comm z x] at h_sum
      linarith [dist_nonneg (x := z) (y := F)]
    exact le_max_of_le_left h1
  · -- x = F: dist F z ≤ max (dist F F) (dist F z) = max 0 (dist F z) = dist F z
    simp only [dist_self, ge_iff_le, zero_le, max_eq_right]
  · -- z = F: dist x F ≤ max (dist F x) (dist F F) = max (dist F x) 0 = dist F x
    simp only [dist_self, ge_iff_le, zero_le, max_eq_left, dist_comm]

-- Collinear subsets are collinear
lemma collinear_subset {S T : Set Plane} (hST : S ⊆ T) (hT : Collinear ℝ T) : Collinear ℝ S :=
  Collinear.subset hT hST

-- Main lemma: among 3 points on L with projection F, we can find a good pair
-- The proof uses Wbtw betweenness directly
lemma exists_pair_close_final {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  have h_proj_lt : ∀ t ∈ L, dist F t < dist p t := fun t ht => dist_proj_lt_dist' ht hp_off
  
  -- All points are on L, so {a, b, c} is collinear
  -- And {F, a, b, c} is collinear (all on L)
  have h_abc_sub_L : ({a, b, c} : Set Plane) ⊆ L := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  
  have h_col_abc : Collinear ℝ ({a, b, c} : Set Plane) := by
    rw [collinear_iff_of_mem (Set.mem_insert a _)]
    -- All are on the 1-dimensional L, so collinear
    -- This requires showing that L.direction is 1-dimensional, i.e., all differences are scalar multiples
    have h_dir : ∀ x y : Plane, x ∈ L → y ∈ L → ∃ t : ℝ, x -ᵥ y ∈ L.direction := fun x y hx hy =>
      ⟨1, AffineSubspace.vsub_mem_direction hx hy⟩
    -- Since L.direction is 1-dimensional, there's a basis vector v
    -- All differences are scalar multiples of v
    sorry
  
  -- Use betweenness: among {a, b, c}, one is between the other two
  have h_btw := Collinear.wbtw_or_wbtw_or_wbtw h_col_abc
  
  rcases h_btw with h | h | h
  · -- Wbtw ℝ a b c: b is between a and c
    -- dist(a, b) ≤ dist(a, c), dist(b, c) ≤ dist(a, c)
    have hab_le : dist a b ≤ dist a c := by
      have h_sum := Wbtw.dist_add_dist h
      linarith [dist_nonneg (x := b) (y := c)]
    have hbc_le : dist b c ≤ dist a c := by
      have h_sum := Wbtw.dist_add_dist h
      linarith [dist_nonneg (x := a) (y := b)]
    -- Now we have two candidates: (a, b) with dist ≤ dist(a, c), (b, c) with dist ≤ dist(a, c)
    -- We need dist < dist(p, z) for some z
    -- Since dist(F, c) < dist(p, c) and dist(F, a) < dist(p, a),
    -- at least one of dist(b, c) < dist(p, c) or dist(a, b) < dist(p, a) should work
    -- ... but this isn't guaranteed without knowing the relative positions
    
    -- Better approach: pick z = argmax dist(F, ·) over {a, c} (the outer points)
    -- Then x = b satisfies dist(b, z) ≤ dist(a, c) ≤ ... 
    -- Still not directly helpful.
    
    -- Actually, the right approach:
    -- Either dist(b, c) < dist(p, c) or dist(a, b) < dist(p, a)
    -- Why? Because:
    -- dist(b, c) ≤ dist(F, c) OR dist(a, b) ≤ dist(F, a) (depending on where F is)
    -- And dist(F, c) < dist(p, c), dist(F, a) < dist(p, a)
    
    -- Case analysis on where F is relative to the segment [a, c]
    by_cases hF_btw : Wbtw ℝ a F c
    · -- F is between a and c, so F is on the segment [a, c]
      -- Either F is between a and b, or F is between b and c
      -- In either case, we get a good pair
      sorry
    · -- F is not between a and c
      -- So either Wbtw ℝ F a c (a is between F and c) or Wbtw ℝ a c F (c is between a and F)
      sorry
  · -- Wbtw ℝ b c a: c is between b and a
    sorry
  · -- Wbtw ℝ c a b: a is between c and b
    sorry

end
