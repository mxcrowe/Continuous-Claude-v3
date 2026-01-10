import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical InnerProductSpace

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Key helper
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

def SameSideOf (F x z : Plane) : Prop :=
  Wbtw ℝ F x z ∨ Wbtw ℝ F z x ∨ x = F ∨ z = F

lemma dist_le_max_of_same_side {F x z : Plane} (h : SameSideOf F x z) :
    dist x z ≤ max (dist F x) (dist F z) := by
  rcases h with h_wbtw | h_wbtw | rfl | rfl
  · have h_sum := Wbtw.dist_add_dist h_wbtw
    have h1 : dist x z ≤ dist F z := by
      rw [dist_comm F x] at h_sum
      linarith [dist_nonneg (x := x) (y := F)]
    exact le_max_of_le_right h1
  · have h_sum := Wbtw.dist_add_dist h_wbtw
    have h1 : dist x z ≤ dist F x := by
      rw [dist_comm F z, dist_comm z x] at h_sum
      linarith [dist_nonneg (x := z) (y := F)]
    exact le_max_of_le_left h1
  · -- x = F, so dist F z ≤ max 0 (dist F z)
    simp only [dist_self]
    exact le_max_right 0 (dist F z)
  · -- z = F, so dist x F ≤ max (dist F x) 0
    simp only [dist_self, dist_comm x F]
    exact le_max_left (dist F x) 0

-- Collinearity helper: points on L are collinear
lemma collinear_of_subset_affineSubspace {L : AffineSubspace ℝ Plane} {S : Set Plane}
    (hS : S ⊆ L) [Nonempty L] [FiniteDimensional ℝ L.direction] :
    Collinear ℝ S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact collinear_empty ℝ Plane
  · rw [collinear_iff_of_mem hx₀]
    -- All differences lie in L.direction
    -- Since L is finite-dimensional, the direction is finite-dimensional
    -- We need to show S - x₀ ⊆ span of some vector
    -- This is true because S ⊆ L and L.direction captures all differences
    have h_dir : L.direction = Submodule.span ℝ (L.direction : Set Plane) := by
      simp
    -- For any x, y ∈ L, x - y ∈ L.direction
    have h_in_dir : ∀ y ∈ S, y -ᵥ x₀ ∈ L.direction := fun y hy =>
      AffineSubspace.vsub_mem_direction (hS hy) (hS hx₀)
    -- Since L.direction is 1-dimensional (for a line), all vectors are scalar multiples of a basis
    -- Actually, we don't know L is a line here. Let me assume finite-dimensionality is enough.
    -- Collinearity just means the set is contained in some affine subspace of dimension ≤ 1.
    -- Since S ⊆ L and L is an affine subspace, S is collinear iff dim(vectorSpan S) ≤ 1.
    -- For any subset of an affine subspace, the vectorSpan is contained in the direction.
    -- So if L.direction has dim ≤ 1, then S is collinear.
    -- But we don't have that hypothesis here.
    sorry

-- Let's just prove the main result directly, deferring collinearity
lemma exists_pair_close_main {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  have h_proj_lt : ∀ t ∈ L, dist F t < dist p t := fun t ht => dist_proj_lt_dist' ht hp_off
  
  -- The key insight: among {a, b, c} on L, at least one pair (x, z) satisfies
  -- dist(x, z) ≤ dist(F, z) (when x is on the segment [F, z])
  -- Combined with dist(F, z) < dist(p, z), we get dist(x, z) < dist(p, z)
  
  -- Strategy: use Wbtw to find such a pair
  -- 
  -- On a line, for any 4 points F, a, b, c, there's an ordering.
  -- WLOG say the order is a ≤ F ≤ b ≤ c (or some permutation)
  -- Then b is between F and c, so dist(b, c) ≤ dist(F, c) < dist(p, c). ✓
  -- 
  -- The question is how to find this pair programmatically.
  
  -- Approach: check all pairs and use decidability... but we need to avoid sorry.
  
  -- Alternative: use the fact that among {F, a, b, c}, one is "innermost" 
  -- relative to the convex hull. But that's overkill for 1D.
  
  -- Simple approach: case on which of a, b, c is closest to F (or equals F)
  -- Let that be x. Then pick z to be one of the other two.
  -- Since x is closest to F, and {x, z} are on L with F also on L,
  -- we have Wbtw ℝ F x z or Wbtw ℝ x F z, and in the first case we're done.
  
  -- Actually, the closest to F might still be on the "wrong side" relative to others.
  -- Let me think again...
  
  -- Concrete approach: parameterize by distance to F
  let da := dist F a
  let db := dist F b
  let dc := dist F c
  
  -- If any of a, b, c equals F, that gives us a pair immediately
  by_cases haF : a = F
  · use b, c
    refine ⟨Set.mem_insert_of_mem a (Set.mem_insert_self b _),
            Set.mem_insert_of_mem a (Set.mem_insert_of_mem b (Set.mem_singleton c)),
            hbc, ?_⟩
    calc dist b c ≤ max (dist F b) (dist F c) := by
            -- b, c are both distinct from F (since a = F and a ≠ b, a ≠ c)
            -- Need to show they're on the same side of F... not immediately clear
            sorry
      _ ≤ dist F c + dist F b := le_max_iff.mp (le_refl _) |> fun _ => by linarith [dist_nonneg, dist_nonneg]
      _ < dist p c := by sorry -- need to show dist F b < dist p c - dist F c, unclear
  · sorry

end
