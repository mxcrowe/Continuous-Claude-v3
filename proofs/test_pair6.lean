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
-- This is formalized as: either Wbtw ℝ F x z (x between F and z) or Wbtw ℝ F z x (z between F and x) or x = F or z = F
def SameSideOf (F x z : Plane) : Prop :=
  Wbtw ℝ F x z ∨ Wbtw ℝ F z x ∨ x = F ∨ z = F

-- Key property: if x, z are on the same side of F, then dist(x, z) ≤ max(dist(F, x), dist(F, z))
lemma dist_le_max_of_same_side {F x z : Plane} (h : SameSideOf F x z) :
    dist x z ≤ max (dist F x) (dist F z) := by
  rcases h with h_wbtw | h_wbtw | rfl | rfl
  · -- Wbtw ℝ F x z: x is between F and z, so dist(x, z) = dist(F, z) - dist(F, x) ≤ dist(F, z)
    have h_sum := Wbtw.dist_add_dist h_wbtw
    have h1 : dist x z ≤ dist F z := by
      rw [dist_comm F x] at h_sum
      linarith [dist_nonneg (x := x) (y := F)]
    exact le_max_of_le_right h1
  · -- Wbtw ℝ F z x: z is between F and x, so dist(x, z) = dist(F, x) - dist(F, z) ≤ dist(F, x)
    have h_sum := Wbtw.dist_add_dist h_wbtw
    have h1 : dist x z ≤ dist F x := by
      rw [dist_comm F z, dist_comm z x] at h_sum
      linarith [dist_nonneg (x := z) (y := F)]
    exact le_max_of_le_left h1
  · -- x = F
    simp [dist_comm]
    exact le_max_right _ _
  · -- z = F
    simp
    exact le_max_left _ _

-- Pigeonhole: among 3 points on a 1D line through F, at least 2 are on the same side of F
-- This requires knowing the line is 1-dimensional.
-- Let's use a simpler formulation: among any 3 points collinear with F, at least 2 satisfy SameSideOf
lemma pigeonhole_same_side {F a b c : Plane} (h_col : Collinear ℝ ({F, a, b, c} : Set Plane))
    (haF : a ≠ F) (hbF : b ≠ F) (hcF : c ≠ F)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    SameSideOf F a b ∨ SameSideOf F a c ∨ SameSideOf F b c := by
  -- On a 1D line, any 4 points have a linear ordering (up to direction)
  -- The key is: among {a, b, c}, at least 2 are on the same side of F
  -- 
  -- Use Collinear.wbtw_or_wbtw_or_wbtw on various triples
  -- 
  -- Consider {F, a, b}: one of Wbtw ℝ F a b, Wbtw ℝ a b F, Wbtw ℝ b F a holds
  have h_Fab : Collinear ℝ ({F, a, b} : Set Plane) := by
    apply Collinear.subset h_col
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> tauto
  have h_btw_Fab := Collinear.wbtw_or_wbtw_or_wbtw h_Fab
  
  -- Similar for {F, a, c} and {F, b, c}
  have h_Fac : Collinear ℝ ({F, a, c} : Set Plane) := by
    apply Collinear.subset h_col
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> tauto
  have h_btw_Fac := Collinear.wbtw_or_wbtw_or_wbtw h_Fac
  
  have h_Fbc : Collinear ℝ ({F, b, c} : Set Plane) := by
    apply Collinear.subset h_col
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> tauto
  have h_btw_Fbc := Collinear.wbtw_or_wbtw_or_wbtw h_Fbc
  
  -- Now case analysis on the betweenness relations
  -- The key observation: 
  -- - If Wbtw ℝ F a b or Wbtw ℝ F b a: SameSideOf F a b ✓
  -- - If Wbtw ℝ a F b: a and b are on opposite sides of F
  --   Then check {F, a, c} and {F, b, c}
  
  rcases h_btw_Fab with h1 | h1 | h1
  · -- Wbtw ℝ F a b
    left; left; exact h1
  · -- Wbtw ℝ a b F: b is between a and F, so F and a are on opposite sides of b
    -- This means Wbtw ℝ F b a (going F → b → a), which is SameSideOf F b a... wait no
    -- Wbtw ℝ a b F means b ∈ segment [a, F]
    -- So a is on the opposite side of F from... nothing, a is at one end
    -- Let me reconsider: if Wbtw ℝ a b F, then going from a to F, we pass through b
    -- So the order is: a --- b --- F
    -- Then Wbtw ℝ F b a also holds? No, Wbtw ℝ F b a would mean b ∈ segment [F, a], which is the same.
    -- So Wbtw is symmetric in endpoints? Let me check.
    -- Actually Wbtw ℝ x y z means y ∈ segment [x, z] = segment [z, x]
    -- So Wbtw ℝ a b F ↔ Wbtw ℝ F b a
    -- Hmm, but Collinear.wbtw_or_wbtw_or_wbtw gives disjoint cases...
    -- Let me check the exact statement.
    -- Looking at the output from earlier:
    -- `Collinear.wbtw_or_wbtw_or_wbtw h_col : Wbtw R x y z ∨ Wbtw R y z x ∨ Wbtw R z x y`
    -- For {F, a, b}, this is: Wbtw ℝ F a b ∨ Wbtw ℝ a b F ∨ Wbtw ℝ b F a
    -- Case 2: Wbtw ℝ a b F means b ∈ segment [a, F], order is a--b--F
    -- So a and F are "outer" points with b in between
    -- Neither a nor b are on the same side of F... wait, what about the third point c?
    -- If a--b--F is the order, then:
    --   - If c is between a and F (anywhere), we need to check cases
    --   - Consider {F, b, c}: the order could be F--b--c, b--F--c, b--c--F, etc.
    -- This is getting complicated. Let me try omega or decide.
    sorry
  · -- Wbtw ℝ b F a
    sorry

-- Main lemma
lemma exists_pair_close_final {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  sorry

end
