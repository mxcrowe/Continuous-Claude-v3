import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- The key lemma we need
lemma exists_pair_close {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  -- Use native_decide or some automated reasoning
  -- The key facts:
  -- 1. F = proj(L, p) is on L
  -- 2. For all t ∈ L: dist(F, t) < dist(p, t) (Pythagorean)
  -- 3. Among 3 points on a 1D line, at least 2 are on the same side of F
  -- 4. For those 2, one is between F and the other, so dist ≤ dist(F, ·)
  
  -- Since this is a geometric pigeonhole argument that's hard to formalize directly,
  -- let's use interval_cases or a more computational approach
  
  -- The cleanest is to work in coordinates. L is 1-dimensional, so we can parameterize.
  
  -- Get F
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  
  -- Height h > 0
  have h_eq : dist p F = Metric.infDist p L :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist L p
  have hL_closed : IsClosed (L : Set Plane) := AffineSubspace.closed_of_finiteDimensional L
  have h_pos : 0 < dist p F := by
    rw [dist_pos]
    intro hpF
    exact hp_off (hpF ▸ hF_mem)
  
  -- Pythagorean: for any t ∈ L, dist(p, t)² = dist(F, t)² + h²
  have pythag : ∀ t ∈ L, dist p t ^ 2 = dist F t ^ 2 + dist p F ^ 2 := fun t ht => by
    have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
      (s := L) t ht
    simp only [sq] at h ⊢
    rw [dist_comm t p, dist_comm t F]
    convert h using 1
    ring
  
  -- Key: dist(F, t) < dist(p, t) for t ≠ F
  have proj_lt : ∀ t ∈ L, t ≠ F → dist F t < dist p t := fun t ht htF => by
    have h_pythag := pythag t ht
    have h_Ft_pos : 0 < dist F t := dist_pos.mpr htF
    have h_pt_pos : 0 < dist p t := dist_pos.mpr (fun hpt => hp_off (hpt ▸ ht))
    nlinarith [sq_nonneg (dist F t), sq_nonneg (dist p t), sq_pos_of_pos h_pos, sq_pos_of_pos h_Ft_pos]
  
  -- Also when t = F: dist(F, F) = 0 < h = dist(p, F)
  have proj_lt_F : dist F F < dist p F := by simp [h_pos]
  
  -- Now the pigeonhole argument
  -- We work with signed coordinates on L. Since L.direction is 1-dimensional,
  -- we can pick a basis vector v and express every point as F + t • v.
  
  -- The condition "on the same side of F" means the t values have the same sign.
  -- Among 3 real numbers (t_a, t_b, t_c), at least 2 have the same sign or are 0.
  
  -- Instead of formalizing coordinates, let's use the Wbtw relation.
  -- The key insight: among 3 collinear points, one is between the other two.
  -- And for 4 collinear points {F, a, b, c}, we can find a "good" configuration.
  
  -- Let me try a direct exhaustive approach using by_cases
  
  -- Case: Is any of a, b, c equal to F?
  by_cases haF : a = F
  · -- a = F, so use (b, c). We need dist(b, c) < dist(p, c) or dist(b, c) < dist(p, b)
    -- Since a = F and a ≠ b, a ≠ c, we have F ≠ b, F ≠ c
    have hbF : b ≠ F := hab ∘ (haF ▸ ·)
    have hcF : c ≠ F := hac ∘ (haF ▸ ·)
    -- F, b, c are distinct points on L
    -- Among {F, b, c}, one is between the other two (since collinear)
    have h_col_Fbc : Collinear ℝ ({F, b, c} : Set Plane) := by
      rw [Set.insert_comm, Set.pair_comm]
      have h_sub : ({b, c, F} : Set Plane) ⊆ L := by
        intro x hx
        simp only [mem_insert_iff, mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      sorry -- collinearity of subset of L
    have h_btw := Collinear.wbtw_or_wbtw_or_wbtw h_col_Fbc
    rcases h_btw with h | h | h
    · -- Wbtw ℝ F b c: b between F and c
      use b, c
      refine ⟨mem_insert_of_mem _ (mem_insert_self _ _),
              mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _)), hbc, ?_⟩
      have h_sum := Wbtw.dist_add_dist h
      have h_bc_le : dist b c ≤ dist F c := by linarith [dist_nonneg (x := F) (y := b)]
      calc dist b c ≤ dist F c := h_bc_le
        _ < dist p c := proj_lt c hc hcF
    · -- Wbtw ℝ b c F: c between b and F
      use b, c
      refine ⟨mem_insert_of_mem _ (mem_insert_self _ _),
              mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _)), hbc, ?_⟩
      have h_sum := Wbtw.dist_add_dist h
      have h_bc_le : dist b c ≤ dist b F := by linarith [dist_nonneg (x := c) (y := F)]
      rw [dist_comm b F] at h_bc_le
      calc dist b c ≤ dist F b := h_bc_le
        _ < dist p b := proj_lt b hb hbF
    · -- Wbtw ℝ c F b: F between c and b
      -- c and b are on opposite sides of F
      -- We still need to find a good pair...
      -- Actually, this means dist(c, b) = dist(c, F) + dist(F, b)
      -- So dist(c, b) > max(dist(c, F), dist(F, b))
      -- But we need dist < dist(p, ·) for some choice
      -- dist(c, b) vs dist(p, b): dist(p, b)² = dist(F, b)² + h²
      --                          dist(c, b)² = (dist(c, F) + dist(F, b))²
      -- Not directly comparable without more info about dist(c, F)
      -- But wait, we need ANY pair from {a, b, c}, not just (b, c)!
      -- Since a = F, let's try (a, b) = (F, b) or (a, c) = (F, c)
      use a, b
      subst haF
      refine ⟨mem_insert_self _ _, mem_insert_of_mem _ (mem_insert_self _ _), hbF.symm, ?_⟩
      -- Need dist(F, b) < dist(p, b), which is exactly proj_lt
      exact proj_lt b hb hbF
  · by_cases hbF : b = F
    · use a, c
      refine ⟨mem_insert_self _ _, mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _)), hac, ?_⟩
      -- Similar to above: need to find which pair works
      -- Since b = F, we can try (a, F) or (F, c) or (a, c)
      -- For (a, c), we need dist(a, c) < dist(p, c) or dist(a, c) < dist(p, a)
      -- This requires knowing the position of a, c relative to F = b
      sorry
    · by_cases hcF : c = F
      · use a, b
        refine ⟨mem_insert_self _ _, mem_insert_of_mem _ (mem_insert_self _ _), hab, ?_⟩
        sorry
      · -- None of a, b, c equal F, so all 4 points are distinct
        -- Use betweenness on {F, a, b, c}
        sorry

end
