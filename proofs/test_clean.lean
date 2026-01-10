import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Pythagorean theorem wrapper
lemma pythag_on_L {L : AffineSubspace ℝ Plane} {p t : Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection]
    (ht : t ∈ L) :
    let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
    dist t p ^ 2 = dist t F ^ 2 + dist p F ^ 2 := by
  intro F
  have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s := L) p ht
  simp only [sq]
  convert h using 1

-- Key lemma: projection is closer
lemma dist_proj_lt {L : AffineSubspace ℝ Plane} {p t : Plane}
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection]
    (ht : t ∈ L) (hp_off : p ∉ L) :
    let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
    dist F t < dist p t := by
  intro F
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  have h_pF_pos : 0 < dist p F := dist_pos.mpr (fun hpF => hp_off (hpF ▸ hF_mem))
  have h_pythag := pythag_on_L (L := L) (p := p) ht
  rw [dist_comm t p, dist_comm t F] at h_pythag
  -- h_pythag : dist p t ^ 2 = dist F t ^ 2 + dist p F ^ 2
  have h_pt_pos : 0 < dist p t := dist_pos.mpr (fun hpt => hp_off (hpt ▸ ht))
  nlinarith [sq_nonneg (dist F t), sq_pos_of_pos h_pF_pos, sq_pos_of_pos h_pt_pos]

-- Collinearity of points on L
lemma collinear_of_mem_L {L : AffineSubspace ℝ Plane} {a b c : Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) :
    Collinear ℝ ({a, b, c} : Set Plane) := by
  -- All points in an affine subspace are collinear (the set is contained in an affine line)
  have h_sub : ({a, b, c} : Set Plane) ⊆ L := by
    intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
  exact collinear_of_subset_affineSubspace h_sub

-- The main lemma
lemma exists_pair_close {a b c p : Plane} {L : AffineSubspace ℝ Plane}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hp_off : p ∉ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    [Nonempty L] [FiniteDimensional ℝ L.direction] [L.direction.HasOrthogonalProjection] :
    ∃ x z, x ∈ ({a, b, c} : Set Plane) ∧ z ∈ ({a, b, c} : Set Plane) ∧ x ≠ z ∧
      dist x z < dist p z := by
  let F : Plane := ↑(EuclideanGeometry.orthogonalProjection L p)
  have hF_mem : F ∈ L := EuclideanGeometry.orthogonalProjection_mem p
  
  -- Handle case when F ∈ {a, b, c}
  by_cases haF : a = F
  · -- Use dist(F, b) < dist(p, b)
    use F, b
    rw [← haF]
    exact ⟨mem_insert_self a _, mem_insert_of_mem _ (mem_insert_self b _), 
           (haF ▸ hab), dist_proj_lt hb hp_off⟩
  · by_cases hbF : b = F
    · use F, a
      rw [← hbF]
      refine ⟨mem_insert_of_mem _ (mem_insert_self b _), mem_insert_self a _, 
             fun h => hbF (h.symm ▸ haF.symm |> fun x => (hab x).elim), ?_⟩
      rw [dist_comm F a]
      exact dist_proj_lt ha hp_off
    · by_cases hcF : c = F
      · use F, a
        rw [← hcF]
        refine ⟨mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton c)), mem_insert_self a _, 
               hac.symm, ?_⟩
        rw [dist_comm F a]
        exact dist_proj_lt ha hp_off
      · -- F ∉ {a, b, c}, so all 4 points are distinct
        -- {a, b, c} are collinear, so by Wbtw one is between the others
        have h_col : Collinear ℝ ({a, b, c} : Set Plane) := collinear_of_mem_L ha hb hc
        have h_btw := Collinear.wbtw_or_wbtw_or_wbtw h_col
        
        -- Also {F, a, b, c} are collinear
        have h_col4 : Collinear ℝ ({F, a, b, c} : Set Plane) := collinear_of_mem_L hF_mem ha hb ▸
          collinear_insert_of_mem_affineSpan_pair (s := L) ?_ -- needs work
        
        -- Case analysis based on betweenness of {a, b, c}
        rcases h_btw with h_wbtw | h_wbtw | h_wbtw
        · -- Wbtw ℝ a b c: b is between a and c
          -- dist(a, b) ≤ dist(a, c), dist(b, c) ≤ dist(a, c)
          have h_sum := Wbtw.dist_add_dist h_wbtw
          have h_ab_le : dist a b ≤ dist a c := by linarith [dist_nonneg (x := b) (y := c)]
          have h_bc_le : dist b c ≤ dist a c := by linarith [dist_nonneg (x := a) (y := b)]
          
          -- Now consider {F, a, c}. One of F, a, c is between the other two.
          have h_col_Fac : Collinear ℝ ({F, a, c} : Set Plane) := collinear_of_mem_L hF_mem ha hc
          have h_btw_Fac := Collinear.wbtw_or_wbtw_or_wbtw h_col_Fac
          
          rcases h_btw_Fac with h2 | h2 | h2
          · -- Wbtw ℝ F a c: a between F and c → dist(a, c) ≤ dist(F, c) < dist(p, c)
            have h_ac_le : dist a c ≤ dist F c := by
              have h_sum2 := Wbtw.dist_add_dist h2
              linarith [dist_nonneg (x := F) (y := a)]
            use b, c
            refine ⟨mem_insert_of_mem _ (mem_insert_self b _), 
                   mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton c)), hbc, ?_⟩
            calc dist b c ≤ dist a c := h_bc_le
              _ ≤ dist F c := h_ac_le
              _ < dist p c := dist_proj_lt hc hp_off
          · -- Wbtw ℝ a c F: c between a and F → dist(a, c) ≤ dist(a, F) < dist(p, a)
            have h_ac_le : dist a c ≤ dist a F := by
              have h_sum2 := Wbtw.dist_add_dist h2
              linarith [dist_nonneg (x := c) (y := F)]
            rw [dist_comm a F] at h_ac_le
            use b, a
            refine ⟨mem_insert_of_mem _ (mem_insert_self b _), mem_insert_self a _, hab.symm, ?_⟩
            calc dist b a = dist a b := dist_comm b a
              _ ≤ dist a c := h_ab_le
              _ ≤ dist F a := h_ac_le
              _ < dist p a := dist_proj_lt ha hp_off
          · -- Wbtw ℝ c F a: F between c and a
            -- c and a are on opposite sides of F
            -- Try {F, b, c} instead
            have h_col_Fbc : Collinear ℝ ({F, b, c} : Set Plane) := collinear_of_mem_L hF_mem hb hc
            have h_btw_Fbc := Collinear.wbtw_or_wbtw_or_wbtw h_col_Fbc
            rcases h_btw_Fbc with h3 | h3 | h3
            · -- Wbtw ℝ F b c: b between F and c → dist(b, c) ≤ dist(F, c) < dist(p, c)
              have h_bc_le2 : dist b c ≤ dist F c := by
                have h_sum3 := Wbtw.dist_add_dist h3
                linarith [dist_nonneg (x := F) (y := b)]
              use b, c
              refine ⟨mem_insert_of_mem _ (mem_insert_self b _), 
                     mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton c)), hbc, ?_⟩
              exact lt_of_le_of_lt h_bc_le2 (dist_proj_lt hc hp_off)
            · -- Wbtw ℝ b c F: c between b and F → dist(b, c) ≤ dist(b, F) < dist(p, b)
              have h_bc_le2 : dist b c ≤ dist b F := by
                have h_sum3 := Wbtw.dist_add_dist h3
                linarith [dist_nonneg (x := c) (y := F)]
              rw [dist_comm b F] at h_bc_le2
              use c, b
              refine ⟨mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton c)),
                     mem_insert_of_mem _ (mem_insert_self b _), hbc.symm, ?_⟩
              rw [dist_comm c b]
              exact lt_of_le_of_lt h_bc_le2 (dist_proj_lt hb hp_off)
            · -- Wbtw ℝ c F b: F between c and b
              -- Now we have: c - F - a (from h2), c - F - b (from h3)
              -- So c is on one side of F, both a and b are on the other side
              -- Therefore dist(a, b) ≤ dist(F, b) or dist(a, b) ≤ dist(F, a)
              -- depending on which of a, b is closer to F
              have h_col_Fab : Collinear ℝ ({F, a, b} : Set Plane) := collinear_of_mem_L hF_mem ha hb
              have h_btw_Fab := Collinear.wbtw_or_wbtw_or_wbtw h_col_Fab
              rcases h_btw_Fab with h4 | h4 | h4
              · -- Wbtw ℝ F a b: a between F and b
                have h_ab_le2 : dist a b ≤ dist F b := by
                  have h_sum4 := Wbtw.dist_add_dist h4
                  linarith [dist_nonneg (x := F) (y := a)]
                use a, b
                refine ⟨mem_insert_self a _, mem_insert_of_mem _ (mem_insert_self b _), hab, ?_⟩
                exact lt_of_le_of_lt h_ab_le2 (dist_proj_lt hb hp_off)
              · -- Wbtw ℝ a b F: b between a and F
                have h_ab_le2 : dist a b ≤ dist a F := by
                  have h_sum4 := Wbtw.dist_add_dist h4
                  linarith [dist_nonneg (x := b) (y := F)]
                rw [dist_comm a F] at h_ab_le2
                use b, a
                refine ⟨mem_insert_of_mem _ (mem_insert_self b _), mem_insert_self a _, hab.symm, ?_⟩
                rw [dist_comm b a]
                exact lt_of_le_of_lt h_ab_le2 (dist_proj_lt ha hp_off)
              · -- Wbtw ℝ b F a: F between b and a
                -- But we have c - F - a and c - F - b, which means both a and b 
                -- are on the opposite side of F from c
                -- And b - F - a means... wait, this is contradictory with c - F - b?
                -- If c - F - b (Wbtw c F b), then F is between c and b
                -- If b - F - a (Wbtw b F a), then F is between b and a
                -- These can coexist: c ... F ... b and b ... F ... a doesn't make sense
                -- Actually Wbtw c F b means F ∈ [c, b], and Wbtw b F a means F ∈ [b, a]
                -- This implies F = b (the common point), contradicting hbF
                exfalso
                -- h3: Wbtw ℝ c F b means F ∈ segment [c, b]
                -- h4: Wbtw ℝ b F a means F ∈ segment [b, a]
                -- From h3: ∃ t ∈ [0, 1], F = (1-t)c + tb
                -- From h4: ∃ s ∈ [0, 1], F = (1-s)b + sa
                -- If F ≠ b, then t ∈ (0, 1] and s ∈ [0, 1)
                -- Combined: F = (1-t)c + tb = (1-s)b + sa
                -- This means c, a, b, F are not in general position...
                -- Actually this case might be impossible. Let me use sorry for now.
                sorry
        · -- Wbtw ℝ b c a: c between b and a
          sorry
        · -- Wbtw ℝ c a b: a between c and b
          sorry

end
