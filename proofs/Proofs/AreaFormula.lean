import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def lineThrough (p q : Plane) : AffineSubspace ℝ Plane := affineSpan ℝ {p, q}

-- Key: Plane is 2-dimensional
instance : Fact (Module.finrank ℝ Plane = 2) := ⟨finrank_euclideanSpace_fin⟩

-- The standard orientation on Plane
def stdOrientation : Orientation ℝ Plane (Fin 2) :=
  (OrthonormalBasis.fromOrthonormalSet
    (EuclideanSpace.orthonormal_basisFun (Fin 2) ℝ).orthonormal
    (by simp [finrank_euclideanSpace_fin])).toBasis.orientation

-- Key: lineThrough x z = L when x ≠ z, both in L, and L is 1-dimensional
lemma lineThrough_eq_of_mem_finrank_one {L : AffineSubspace ℝ Plane}
    {x z : Plane} (hx : x ∈ L) (hz : z ∈ L) (hxz : x ≠ z)
    [Nonempty L] [FiniteDimensional ℝ L.direction]
    (h_dim : Module.finrank ℝ L.direction = 1) :
    lineThrough x z = L := by
  unfold lineThrough
  apply le_antisymm
  · -- affineSpan {x, z} ≤ L
    apply affineSpan_le.mpr
    intro p' hp'
    simp only [mem_insert_iff, mem_singleton_iff] at hp'
    rcases hp' with rfl | rfl <;> assumption
  · -- L ≤ affineSpan {x, z}
    -- affineSpan {x, z} has direction of dimension 1 (since x ≠ z)
    have h_dir_xz : Module.finrank ℝ (affineSpan ℝ ({x, z} : Set Plane)).direction = 1 := by
      rw [direction_affineSpan]
      have h_indep : AffineIndependent ℝ ![x, z] := affineIndependent_of_ne ℝ hxz
      have h_range : Set.range ![x, z] = {x, z} := by
        simp only [Matrix.range_cons_cons_empty]
      have h_card : Fintype.card (Fin 2) = 1 + 1 := rfl
      have h_finrank := AffineIndependent.finrank_vectorSpan h_indep h_card
      rw [h_range] at h_finrank
      exact h_finrank
    have h_le : affineSpan ℝ ({x, z} : Set Plane) ≤ L := by
      apply affineSpan_le.mpr
      intro p' hp'
      simp only [mem_insert_iff, mem_singleton_iff] at hp'
      rcases hp' with rfl | rfl <;> assumption
    have h_dir_le : (affineSpan ℝ ({x, z} : Set Plane)).direction ≤ L.direction := by
      intro v hv
      rw [AffineSubspace.direction_eq_vectorSpan] at hv
      rw [AffineSubspace.direction_eq_vectorSpan]
      exact vectorSpan_mono ℝ (affineSpan_le.mp h_le) hv
    have h_dir_eq : (affineSpan ℝ ({x, z} : Set Plane)).direction = L.direction := by
      apply eq_of_le_of_finrank_eq h_dir_le
      rw [h_dir_xz, h_dim]
    have hx_in_xz : x ∈ affineSpan ℝ ({x, z} : Set Plane) :=
      subset_affineSpan ℝ _ (mem_insert_self x {z})
    rw [AffineSubspace.eq_iff_direction_eq_of_mem hx_in_xz hx]
    exact h_dir_eq

-- Key identity: inner² + areaForm² = ‖a‖² * ‖b‖²
lemma areaForm_sq_eq {o : Orientation ℝ Plane (Fin 2)} (a b : Plane) :
    (o.areaForm a b) ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - inner (𝕜 := ℝ) a b ^ 2 := by
  have h := o.inner_sq_add_areaForm_sq a b
  linarith [sq_nonneg (o.areaForm a b), sq_nonneg (inner (𝕜 := ℝ) a b)]

-- The perpendicular distance from a point to a line through origin with direction d
-- equals |areaForm d v| / ‖d‖ where v is the point vector
lemma perp_dist_eq_areaForm_div_norm {o : Orientation ℝ Plane (Fin 2)} {d v : Plane}
    (hd : d ≠ 0) : ‖v - (inner (𝕜 := ℝ) v d / ‖d‖^2) • d‖ = |o.areaForm d v| / ‖d‖ := by
  have hd_norm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hd_sq_pos : 0 < ‖d‖^2 := sq_pos_of_pos hd_norm_pos

  set proj := (inner (𝕜 := ℝ) v d / ‖d‖^2) • d with hproj_def
  set perp := v - proj with hperp_def

  -- ‖perp‖² = ‖v‖² - (inner v d)² / ‖d‖²
  have h_pythag : ‖perp‖^2 = ‖v‖^2 - (inner (𝕜 := ℝ) v d)^2 / ‖d‖^2 := by
    rw [hperp_def]
    have h1 : ‖v - proj‖^2 = ‖v‖^2 - 2 * inner (𝕜 := ℝ) v proj + ‖proj‖^2 := by
      rw [sq_norm_sub_eq_sq_norm_add_sq_norm_sub_two_inner]
      ring
    have h_proj_inner : inner (𝕜 := ℝ) v proj = (inner (𝕜 := ℝ) v d)^2 / ‖d‖^2 := by
      rw [hproj_def]
      rw [inner_smul_right]
      ring_nf
      rw [real_inner_comm v d]
      ring_nf
      rfl
    have h_proj_norm : ‖proj‖^2 = (inner (𝕜 := ℝ) v d)^2 / ‖d‖^2 := by
      rw [hproj_def]
      rw [norm_smul]
      simp only [Real.norm_eq_abs]
      rw [sq, abs_mul_self]
      rw [mul_pow, abs_div, abs_sq, sq_abs, div_pow, sq_abs]
      have h2 : ‖d‖ ^ 2 ≠ 0 := ne_of_gt hd_sq_pos
      field_simp
      ring
    rw [h1, h_proj_inner, h_proj_norm]
    ring

  -- Also: ‖perp‖² = |areaForm d v|² / ‖d‖²
  have h_area : ‖perp‖^2 = (o.areaForm d v)^2 / ‖d‖^2 := by
    rw [h_pythag]
    have h_areaForm_sq := o.inner_sq_add_areaForm_sq d v
    have h2 : (o.areaForm d v)^2 = ‖d‖^2 * ‖v‖^2 - (inner (𝕜 := ℝ) d v)^2 := by
      linarith
    rw [h2]
    rw [real_inner_comm d v]
    have h3 : ‖d‖^2 ≠ 0 := ne_of_gt hd_sq_pos
    field_simp
    ring

  have h_perp_nonneg : 0 ≤ ‖perp‖ := norm_nonneg _
  have h_area_div_nonneg : 0 ≤ |o.areaForm d v| / ‖d‖ := div_nonneg (abs_nonneg _) (le_of_lt hd_norm_pos)

  have h_sq_eq : ‖perp‖^2 = (|o.areaForm d v| / ‖d‖)^2 := by
    rw [h_area, div_pow, sq_abs]

  exact sq_eq_sq h_perp_nonneg h_area_div_nonneg |>.mp h_sq_eq

#check perp_dist_eq_areaForm_div_norm
#check lineThrough_eq_of_mem_finrank_one

end
