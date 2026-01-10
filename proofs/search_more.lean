import Mathlib

-- Betweenness lemmas
#check @Wbtw
#check @Sbtw
#check @wbtw_iff_same_ray_or_eq
#check @Wbtw.dist_le_dist

-- Distance and collinearity
#check @collinear_iff_dist_eq_abs_smul
#check @dist_mul_of_same_ray
#check @dist_add_dist_eq_of_wbtw

-- Orthogonal projection
#check @EuclideanGeometry.orthogonalProjection_mem
#check @EuclideanGeometry.dist_orthogonalProjection_eq_infDist
#check @EuclideanGeometry.inner_vsub_orthogonalProjection_mem_direction_le

-- Line segment
#check @segment_eq_image'
#check @left_mem_segment
#check @right_mem_segment
