import Mathlib

-- Search for relevant lemmas

-- For area formula
#check @EuclideanGeometry.oangle_sign_area
#check @Orientation.abs_oangle_eq_abs_arcsin_div_dist_mul_dist

-- For distance to line using cross product
#check @EuclideanGeometry.dist_div_eq_sin_abs_oangle
#check @EuclideanGeometry.dist_eq_mul_dist_sin_angle

-- For collinearity and betweenness
#check @Wbtw.dist_add_dist
#check @Sbtw.dist_lt_dist
#check @EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq

-- For affine subspaces
#check @AffineSubspace.coe_direction_eq_vsub_set_right
#check @affineSpan_pair

-- For inner product and projections
#check @inner_vsub_orthogonalProjection_le
#check @orthogonalProjection_eq_self_iff
