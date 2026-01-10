import Mathlib

#check @Wbtw.wbtw_or_wbtw_or_eq
#check @Wbtw.left_ne_right_of_ne_left
#check @wbtw_or_wbtw_or_eq_of_wbtw

-- Key insight: if Wbtw a b c (b between a and c) and x ∈ segment [a,b] and x ∈ segment [b,c],
-- then x = b (since the segments only share the endpoint b)

-- Let's try to prove: if Wbtw a b c and Wbtw a x b and Wbtw b x c, then x = b
example {V : Type*} {P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] 
    [PseudoMetricSpace P] [NormedAddTorsor V P]
    {a b c x : P} (h_abc : Wbtw ℝ a b c) (h_axb : Wbtw ℝ a x b) (h_bxc : Wbtw ℝ b x c) : x = b := by
  -- From h_axb, x ∈ segment [a, b]
  -- From h_bxc, x ∈ segment [b, c]
  -- We need to show the intersection is {b}
  -- Use distance: dist a x + dist x b = dist a b and dist b x + dist x c = dist b c
  -- Also dist a b + dist b c = dist a c (from h_abc)
  have d1 := Wbtw.dist_add_dist h_axb
  have d2 := Wbtw.dist_add_dist h_bxc
  have d3 := Wbtw.dist_add_dist h_abc
  -- d1: dist a x + dist x b = dist a b
  -- d2: dist b x + dist x c = dist b c
  -- d3: dist a b + dist b c = dist a c
  -- Note: dist x b = dist b x, so d1 + d2 gives:
  -- dist a x + dist x b + dist b x + dist x c = dist a b + dist b c
  -- dist a x + 2 * dist x b + dist x c = dist a c (using d3)
  -- 
  -- Also, dist a x + dist x c ≥ dist a c (triangle inequality), with equality iff Wbtw a x c
  -- From d1 and d2: dist a x + dist x c ≤ dist a b + dist b c = dist a c
  -- Combined with triangle inequality: dist a x + dist x c = dist a c
  -- So Wbtw a x c holds.
  -- 
  -- Now: dist a x + dist x b = dist a b
  --      dist a x + dist x c = dist a c = dist a b + dist b c
  -- Subtracting: dist x c - dist x b = dist b c
  -- From d2: dist x b + dist x c = dist b c (since dist b x = dist x b)
  -- So dist x c - dist x b = dist x b + dist x c, which gives -2 * dist x b = 0, so dist x b = 0
  -- Therefore x = b!
  
  have h_xb_zero : dist x b = 0 := by
    have h1 : dist a x + dist x b = dist a b := d1
    have h2 : dist b x + dist x c = dist b c := d2
    have h3 : dist a b + dist b c = dist a c := d3
    have h_bx : dist b x = dist x b := dist_comm b x
    rw [h_bx] at h2
    -- From h1 + h2: dist a x + dist x b + dist x b + dist x c = dist a b + dist b c = dist a c
    -- dist a x + 2 * dist x b + dist x c = dist a c
    -- Triangle inequality: dist a x + dist x c ≥ dist a c
    -- So 2 * dist x b ≤ 0, hence dist x b = 0
    have h_tri : dist a c ≤ dist a x + dist x c := dist_triangle a x c
    linarith [dist_nonneg (x := x) (y := b)]
  exact dist_eq_zero.mp h_xb_zero

#check Wbtw.dist_add_dist

