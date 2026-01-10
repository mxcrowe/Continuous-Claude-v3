import Mathlib

lemma wbtw_segment_intersection {V : Type*} {P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] 
    [MetricSpace P] [NormedAddTorsor V P]
    {a b c F : P} (h_abc : Wbtw ℝ a b c) (h_bFa : Wbtw ℝ b F a) (h_cFb : Wbtw ℝ c F b) : F = b := by
  -- Get distance equations from Wbtw
  have d_abc := Wbtw.dist_add_dist h_abc  -- dist a b + dist b c = dist a c
  have d_bFa := Wbtw.dist_add_dist h_bFa  -- dist b F + dist F a = dist b a = dist a b
  have d_cFb := Wbtw.dist_add_dist h_cFb  -- dist c F + dist F b = dist c b = dist b c
  -- Triangle inequality
  have h_tri : dist a c ≤ dist a F + dist F c := dist_triangle a F c
  -- Combine to show dist F b = 0
  have h_Fb_zero : dist F b = 0 := by
    -- From d_bFa: dist b F + dist F a = dist b a, i.e., dist F a = dist a b - dist b F
    -- From d_cFb: dist c F + dist F b = dist c b, i.e., dist c F = dist b c - dist F b
    -- Note dist b F = dist F b and dist c F = dist F c
    have h1 : dist F a = dist a b - dist F b := by
      have : dist b F + dist F a = dist b a := d_bFa
      rw [dist_comm b F, dist_comm b a] at this
      linarith
    have h2 : dist F c = dist b c - dist F b := by
      have : dist c F + dist F b = dist c b := d_cFb
      rw [dist_comm c F, dist_comm c b] at this
      linarith
    -- From h_tri: dist a c ≤ (dist a b - dist F b) + (dist b c - dist F b)
    --           = dist a b + dist b c - 2 * dist F b
    --           = dist a c - 2 * dist F b  (using d_abc)
    -- So 0 ≤ -2 * dist F b, hence dist F b ≤ 0
    rw [dist_comm a F, h1, h2] at h_tri
    linarith [dist_nonneg (x := F) (y := b)]
  exact dist_eq_zero.mp h_Fb_zero

#check wbtw_segment_intersection

