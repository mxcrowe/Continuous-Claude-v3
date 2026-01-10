import Mathlib

lemma wbtw_segment_intersection {V : Type*} {P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] 
    [MetricSpace P] [NormedAddTorsor V P]
    {a b c F : P} (h_abc : Wbtw ℝ a b c) (h_bFa : Wbtw ℝ b F a) (h_cFb : Wbtw ℝ c F b) : F = b := by
  have d_abc := Wbtw.dist_add_dist h_abc  -- dist a b + dist b c = dist a c
  have d_bFa := Wbtw.dist_add_dist h_bFa  -- dist b F + dist F a = dist b a
  have d_cFb := Wbtw.dist_add_dist h_cFb  -- dist c F + dist F b = dist c b
  -- Rewrite using dist_comm
  have d_bFa' : dist F b + dist a F = dist a b := by rw [dist_comm b F, dist_comm F a] at d_bFa; linarith
  have d_cFb' : dist F c + dist b F = dist b c := by rw [dist_comm c F, dist_comm c b, dist_comm F b] at d_cFb; linarith
  -- Triangle inequality
  have h_tri : dist a c ≤ dist a F + dist F c := dist_triangle a F c
  -- From the equalities: 
  -- dist a F = dist a b - dist F b
  -- dist F c = dist b c - dist b F
  -- And dist a c = dist a b + dist b c
  have h_Fb_zero : dist F b = 0 := by
    have h1 : dist a F ≤ dist a b := by
      have := Wbtw.dist_le_dist_left h_bFa
      rwa [dist_comm b a] at this
    have h2 : dist F c ≤ dist b c := by
      have := Wbtw.dist_le_dist_right h_cFb
      rwa [dist_comm c b] at this
    -- Alternative: compute directly
    -- dist a F + dist F c ≥ dist a c (triangle)
    -- dist a F = dist a b - dist F b (from d_bFa')
    -- dist F c = dist b c - dist b F = dist b c - dist F b (from d_cFb')
    -- So: (dist a b - dist F b) + (dist b c - dist F b) ≥ dist a b + dist b c
    -- dist a b + dist b c - 2 * dist F b ≥ dist a b + dist b c
    -- -2 * dist F b ≥ 0, so dist F b ≤ 0
    have eq1 : dist a F + dist F b = dist a b := d_bFa'
    have eq2 : dist F c + dist b F = dist b c := d_cFb'
    have eq3 : dist a b + dist b c = dist a c := d_abc
    have h_bF : dist b F = dist F b := dist_comm b F
    -- dist a F = dist a b - dist F b
    have h_aF : dist a F = dist a b - dist F b := by linarith
    -- dist F c = dist b c - dist F b
    have h_Fc : dist F c = dist b c - dist F b := by rw [h_bF] at eq2; linarith
    rw [h_aF, h_Fc] at h_tri
    linarith [dist_nonneg (x := F) (y := b)]
  exact dist_eq_zero.mp h_Fb_zero

#check wbtw_segment_intersection

