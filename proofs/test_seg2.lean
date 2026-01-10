import Mathlib

-- Key lemma: if Wbtw a b c and Wbtw b F a and Wbtw c F b, then F = b
lemma wbtw_segment_intersection {V : Type*} {P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] 
    [MetricSpace P] [NormedAddTorsor V P]
    {a b c F : P} (h_abc : Wbtw ℝ a b c) (h_bFa : Wbtw ℝ b F a) (h_cFb : Wbtw ℝ c F b) : F = b := by
  have d_abc := Wbtw.dist_add_dist h_abc  -- dist a b + dist b c = dist a c
  have d_bFa := Wbtw.dist_add_dist h_bFa  -- dist b F + dist F a = dist b a
  have d_cFb := Wbtw.dist_add_dist h_cFb  -- dist c F + dist F b = dist c b
  rw [dist_comm b a] at d_bFa
  rw [dist_comm c b, dist_comm c F] at d_cFb
  have h_tri : dist a c ≤ dist a F + dist F c := dist_triangle a F c
  have h_Fb_zero : dist F b = 0 := by
    have h1 : dist a F = dist a b - dist b F := by linarith
    have h2 : dist F c = dist b c - dist F b := by linarith
    have h3 : dist a c = dist a b + dist b c := d_abc
    have h_bF : dist b F = dist F b := dist_comm b F
    rw [h1, h2, h3, h_bF] at h_tri
    linarith [dist_nonneg (x := F) (y := b)]
  exact dist_eq_zero.mp h_Fb_zero

#check wbtw_segment_intersection

