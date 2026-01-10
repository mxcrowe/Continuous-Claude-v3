import Mathlib

#check @Collinear.subset
#check @Collinear.mono
#check @collinear_of_finrank_le_one
#check @Collinear

example {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]
    {s t : Set P} (hst : s ⊆ t) (ht : Collinear k t) : Collinear k s := by
  exact?

