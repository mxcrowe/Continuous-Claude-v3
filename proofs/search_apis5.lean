import Mathlib

-- Search in Group namespace for anything about cyclic and center
#check @IsCyclic.commGroup
#check @Subgroup.IsCyclic.center

-- Let me search for theorems about quotient by center being cyclic
-- implying the group is commutative
example {G : Type*} [Group G] [IsCyclic (G ⧸ Subgroup.center G)] : 
    ∀ a b : G, a * b = b * a := by
  exact?

