import Mathlib

variable {G : Type*} [Group G]

-- The quotient map for the center
#check @QuotientGroup.mk'
#check @QuotientGroup.ker_mk'

-- Check the theorem signature
#check @commutative_of_cyclic_center_quotient

-- The key: for the quotient map, ker = center
example : (QuotientGroup.mk' (Subgroup.center G)).ker = Subgroup.center G := 
  QuotientGroup.ker_mk' _

-- So we need to show center ≤ center which is trivial
example [IsCyclic (G ⧸ Subgroup.center G)] (a b : G) : a * b = b * a := by
  have hker : (QuotientGroup.mk' (Subgroup.center G)).ker ≤ Subgroup.center G := by
    rw [QuotientGroup.ker_mk']
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center G)) hker a b

