import Mathlib

variable {G : Type*} [Group G] [Fintype G]

-- Search for the quotient by center theorem
-- Maybe it's about proving the whole group is abelian
#check @Group.commutative_of_cyclic_center_quotient
#check @Subgroup.commutative_of_cyclic_center_quotient
#check @CommGroup
#check @Group.IsAbelian

-- Alternative: try exact?
example (hcyc : IsCyclic (G ⧸ Subgroup.center G)) : ∀ a b : G, a * b = b * a := by
  intro a b
  apply?

-- Or perhaps there's a theorem about when Z(G) = G
#check @Subgroup.center_eq_top

