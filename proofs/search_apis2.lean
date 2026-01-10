import Mathlib

-- Check Fintype.one_lt_card_iff
#check @Fintype.one_lt_card_iff
-- Check if there's a direct way
variable {G : Type*} [Group G] [Fintype G]

example (h : 1 < Fintype.card G) : Nontrivial G := by
  exact Fintype.one_lt_card_iff.mp h

-- What about commutative from cyclic center quotient?
#check @IsCyclic
#check @Subgroup.center
#check @QuotientGroup.quotientGroup

-- Let me search for the theorem about G/Z(G) cyclic => G commutative
example [IsCyclic (G ⧸ Subgroup.center G)] : ∀ a b : G, a * b = b * a := by
  exact?

