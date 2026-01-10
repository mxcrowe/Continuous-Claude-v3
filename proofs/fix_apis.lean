import Mathlib

variable {G : Type*} [Group G] [Fintype G]

-- Check the correct way to prove Nontrivial from card
#check @Fintype.one_lt_card_iff_nontrivial

example (h : 1 < Fintype.card G) : Nontrivial G := 
  Fintype.one_lt_card_iff_nontrivial.mp h

-- Check the correct way to get 1 < Nat.card from Nontrivial
#check @Nat.one_lt_card_iff_nontrivial
#check @one_lt_card_of_nontrivial

-- For subgroups
variable (H : Subgroup G)
#check (inferInstance : Nontrivial H)

example [h : Nontrivial H] : 1 < Nat.card H := by
  exact?

