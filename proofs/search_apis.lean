import Mathlib

-- Search for nontrivial from card
#check @Fintype.one_lt_card_iff
#check @Nat.one_lt_card_iff
#check @nontrivial_of_one_lt_card

-- Search for commutative_of_cyclic
#check @Group.commutative_of_cyclic_center_quotient
#check @commutative_of_cyclic_center_quotient

-- Check the API for center and nontrivial
example {G : Type*} [Group G] [Fintype G] (h : 1 < Fintype.card G) : Nontrivial G :=
  Fintype.one_lt_card_iff.mp h

