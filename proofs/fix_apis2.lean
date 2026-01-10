import Mathlib

variable {G : Type*} [Group G] [Fintype G]

-- For subgroups with Nontrivial
variable (H : Subgroup G) [hnt : Nontrivial H]

#check @Finite.one_lt_card_iff_nontrivial

example : 1 < Nat.card H := Finite.one_lt_card_iff_nontrivial.mpr hnt

-- Check the Fintype version too
#check @Fintype.one_lt_card

example [Fintype H] : 1 < Fintype.card H := Fintype.one_lt_card

