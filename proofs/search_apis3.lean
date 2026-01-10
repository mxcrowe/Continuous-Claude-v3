import Mathlib

variable {G : Type*} [Group G] [Fintype G]

-- Find the correct nontrivial lemma
#check @Fintype.one_lt_card_iff_nontrivial

-- Alternative approach: construct Nontrivial directly
example (h : 1 < Fintype.card G) : Nontrivial G := by
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp h
  exact ⟨⟨a, b, hab⟩⟩

-- Now find the cyclic quotient lemma
#check @Group.cyclic_center_quotient_of_card_prime_sq

-- Let me search for commutative
example (hcyc : IsCyclic (G ⧸ Subgroup.center G)) : ∀ a b : G, a * b = b * a := by
  intro a b
  have := Group.commutative_of_cyclic_center_quotient
  sorry

