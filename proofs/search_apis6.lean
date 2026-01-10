import Mathlib

-- The key theorem: if G/Z(G) is cyclic, then G is abelian
-- This is because g^n * h^m = h^m * g^n when both come from a cyclic quotient
-- Let me find or prove it

variable {G : Type*} [Group G]

-- This should be in Mathlib somewhere
#check @Subgroup.cyclic_center_quotient_iff_abelian
#check @Group.center_quotient_cyclic_iff
#check @IsCyclic.mul_comm

-- Let me just prove it manually
lemma commute_of_cyclic_center_quotient 
    [IsCyclic (G ⧸ Subgroup.center G)] (a b : G) : a * b = b * a := by
  -- If G/Z(G) is cyclic with generator g, then 
  -- a = g^n * z₁ and b = g^m * z₂ for some z₁, z₂ ∈ Z(G)
  -- So ab = g^n z₁ g^m z₂ = g^n g^m z₁ z₂ = g^(n+m) z₁ z₂
  -- and ba = g^m z₂ g^n z₁ = g^m g^n z₂ z₁ = g^(n+m) z₂ z₁ = g^(n+m) z₁ z₂
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G ⧸ Subgroup.center G)
  sorry

