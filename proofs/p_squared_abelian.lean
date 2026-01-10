import Mathlib

/-!
# Every group of order p² is abelian

We prove that if G is a finite group of order p² for a prime p,
then G is abelian.

## Proof Strategy
1. For a p-group, the center Z(G) is non-trivial
2. If |G| = p², then |Z(G)| ∈ {p, p²}
3. If |Z(G)| = p², then G = Z(G), so G is abelian
4. If |Z(G)| = p, then G/Z(G) has order p, hence is cyclic
5. A group with cyclic quotient by its center is abelian
-/

-- The key theorem: a group of order p² is commutative
-- Found via Loogle: "Nat.card _ = _ ^ 2"
-- → IsPGroup.commutative_of_card_eq_prime_sq
-- → Nat.card_eq_fintype_card (for conversion)
theorem group_order_p_sq_abelian {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [hp : Fact (Nat.Prime p)] (h : Fintype.card G = p ^ 2) :
    ∀ a b : G, a * b = b * a := by
  -- Convert Fintype.card to Nat.card
  have h_nat : Nat.card G = p ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact h
  -- Apply the Mathlib theorem directly
  exact IsPGroup.commutative_of_card_eq_prime_sq h_nat
