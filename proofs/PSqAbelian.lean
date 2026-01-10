import Mathlib

/-!
# Every group of order p² is abelian

This is already in Mathlib as `IsPGroup.commutative_of_card_eq_prime_sq`.
We verify the API and demonstrate its usage.
-/

variable {G : Type*} [Group G]
variable {p : ℕ} [hp : Fact (Nat.Prime p)]

-- Mathlib theorems for p-groups
#check Subgroup.center
#check IsPGroup
#check IsPGroup.center_nontrivial

-- The theorem we want (already in Mathlib!)
#check @IsPGroup.commutative_of_card_eq_prime_sq
-- IsPGroup.commutative_of_card_eq_prime_sq :
--   ∀ {p : ℕ} {G : Type*} [inst : Group G] [inst_1 : Fact (Nat.Prime p)] (hG : IsPGroup p G),
--     Nat.card G = p ^ 2 → ∀ (a b : G), a * b = b * a

-- Also there's a CommGroup instance
#check @IsPGroup.commGroupOfCardEqPrimeSq

-- For the G/Z(G) cyclic approach
#check @commutative_of_cyclic_center_quotient

