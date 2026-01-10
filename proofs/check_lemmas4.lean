import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

#check @Finset.sum_const
-- Finset.sum_const : ∀ ... ∑ x ∈ s, b = s.card • b
-- In additive group/monoid, s.card • b is scalar mult by ℕ

variable (s : Finset (Fin 3)) (b : ℚ)
#check s.card • b  -- this should be ℕ smul ℚ

-- Check if we need AddCommMonoid instance
#check (inferInstance : AddCommMonoid ℚ)

-- The smul for AddCommMonoid is nsmul
example (n : ℕ) (x : ℚ) : n • x = n * x := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih]; ring
