/-
Theorem: For all natural numbers n, n + 0 = n

This is one of the defining properties of addition on natural numbers.
-/

theorem nat_add_zero : ∀ n : Nat, n + 0 = n := by
  intro n
  simp
