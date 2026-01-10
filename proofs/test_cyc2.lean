import Mathlib

-- Check cyclotomic_two
#check @Polynomial.cyclotomic_two
-- cyclotomic 2 R = X + 1

example (q : ℕ) (hq : 2 ≤ q) : 0 < (Polynomial.cyclotomic 2 ℤ).eval (q : ℤ) := by
  rw [Polynomial.cyclotomic_two]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  omega

