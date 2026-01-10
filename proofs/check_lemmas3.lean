import Mathlib.Algebra.BigOperators.Group.Finset.Basic

variable (n : ℕ) (x : ℚ)
#check n • x
#check @nsmul_eq_mul'
#check @Algebra.smul_def
example : n • x = n * x := nsmul_eq_mul n x
