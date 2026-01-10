import Mathlib

#check @pow_le_pow_right
#check @Nat.pow_le_pow_right
#check @pow_right_mono
#check @pow_le_pow_of_le_right
#check @geom_sum_mul

-- Check cast lemmas
example (n : ℕ) (q : ℤ) : (Polynomial.cyclotomic n ℤ).eval q = 
    ((Polynomial.cyclotomic n ℤ).map (Int.castRingHom ℝ)).eval (q : ℝ) := by
  rw [Polynomial.eval_map]
  simp

