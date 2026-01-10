import Mathlib

-- Test how to properly cast cyclotomic evaluation
-- Use explicit type annotation
example (n q : ℕ) : 
    (((Polynomial.cyclotomic n ℤ).eval (q : ℤ) : ℤ) : ℝ) = 
    Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ) := by
  have h1 : (((Polynomial.cyclotomic n ℤ).eval (q : ℤ) : ℤ) : ℝ) =
      ((Polynomial.cyclotomic n ℤ).map (Int.castRingHom ℝ)).eval ((q : ℤ) : ℝ) := by
    rw [Polynomial.eval_map]
  have h2 : (Polynomial.cyclotomic n ℤ).map (Int.castRingHom ℝ) = Polynomial.cyclotomic n ℝ :=
    Polynomial.map_cyclotomic n (Int.castRingHom ℝ)
  simp only [h1, h2, Int.cast_natCast]

