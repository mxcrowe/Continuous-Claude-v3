import Mathlib

-- Test how to properly cast cyclotomic evaluation
example (n q : ℕ) : ((Polynomial.cyclotomic n ℤ).eval (q : ℤ) : ℤ) = 
    ((Polynomial.cyclotomic n ℤ).eval (q : ℤ)) := rfl

-- Now try the cast
example (n q : ℕ) : True := by
  have evZ : ℤ := (Polynomial.cyclotomic n ℤ).eval (q : ℤ)
  have hcast : (evZ : ℝ) = Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ) := by
    have h1 : (evZ : ℝ) =
        ((Polynomial.cyclotomic n ℤ).map (Int.castRingHom ℝ)).eval ((q : ℤ) : ℝ) := by
      simp only [Polynomial.eval_map, eq_intCast, RingHom.coe_coe]
    have h2 : (Polynomial.cyclotomic n ℤ).map (Int.castRingHom ℝ) = Polynomial.cyclotomic n ℝ :=
      Polynomial.map_cyclotomic n (Int.castRingHom ℝ)
    simp only [h1, h2, Int.cast_natCast]
  trivial

