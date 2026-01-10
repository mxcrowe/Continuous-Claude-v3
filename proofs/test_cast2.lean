import Mathlib

-- Test how to properly cast cyclotomic evaluation
example (n q : ℕ) : (((Polynomial.cyclotomic n ℤ).eval (q : ℤ)) : ℝ) =
    Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ) := by
  -- Be explicit about the evaluation over ℤ first
  set evZ := (Polynomial.cyclotomic n ℤ).eval (q : ℤ) with hevZ
  -- The key is: Int.cast (p.eval x) = (p.map Int.cast).eval (Int.cast x)
  have h1 : (evZ : ℝ) =
      ((Polynomial.cyclotomic n ℤ).map (Int.castRingHom ℝ)).eval ((q : ℤ) : ℝ) := by
    simp only [Polynomial.eval_map, eq_intCast, RingHom.coe_coe]
  have h2 : (Polynomial.cyclotomic n ℤ).map (Int.castRingHom ℝ) = Polynomial.cyclotomic n ℝ :=
    Polynomial.map_cyclotomic n (Int.castRingHom ℝ)
  simp only [h1, h2, Int.cast_natCast]

