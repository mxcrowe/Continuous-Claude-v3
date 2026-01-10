import Mathlib

#check @Polynomial.eval_map
-- Polynomial.eval_map : (p.map f).eval x = p.eval₂ f x

#check @Polynomial.eval₂_ringHom_apply
-- eval₂_ringHom_apply : f (p.eval₂ g x) = p.eval₂ (f.comp g) (f x)

-- So we want: (Int.castRingHom ℝ) (p.eval x) = (p.map (Int.castRingHom ℝ)).eval (Int.castRingHom ℝ x)
-- But eval_map gives: (p.map f).eval x = p.eval₂ f x

-- Let's check int_cast_eval
#check @Polynomial.int_cast_eq_C

-- Maybe we need eval₂ directly
example (n q : ℕ) : 
    (((Polynomial.cyclotomic n ℤ).eval (q : ℤ) : ℤ) : ℝ) = 
    Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ) := by
  -- Use eval₂ as intermediate
  have key : ∀ (p : Polynomial ℤ), ((p.eval (q : ℤ)) : ℝ) = 
      (p.map (Int.castRingHom ℝ)).eval ((q : ℤ) : ℝ) := by
    intro p
    simp only [Polynomial.eval_map, Int.cast_natCast]
    rfl
  rw [key]
  congr 1
  · exact Polynomial.map_cyclotomic n (Int.castRingHom ℝ)
  · simp

