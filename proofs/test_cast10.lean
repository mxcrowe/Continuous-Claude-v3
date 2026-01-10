import Mathlib

example (n q : ℕ) : 
    (((Polynomial.cyclotomic n ℤ).eval (q : ℤ) : ℤ) : ℝ) = 
    Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ) := by
  let f := Int.castRingHom ℝ
  let p := Polynomial.cyclotomic n ℤ
  -- The LHS is f (p.eval (q : ℤ)), need to transform to RHS
  show f (p.eval (q : ℤ)) = Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ)
  have h1 : f (p.eval (q : ℤ)) = p.eval₂ f (f (q : ℤ)) := by
    conv_lhs => rw [show p.eval (q : ℤ) = p.eval₂ (RingHom.id ℤ) (q : ℤ) from rfl]
    rw [Polynomial.hom_eval₂]
    simp
  have h2 : p.eval₂ f (f (q : ℤ)) = (p.map f).eval (f (q : ℤ)) := by
    rw [← Polynomial.eval_map]
  have h3 : (p.map f) = Polynomial.cyclotomic n ℝ := Polynomial.map_cyclotomic n f
  rw [h1, h2, h3]
  -- now we need f (q : ℤ) = (q : ℝ)
  congr 1
  simp [f]

