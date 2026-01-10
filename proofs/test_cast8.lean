import Mathlib

-- Look for direct lemma
#check @RingHom.map_polynomial_eval

example (n q : ℕ) : 
    (((Polynomial.cyclotomic n ℤ).eval (q : ℤ) : ℤ) : ℝ) = 
    Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ) := by
  let f := Int.castRingHom ℝ
  let p := Polynomial.cyclotomic n ℤ
  -- Direct approach using hom_eval₂
  have h1 : (f (p.eval (q : ℤ))) = p.eval₂ f (f (q : ℤ)) := by
    conv_lhs => rw [show p.eval (q : ℤ) = p.eval₂ (RingHom.id ℤ) (q : ℤ) from rfl]
    rw [Polynomial.hom_eval₂]
    simp
  have h2 : p.eval₂ f (f (q : ℤ)) = (p.map f).eval (f (q : ℤ)) := by
    rw [← Polynomial.eval_map]
  have h3 : (p.map f) = Polynomial.cyclotomic n ℝ := Polynomial.map_cyclotomic n f
  simp only [h1, h2, h3]
  simp

