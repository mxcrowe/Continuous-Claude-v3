import Mathlib

-- Working lemma for casting cyclotomic evaluation
lemma cyclotomic_eval_cast (n q : ℕ) : 
    (((Polynomial.cyclotomic n ℤ).eval (q : ℤ) : ℤ) : ℝ) = 
    Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ) := by
  let f := Int.castRingHom ℝ
  let p := Polynomial.cyclotomic n ℤ
  show f (p.eval (q : ℤ)) = Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ)
  have h1 : f (p.eval (q : ℤ)) = p.eval₂ f (f (q : ℤ)) := by
    conv_lhs => rw [show p.eval (q : ℤ) = p.eval₂ (RingHom.id ℤ) (q : ℤ) from rfl]
    rw [Polynomial.hom_eval₂]
    simp
  have h2 : p.eval₂ f (f (q : ℤ)) = (p.map f).eval (f (q : ℤ)) := by
    rw [← Polynomial.eval_map]
  have h3 : (p.map f) = Polynomial.cyclotomic n ℝ := Polynomial.map_cyclotomic n f
  have h4 : f (q : ℤ) = (q : ℝ) := by simp [f]
  rw [h1, h2, h3, h4]

#check cyclotomic_eval_cast

