import Mathlib

-- Look for the right lemma
#check @Polynomial.hom_eval₂
-- hom_eval₂ : f (p.eval₂ g x) = p.eval₂ (f.comp g) (f x)

-- What about just casting?
-- For a ring hom f : R →+* S and p : Polynomial R:
-- f (p.eval x) = (p.map f).eval (f x) 
-- This is because eval is eval₂ id
#check @Polynomial.eval_eq_eval₂_id
-- p.eval x = p.eval₂ (RingHom.id R) x

-- So: f (p.eval x) = f (p.eval₂ id x) = p.eval₂ (f.comp id) (f x) = p.eval₂ f (f x)
-- And: p.eval₂ f (f x) = (p.map f).eval (f x) by eval_map

-- Let me verify this
example (n q : ℕ) : 
    (((Polynomial.cyclotomic n ℤ).eval (q : ℤ) : ℤ) : ℝ) = 
    Polynomial.eval (q : ℝ) (Polynomial.cyclotomic n ℝ) := by
  let f := Int.castRingHom ℝ
  let p := Polynomial.cyclotomic n ℤ
  let x : ℤ := q
  -- Goal: f (p.eval x) = (p.map f).eval (f x)
  calc ((p.eval x) : ℝ)
      = f (p.eval x) := rfl
    _ = f (p.eval₂ (RingHom.id ℤ) x) := by rw [Polynomial.eval_eq_eval₂_id]
    _ = p.eval₂ (f.comp (RingHom.id ℤ)) (f x) := by rw [Polynomial.hom_eval₂]
    _ = p.eval₂ f (f x) := by simp
    _ = (p.map f).eval (f x) := by rw [← Polynomial.eval_map]
    _ = (Polynomial.cyclotomic n ℝ).eval (q : ℝ) := by
        rw [Polynomial.map_cyclotomic]
        simp

