import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

variable (s : Finset (Fin 3)) (b : ℚ) (n : ℕ)

#check s.card • b  
#check @nsmul_eq_mul

example : s.card • b = s.card * b := nsmul_eq_mul s.card b
