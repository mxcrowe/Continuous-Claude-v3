-- Basic proofs module
-- Add your theorems here

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory

-- Example: Identity functor
example {C : Type*} [Category C] : C ⥤ C := Functor.id C
