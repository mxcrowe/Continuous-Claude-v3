/-
  Natural Transformation Test

  For natural transformation η : F ⟹ G, the naturality square commutes.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.NatTrans

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {F G : C ⥤ D}

-- Prove naturality condition
-- Fixed with Godel: exact η.naturality f
theorem naturality_square (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ η.app Y = η.app X ≫ G.map f := by
  exact η.naturality f
