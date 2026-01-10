/-
  Category Theory Test: Functor preserves identity

  For any functor F : C ⥤ D and object X in C,
  F.map (𝟙 X) = 𝟙 (F.obj X)
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

-- Prove that functors preserve identity morphisms
-- Fixed with Godel suggestion: simp [F.map_id]
theorem functor_preserves_id (F : C ⥤ D) (X : C) :
    F.map (𝟙 X) = 𝟙 (F.obj X) := by
  simp [F.map_id]
