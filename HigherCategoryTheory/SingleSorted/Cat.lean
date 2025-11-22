/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Basic
import HigherCategoryTheory.SingleSorted.Category
import HigherCategoryTheory.SingleSorted.Functor

/-!
# Categories of single-sorted categories

This file defines the categories whose objects are single-sorted categories and whose morphisms are
single-sorted functors.
-/

universe u

namespace HigherCategoryTheory

/-- TODO: Comment. -/
structure StructureFamily (bundled : Type u → Type u) : Type (u + 1) where
  obj : Type u
  str : bundled obj

namespace StructureFamily

variable {bundled : Type u → Type u} {C : StructureFamily bundled}

/-- TODO: Comment. -/
instance instCoeSort : CoeSort (StructureFamily bundled) (Type u) := ⟨StructureFamily.obj⟩

/-- TODO: Comment. -/
instance instBundled : bundled C := C.str

end StructureFamily

open CategoryTheory

/-- TODO: Comment. -/
abbrev SingleSortedCat (index : Type) [LinearOrder index] :=
  StructureFamily.{u} (SingleSortedCategory index)

/-- TODO: Comment. -/
abbrev SingleSortedNCat (n : ℕ) := StructureFamily.{u} (SingleSortedNCategory n)

/-- TODO: Comment. -/
instance SingleSortedCat.category {index : Type} [LinearOrder index] :
    Category (SingleSortedCat index) where
  Hom C D := SingleSortedFunctor index C D
  id C := idₛ C
  comp F G := G ⊚ F

-- Since `SingleSortedNCategory n` is just a special case of `SingleSortedCategory index`, we can
-- reuse the same instance.
example {n : ℕ} : Category (SingleSortedNCat n) := by infer_instance

/-- TODO: Comment. -/
abbrev SingleSortedOmegaCat := StructureFamily.{u} SingleSortedOmegaCategory

/-- TODO: Comment. -/
instance SingleSortedOmegaCat.category : Category SingleSortedOmegaCat where
  Hom C D := SingleSortedOmegaFunctor C D
  id C := idₛ C
  comp F G := G ⊚ F

end HigherCategoryTheory
