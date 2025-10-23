/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Basic
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Functor

/-!
TODO: Document the file.
-/

universe u

namespace HigherCategoryTheory

open CategoryTheory

structure ObjectsFamily where
  Obj : Type u

@[ext]
structure SingleSortedCategoriesFamily extends ObjectsFamily where
  _inst : SingleSortedCategory Obj

attribute [instance] SingleSortedCategoriesFamily._inst

instance SingleSortedCat : LargeCategory SingleSortedCategoriesFamily where
  Hom C D := SingleSortedFunctor C.Obj D.Obj
  id _ := idₛₛ
  comp F G := G ⊚ F

structure SingleSorted2CategoriesFamily extends ObjectsFamily where
  _inst : SingleSorted2Category Obj

attribute [instance] SingleSorted2CategoriesFamily._inst

instance SingleSorted2Cat : LargeCategory SingleSorted2CategoriesFamily where
  Hom C D := SingleSorted2Functor C.Obj D.Obj
  id _ := idₛₛ
  comp F G := G ⊚ F

structure SingleSortedNCategoriesFamily (n : Nat) extends ObjectsFamily where
  _inst : SingleSortedNCategory Obj n

attribute [instance] SingleSortedNCategoriesFamily._inst

instance SingleSortedNCat {n : Nat} : LargeCategory (SingleSortedNCategoriesFamily n) where
  Hom C D := SingleSortedNFunctor C.Obj D.Obj n
  id _ := idₛₛ
  comp F G := G ⊚ F

structure SingleSortedOmegaCategoriesFamily extends ObjectsFamily where
  _inst : SingleSortedOmegaCategory Obj

attribute [instance] SingleSortedOmegaCategoriesFamily._inst

instance SingleSortedOmegaCat : LargeCategory SingleSortedOmegaCategoriesFamily where
  Hom C D := SingleSortedOmegaFunctor C.Obj D.Obj
  id _ := idₛₛ
  comp F G := G ⊚ F

end HigherCategoryTheory
