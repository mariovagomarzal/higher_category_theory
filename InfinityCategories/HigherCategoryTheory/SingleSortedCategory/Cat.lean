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

@[ext]
structure SingleSortedCategoriesFamily (index : Type) [NatIndex index] where
  Obj : Type u
  _inst : SingleSortedCategoryFamily Obj index

attribute [instance] SingleSortedCategoriesFamily._inst

open CategoryTheory in
instance SingleSortedCat (index : Type) [NatIndex index] :
    LargeCategory (SingleSortedCategoriesFamily index) where
  Hom C D := SingleSortedFunctorFamily C.Obj D.Obj index
  id C := id
  comp F G := G ⊚ F

end HigherCategoryTheory
