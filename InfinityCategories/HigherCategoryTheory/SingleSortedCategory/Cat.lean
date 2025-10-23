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
structure SingleSortedCategoryStructsFamily (index : Type) [NatIndex index] where
  Obj : Type u
  _inst : SingleSortedCategoryStruct Obj index

attribute [instance] SingleSortedCategoryStructsFamily._inst

open CategoryTheory

instance SingleSortedCatStruct (index : Type) [NatIndex index] :
    LargeCategory (SingleSortedCategoryStructsFamily index) where
  Hom C D := SingleSortedFunctorFamily C.Obj D.Obj index
  id _ := idₛₛ
  comp F G := G ⊚ F

end HigherCategoryTheory
