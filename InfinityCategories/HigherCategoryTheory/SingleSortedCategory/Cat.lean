/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Basic
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Functor

/-!
# Categories of single-sorted higher-order categories

This file defines the large categories whose objects are single-sorted categories, 2-categories,
$n$-categories, and $\omega$-categories, with functors as morphisms.

## Implementation notes

The "Family" structures (`SingleSortedCategoriesFamily`, `SingleSorted2CategoriesFamily`, etc.)
extend `ObjectsFamily` and carry the appropriate type class instance. These families serve as the
objects of the corresponding large categories. The large category instances use `LargeCategory`
from Mathlib's category theory library, with functors as morphisms and functor composition as
the composition operation.
-/

universe u

namespace HigherCategoryTheory

open CategoryTheory

/-- A family of objects, represented as a wrapper around a type. This serves as the base structure
for families of categories and higher categories. -/
structure ObjectsFamily where
  /-- The underlying type of objects in the family. -/
  Obj : Type u

/-- A family of single-sorted categories, consisting of a type `Obj` equipped with a
`SingleSortedCategory` instance. This structure serves as the objects in the large category
`SingleSortedCat`. -/
@[ext]
structure SingleSortedCategoriesFamily extends ObjectsFamily where
  /-- The `SingleSortedCategory` structure on the underlying type. -/
  _inst : SingleSortedCategory Obj

attribute [instance] SingleSortedCategoriesFamily._inst

/-- The large category of single-sorted categories. Objects are families of single-sorted
categories (`SingleSortedCategoriesFamily`), and morphisms are single-sorted functors between
them. -/
instance SingleSortedCat : LargeCategory SingleSortedCategoriesFamily where
  Hom C D := SingleSortedFunctor C.Obj D.Obj
  id _ := idₛₛ
  comp F G := G ⊚ F

/-- A family of single-sorted 2-categories, consisting of a type `Obj` equipped with a
`SingleSorted2Category` instance. This structure serves as the objects in the large category
`SingleSorted2Cat`. -/
structure SingleSorted2CategoriesFamily extends ObjectsFamily where
  /-- The `SingleSorted2Category` structure on the underlying type. -/
  _inst : SingleSorted2Category Obj

attribute [instance] SingleSorted2CategoriesFamily._inst

/-- The large category of single-sorted 2-categories. Objects are families of single-sorted
2-categories (`SingleSorted2CategoriesFamily`), and morphisms are single-sorted 2-functors between
them. -/
instance SingleSorted2Cat : LargeCategory SingleSorted2CategoriesFamily where
  Hom C D := SingleSorted2Functor C.Obj D.Obj
  id _ := idₛₛ
  comp F G := G ⊚ F

/-- A family of single-sorted $n$-categories for a fixed natural number `n`, consisting of a type
`Obj` equipped with a `SingleSortedNCategory` instance. This structure serves as the objects in
the large category `SingleSortedNCat`. -/
structure SingleSortedNCategoriesFamily (n : Nat) extends ObjectsFamily where
  /-- The `SingleSortedNCategory` structure on the underlying type. -/
  _inst : SingleSortedNCategory Obj n

attribute [instance] SingleSortedNCategoriesFamily._inst

/-- The large category of single-sorted $n$-categories for a fixed `n : Nat`. Objects are families
of single-sorted $n$-categories (`SingleSortedNCategoriesFamily n`), and morphisms are
single-sorted $n$-functors between them. -/
instance SingleSortedNCat {n : Nat} : LargeCategory (SingleSortedNCategoriesFamily n) where
  Hom C D := SingleSortedNFunctor C.Obj D.Obj n
  id _ := idₛₛ
  comp F G := G ⊚ F

/-- A family of single-sorted $\omega$-categories, consisting of a type `Obj` equipped with a
`SingleSortedOmegaCategory` instance. This structure serves as the objects in the large category
`SingleSortedOmegaCat`. -/
structure SingleSortedOmegaCategoriesFamily extends ObjectsFamily where
  /-- The `SingleSortedOmegaCategory` structure on the underlying type. -/
  _inst : SingleSortedOmegaCategory Obj

attribute [instance] SingleSortedOmegaCategoriesFamily._inst

/-- The large category of single-sorted $\omega$-categories. Objects are families of single-sorted
$\omega$-categories (`SingleSortedOmegaCategoriesFamily`), and morphisms are single-sorted
$\omega$-functors between them. -/
instance SingleSortedOmegaCat : LargeCategory SingleSortedOmegaCategoriesFamily where
  Hom C D := SingleSortedOmegaFunctor C.Obj D.Obj
  id _ := idₛₛ
  comp F G := G ⊚ F

end HigherCategoryTheory
