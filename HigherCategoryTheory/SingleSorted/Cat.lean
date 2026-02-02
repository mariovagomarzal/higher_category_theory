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

## Main definitions

* `SingleSortedCat`: The category of single-sorted categories with a given index type.
* `SingleSortedNCat`: The category of single-sorted $n$-categories.
* `SingleSortedOmegaCat`: The category of single-sorted $\omega$-categories.

## Implementation notes

The `StructureFamily` structure pairs a type with a structure class instance, enabling the
construction of categories of structured objects. Coercion and instance mechanisms are provided to
seamlessly access the underlying type and its structure.
-/

universe u

namespace HigherCategoryTheory

/--
A generic bundled structure that pairs a type with a structure class instance.

This structure is used to create categories of structured mathematical objects. Given a type class
`bundled : Type u → Type u` (such as `SingleSortedCategory index`), a `StructureFamily bundled`
consists of a type `obj : Type u` together with an instance `str : bundled obj`.

This construction enables treating structured objects as first-class citizens in category theory,
allowing us to define categories whose objects are themselves structured types.
-/
structure StructureFamily (bundled : Type u → Type u) : Type (u + 1) where
  obj : Type u
  str : bundled obj := by infer_instance

namespace StructureFamily

variable {bundled : Type u → Type u} {C : StructureFamily bundled}

set_option checkBinderAnnotations false in
/--
Convenience constructor for `StructureFamily` that automatically infers the structure instance.

Given a type `obj` with an instance of `bundled obj`, this constructs a `StructureFamily bundled`.
-/
def of (obj : Type u) [str : bundled obj] : StructureFamily bundled := ⟨obj, str⟩

/--
Coercion instance allowing a `StructureFamily` to be used as its underlying type.

This enables writing `C` instead of `C.obj` when referring to the underlying type of a
`StructureFamily bundled` value.
-/
instance instCoeSort : CoeSort (StructureFamily bundled) (Type u) := ⟨StructureFamily.obj⟩

/--
Provides the bundled structure instance for a `StructureFamily`.

This instance allows accessing the structure on the underlying type of a `StructureFamily` value,
enabling seamless use of the bundled structure's operations and properties.
-/
instance instBundled : bundled C := C.str

end StructureFamily

open CategoryTheory

/--
The category of single-sorted categories with a given index type.

Objects of `SingleSortedCat index` are types equipped with a `SingleSortedCategory index` structure.
-/
abbrev SingleSortedCat (index : Type) [LinearOrder index] :=
  StructureFamily.{u} (SingleSortedCategory index)

/- Since `SingleSortedCategory index` is just a type class on types, we can directly use the
`StructureFamily` instance to get the category structure. -/
example {index : Type} [LinearOrder index] {C : Type u} [SingleSortedCategory index C] :
    SingleSortedCat index :=
  StructureFamily.of C

/--
Category instance for `SingleSortedCat index`.

The morphisms between objects `C` and `D` are single-sorted functors `SingleSortedFunctor index C
D`, the identity morphism is the identity functor `idₛ`, and composition is functor composition `⊚`.
-/
instance SingleSortedCat.category {index : Type} [LinearOrder index] :
    Category (SingleSortedCat index) where
  Hom C D := SingleSortedFunctor index C D
  id C := idₛ C
  comp F G := G ⊚ F

/-- The category of single-sorted $n$-categories. -/
abbrev SingleSortedNCat (n : ℕ) := StructureFamily.{u} (SingleSortedNCategory n)

/--
Category instance for `SingleSortedNCat n`.

Reuses the category structure from `SingleSortedCat` but specifying that morphisms are of type
`SingleSortedNFunctor`.
-/
instance SingleSortedNCat.category {n : ℕ} : Category (SingleSortedNCat n) :=
  { SingleSortedCat.category with
    Hom C D := SingleSortedNFunctor n C D }

/-- The category of single-sorted $\omega$-categories. -/
abbrev SingleSortedOmegaCat := StructureFamily.{u} SingleSortedOmegaCategory

/--
Category instance for `SingleSortedOmegaCat`.

The morphisms between objects `C` and `D` are single-sorted $\omega$-functors
`SingleSortedOmegaFunctor C D`, the identity morphism is the identity functor `idₛ`, and composition
is functor composition `⊚`.
-/
instance SingleSortedOmegaCat.category : Category SingleSortedOmegaCat where
  Hom C D := SingleSortedOmegaFunctor C D
  id C := idₛ C
  comp F G := G ⊚ F

end HigherCategoryTheory
