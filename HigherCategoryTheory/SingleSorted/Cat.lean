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

* `Cat`: The category of single-sorted categories with a given index type.
* `NCat`: The category of single-sorted $n$-categories.
* `OmegaCat`: The category of single-sorted $\omega$-categories.

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
`bundled : Type u → Type u` (such as `SingleSorted.Category Index`), a `StructureFamily bundled`
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

end HigherCategoryTheory

namespace HigherCategoryTheory.SingleSorted

open HigherCategoryTheory

/--
The category of single-sorted categories with a given index type.

Objects of `Cat Index` are types equipped with a `Category Index` structure.
-/
abbrev Cat (Index : Type) [Preorder Index] :=
  StructureFamily.{u} (Category Index)

/- Since `Category Index` is just a type class on types, we can directly use the
`StructureFamily` instance to get the category structure. -/
example {Index : Type} [Preorder Index] {C : Type u} [Category Index C] :
    Cat Index :=
  StructureFamily.of C

/--
Category instance for `Cat Index`.

The morphisms between objects `C` and `D` are single-sorted functors `Functor Index C D`, the
identity morphism is the identity functor `idₛ`, and composition is functor composition `⊚`.
-/
instance Cat.category {Index : Type} [Preorder Index] :
    CategoryTheory.Category (Cat Index) where
  Hom C D := Functor Index C D
  id C := idₛ C
  comp F G := G ⊚ F

/-- The category of single-sorted $n$-categories. -/
abbrev NCat (n : ℕ) := StructureFamily.{u} (NCategory n)

/--
Category instance for `NCat n`.

Reuses the category structure from `Cat` but specifying that morphisms are of type `NFunctor`.
-/
instance NCat.category {n : ℕ} : CategoryTheory.Category (NCat n) :=
  { Cat.category with
    Hom C D := NFunctor n C D }

/-- The category of single-sorted $\omega$-categories. -/
abbrev OmegaCat := StructureFamily.{u} OmegaCategory

/--
Category instance for `OmegaCat`.

The morphisms between objects `C` and `D` are single-sorted $\omega$-functors
`OmegaFunctor C D`, the identity morphism is the identity functor `idₛ`, and composition
is functor composition `⊚`.
-/
instance OmegaCat.category : CategoryTheory.Category OmegaCat where
  Hom C D := OmegaFunctor C D
  id C := idₛ C
  comp F G := G ⊚ F

end HigherCategoryTheory.SingleSorted
