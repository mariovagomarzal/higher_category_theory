/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Basic
import HigherCategoryTheory.ManySorted.Category
import HigherCategoryTheory.ManySorted.Functor

/-!
# Categories of many-sorted categories

This file defines the categories whose objects are many-sorted categories and whose morphisms are
many-sorted functors.

## Main definitions

* `Cat`: The category of many-sorted categories with a given index type.
* `NCat`: The category of many-sorted $n$-categories.
* `OmegaCat`: The category of many-sorted $\omega$-categories.

## Implementation notes

The `Cat` structure bundles a type family `Index → Type u` with a many-sorted `Category` instance,
enabling the construction of categories of many-sorted structured objects. This is analogous to
`StructureFamily` from the single-sorted setting, but adapted for type families.
-/

universe u

namespace HigherCategoryTheory.ManySorted

/--
A bundled many-sorted category: a family of types equipped with a `Category` instance.

Objects of `Cat Index` are families of types `(C k)_{k ∈ Index}` together with a many-sorted
`Category Index C` structure.
-/
structure Cat (Index : Type) [Preorder Index] : Type (u + 1) where
  /-- The underlying family of types indexed by `Index`. -/
  obj : Index → Type u
  /-- The many-sorted category structure on the family. -/
  str : Category Index obj := by infer_instance

namespace Cat

attribute [instance] Cat.str

variable {Index : Type} [Preorder Index]

set_option checkBinderAnnotations false in
/--
Convenience constructor for `Cat` that automatically infers the category instance.

Given a family of types `obj` with an instance of `Category Index obj`, this constructs a
`Cat Index`.
-/
def of (obj : Index → Type u) [str : Category Index obj] : Cat Index := ⟨obj, str⟩

/--
Category instance for `Cat Index`.

The morphisms between objects `C` and `D` are many-sorted functors `Functor Index C D`, the
identity morphism is the identity functor `idₘ`, and composition is functor composition `⊚`.
-/
instance category : CategoryTheory.Category (Cat.{u} Index) where
  Hom C D := Functor Index C.obj D.obj
  id C := idₘ C.obj
  comp F G := G ⊚ F

end Cat

/-- The category of many-sorted $n$-categories. -/
abbrev NCat (n : ℕ) := Cat.{u} (FinSucc n)

/--
Category instance for `NCat n`.

Reuses the category structure from `Cat` but specifying that morphisms are of type `NFunctor`.
-/
instance NCat.category {n : ℕ} : CategoryTheory.Category (NCat.{u} n) :=
  { Cat.category with
    Hom C D := NFunctor n C.obj D.obj }

/-- The category of many-sorted $\omega$-categories. -/
abbrev OmegaCat := Cat.{u} ℕ

/--
Category instance for `OmegaCat`.

Reuses the category structure from `Cat` but specifying that morphisms are of type `OmegaFunctor`.
-/
instance OmegaCat.category : CategoryTheory.Category OmegaCat.{u} :=
  { Cat.category with
    Hom C D := OmegaFunctor C.obj D.obj }

end HigherCategoryTheory.ManySorted
