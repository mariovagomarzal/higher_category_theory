/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Basic
import HigherCategoryTheory.Indices
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

The `Cat` structure bundles a family of types `Index → Type u` with a many-sorted `Category`
instance. Coercion to the carrier family is provided so that the underlying types can be used
directly.

The specialization `NCat` is an abbreviation for `Cat (FinSucc n)`, and `OmegaCat` for `Cat ℕ`
(since many-sorted `OmegaCategory` is defined as `Category ℕ` without additional axioms). Both have
separate `Category` instances that narrow the morphisms to `NFunctor` and `OmegaFunctor`
respectively.
-/

universe u

namespace HigherCategoryTheory.ManySorted

/--
The category of many-sorted categories with a given index type.

Bundles a family of types `C : Index → Type u` with a `Category Index C` instance.
-/
structure Cat (Index : Type) [Preorder Index] where
  /-- Build a `Cat` from a carrier family with a `Category` instance. -/
  of ::
  /-- The underlying family of types indexed by `Index`. -/
  carrier : Index → Type u
  /-- The many-sorted category structure on the family. -/
  [str : Category Index carrier]

attribute [instance] Cat.str

namespace Cat

variable {Index : Type} [Preorder Index]

/-- Coercion allowing a `Cat` to be applied to an index, yielding the type at that dimension. -/
instance : CoeFun (Cat Index) fun _ ↦ Index → Type u := ⟨Cat.carrier⟩

attribute [coe] Cat.carrier

/--
Category instance for `Cat Index`.

The morphisms between objects `C` and `D` are many-sorted functors `Functor Index C D`, the
identity morphism is the identity functor `idₘ`, and composition is functor composition `⊚`.
-/
instance category : CategoryTheory.LargeCategory.{u} (Cat Index) where
  Hom C D := Functor Index C D
  comp F G := G ⊚ F
  id C := idₘ C

end Cat

/-- The category of many-sorted $n$-categories. -/
abbrev NCat (n : ℕ) := Cat (FinSucc n)

namespace NCat

variable {n : ℕ}

/--
Category instance for `NCat n`.

The morphisms between objects `C` and `D` are `NFunctor n C D`, the identity morphism is the
identity functor `idₘ`, and composition is functor composition `⊚`.
-/
instance category : CategoryTheory.LargeCategory.{u} (NCat n) where
  Hom C D := NFunctor n C D
  comp F G := G ⊚ F
  id C := idₘ C

end NCat

/-- The category of many-sorted $\omega$-categories. -/
abbrev OmegaCat := Cat ℕ

namespace OmegaCat

/--
Category instance for `OmegaCat`.

The morphisms between objects `C` and `D` are many-sorted $\omega$-functors
`OmegaFunctor C D`, the identity morphism is the identity functor `idₘ`, and composition
is functor composition `⊚`.
-/
instance category : CategoryTheory.LargeCategory.{u} OmegaCat where
  Hom C D := OmegaFunctor C D
  comp F G := G ⊚ F
  id C := idₘ C

end OmegaCat

/--
The category of many-sorted categories of a given dimension in `ℕ∞`.

Returns `NCat n` when the dimension is finite and `OmegaCat` when the dimension is $\omega$.
-/
abbrev ICat (dimension : ℕ∞) : Type (u + 1) := match dimension with
  | fin n => NCat n
  | ω => OmegaCat

/-- Category instance for `ICat dimension`, where the category instance for each case of `dimension`
is inferred from the corresponding category instance of `NCat n` or `OmegaCat`. -/
instance ICat.category {dimension : ℕ∞} : CategoryTheory.LargeCategory.{u} (ICat dimension) :=
  match dimension with
  | fin _ => NCat.category
  | ω => OmegaCat.category

end HigherCategoryTheory.ManySorted
