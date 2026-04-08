/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Basic
import HigherCategoryTheory.Indices
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

Each bundled category (`Cat`, `OmegaCat`) is defined as a structure pairing a carrier type with the
corresponding category instance. Coercion to the carrier type is provided so that the underlying
type can be used directly.

The specialization `NCat` is an abbreviation for `Cat (Fin n)`, while `OmegaCat` is defined as its
own structure rather than as `Cat ℕ` because `OmegaCategory` extends `Category ℕ` with an additional
axiom (`is_cell`). Both have separate `Category` instances that narrow the morphisms to `NFunctor`
and `OmegaFunctor` respectively. The `lift` function embeds an `OmegaCat` into `Cat ℕ` by forgetting
`is_cell`.
-/

universe u

namespace HigherCategoryTheory.SingleSorted

/--
The category of single-sorted categories with a given index type.

Bundles a carrier type `C` with a `Category Index C` instance.
-/
structure Cat (Index : Type) [Preorder Index] where
  /-- Build a `Cat` from a carrier type with a `Category` instance. -/
  of ::
  /-- The underlying carrier type. -/
  carrier : Type u
  /-- The single-sorted category structure on the carrier. -/
  [str : Category Index carrier]

attribute [instance] Cat.str

namespace Cat

variable {Index : Type} [Preorder Index]

/-- Coercion allowing a `Cat` to be used as its underlying carrier type. -/
instance : CoeSort (Cat Index) (Type u) := ⟨Cat.carrier⟩

attribute [coe] Cat.carrier

/--
Category instance for `Cat Index`.

The morphisms between objects `C` and `D` are single-sorted functors `Functor Index C D`, the
identity morphism is the identity functor `idₛ`, and composition is functor composition `⊚`.
-/
instance category : CategoryTheory.LargeCategory.{u} (Cat Index) where
  Hom C D := Functor Index C D
  comp F G := G ⊚ F
  id C := idₛ C

end Cat

/-- The category of single-sorted $n$-categories. -/
abbrev NCat (n : ℕ) := Cat (Fin n)

namespace NCat

variable {n : ℕ}

/--
Category instance for `NCat n`.

The morphisms between objects `C` and `D` are `NFunctor n C D`, the identity morphism is the
identity functor `idₛ`, and composition is functor composition `⊚`.
-/
instance category : CategoryTheory.LargeCategory.{u} (NCat n) where
  Hom C D := NFunctor n C D
  comp F G := G ⊚ F
  id C := idₛ C

end NCat

/--
The category of single-sorted $\omega$-categories.

Bundles a carrier type `C` with an `OmegaCategory C` instance. Defined as its own structure rather
than as `Cat ℕ` because `OmegaCategory` extends `Category ℕ` with the `is_cell` axiom.
-/
structure OmegaCat where
  /-- Build an `OmegaCat` from a carrier type with an `OmegaCategory` instance. -/
  of ::
  /-- The underlying carrier type. -/
  carrier : Type u
  /-- The single-sorted $\omega$-category structure on the carrier. -/
  [str : OmegaCategory carrier]

attribute [instance] OmegaCat.str

namespace OmegaCat

/-- Coercion allowing an `OmegaCat` to be used as its underlying carrier type. -/
instance : CoeSort OmegaCat (Type u) := ⟨OmegaCat.carrier⟩

attribute [coe] OmegaCat.carrier

/--
Category instance for `OmegaCat`.

The morphisms between objects `C` and `D` are single-sorted $\omega$-functors `OmegaFunctor C D`,
the identity morphism is the identity functor `idₛ`, and composition is functor composition `⊚`.
-/
instance category : CategoryTheory.LargeCategory.{u} OmegaCat where
  Hom C D := OmegaFunctor C D
  comp F G := G ⊚ F
  id C := idₛ C

/-- Embed an `OmegaCat` into `Cat ℕ` by forgetting the `is_cell` axiom. -/
def lift {C : OmegaCat} : Cat ℕ where carrier := C.carrier

end OmegaCat

/--
The category of single-sorted categories of a given dimension in `ℕ∞`.

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

end HigherCategoryTheory.SingleSorted
