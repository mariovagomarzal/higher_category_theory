/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category

/-!
# The single-sorted category on pair types

This file defines a single-sorted $1$-category structure on the product type $\alpha \times \alpha$
for any type $\alpha$.
-/

universe u

namespace Prod

open HigherCategoryTheory.SingleSorted

/-- The product type `α × α` forms a single-sorted $1$-category, where composition is defined when
the first component of the first pair equals the second component of the second pair and its value
is given by the pair formed by the second component of the first pair and the first component of the
second pair. -/
instance inst1Category {α : Type u} : NCategory 1 (α × α) where
  sc := fun _ (y₁, _) ↦ (y₁, y₁)
  tg := fun _ (_, x₂) ↦ (x₂, x₂)
  pcomp := fun _ (y₁, y₂) (x₁, x₂) ↦ ⟨y₁ = x₂, fun _ ↦ (x₁, y₂)⟩

end Prod
