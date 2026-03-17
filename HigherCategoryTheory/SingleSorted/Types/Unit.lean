/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category

/-!
# The single-sorted category on the unit type

This file defines the trivial single-sorted $1$-category structure on the unit type.
-/

universe u

namespace Unit

open HigherCategoryTheory.SingleSorted

/-- The unit type with its unique element forms a single-sorted $1$-category, where composition is
always defined and its value is the unique element of the unit type. -/
instance instSingleSorted1Category : NCategory 1 Unit where
  sc _ _ := ()
  tg _ _ := ()
  pcomp _ _ _ := ⟨True, fun _ ↦ ()⟩

end Unit
