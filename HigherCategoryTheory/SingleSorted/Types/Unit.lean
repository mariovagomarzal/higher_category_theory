/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category

/-!
# The single-sorted category on the unit type

This file defines the trivial single-sorted category structure on the unit type.
-/

namespace Unit.SingleSorted

open HigherCategoryTheory.SingleSorted

/-- The unit type with its unique element forms a single-sorted category, where composition is
always defined and its value is the unique element of the unit type. -/
instance instCategory (Index : Type) [Preorder Index] : Category Index Unit where
  sc _ _ := ()
  tg _ _ := ()
  pcomp _ _ _ := ⟨True, fun _ ↦ ()⟩

/-- Specialization of the unit category instance to `NCategory 1`. -/
instance (priority := 1100) inst1Category : NCategory 1 Unit := PreCategory.lift

end Unit.SingleSorted
