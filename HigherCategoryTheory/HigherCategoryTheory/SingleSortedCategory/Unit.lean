/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
# The unit type as single-sorted categories

This file shows that the unit type can be given single-sorted category and 2-category structures,
representing the trivial category with one object and one morphism.
-/

namespace Unit

open HigherCategoryTheory

/-- The unit type `Unit` is a single-sorted category with a single morphism (the unique element
`()`), which is both its own source and target. -/
instance instSingleSortedCategory : SingleSortedCategory Unit where
  Sc _ _ := ()
  Tg _ _ := ()
  PComp _ _ _ := ⟨True, (fun _ ↦ ())⟩
  pcomp_dom := by
    intros
    apply Iff.intro
    · intros
      rfl
    · intros
      trivial

/-- The unit type `Unit` is a single-sorted 2-category with a single morphism (the unique element
`()`), which is both its own source and target. -/
instance instSingleSorted2Category : SingleSorted2Category Unit where
  Sc _ _ := ()
  Tg _ _ := ()
  PComp _ _ _ := ⟨True, (fun _ ↦ ())⟩
  pcomp_dom := by
    intros
    apply Iff.intro
    · intros
      rfl
    · intros
      trivial

end Unit
