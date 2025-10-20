/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
TODO: Document the file.
-/

namespace HigherCategoryTheory

instance : SingleSortedCategory Unit where
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

end HigherCategoryTheory
