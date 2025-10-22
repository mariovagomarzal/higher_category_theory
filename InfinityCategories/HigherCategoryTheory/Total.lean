/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
TODO: Document the file.
-/

universe u

namespace HigherCategoryTheory

instance singleSortedCategoryTotal {α : Type u} : SingleSortedCategory (α×α) where
  Sc := fun _ (_, y) ↦ (y, y)
  Tg := fun _ (x, _) ↦ (x, x)
  PComp := fun _ (y₁, y₂) (x₁, x₂) ↦ ⟨y₂ = x₁, (fun _ ↦ (y₁, x₂))⟩
  pcomp_dom := by
    intros
    apply Iff.intro
    · intros
      simpa
    · intro h
      simp at h
      exact h

end HigherCategoryTheory
