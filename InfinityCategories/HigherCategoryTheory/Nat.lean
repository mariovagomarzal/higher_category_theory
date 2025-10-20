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

instance : SingleSortedCategory (Nat×Nat) where
  Sc := fun _ (_, y₂) ↦ (y₂, y₂)
  Tg := fun _ (x₁, _) ↦ (x₁, x₁)
  PComp := fun _ (y₁, y₂) (x₁, x₂) ↦ ⟨y₂ = x₁, (fun _ ↦ (y₁, x₂))⟩
  pcomp_dom := by
    intros
    apply Iff.intro
    · intros
      simpa
    · intro h
      simp at h
      simpa

end HigherCategoryTheory
