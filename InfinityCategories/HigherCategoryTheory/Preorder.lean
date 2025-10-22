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

namespace Preorder

open HigherCategoryTheory

instance singleSortedCategoryPreorderProduct (α : Type u) [Preorder α] :
    SingleSortedCategory ({(x, y) : α×α | x ≤ y}) where
  Sc := fun _ ⟨(x, _), h⟩ ↦ ⟨(x, x), le_refl x⟩
  Tg := fun _ ⟨(_, y), h⟩ ↦ ⟨(y, y), le_refl y⟩
  PComp := fun _ ⟨(x₂, y₂), h₂⟩ ⟨(x₁, y₁), h₁⟩ ↦
    ⟨x₂ = y₁, fun h ↦ ⟨(x₁, y₂), calc
      x₁ ≤ y₁ := h₁
      _ = x₂ := h.symm
      _ ≤ y₂ := h₂⟩⟩
  pcomp_dom := by
    intros
    apply Iff.intro
    · intros
      simpa
    · intro h
      simp
      simp at h
      exact h

end Preorder
