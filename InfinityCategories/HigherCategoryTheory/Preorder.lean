/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
# Preorders as single-sorted categories

This file shows that preorders can be viewed as single-sorted categories where morphisms
correspond to the order relation.
-/

universe u

namespace Preorder

open HigherCategoryTheory

/-- The set of comparable pairs $\{(x, y) \mid x \leq y\}$ in a preorder forms a single-sorted
category, where composition corresponds to transitivity of the order relation. -/
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
