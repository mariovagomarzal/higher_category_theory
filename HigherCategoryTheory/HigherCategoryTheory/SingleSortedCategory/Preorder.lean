/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Basic

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
instance instSingleSortedCategoryOfProduct (α : Type u) [Preorder α] :
    SingleSortedCategory ({(x, y) : α × α | x ≤ y}) where
  Sc := fun _ ⟨(y₁, _), h⟩ ↦ ⟨(y₁, y₁), le_refl y₁⟩
  Tg := fun _ ⟨(_, x₂), h⟩ ↦ ⟨(x₂, x₂), le_refl x₂⟩
  PComp := fun _ ⟨(x₁, x₂), h₁⟩ ⟨(y₁, y₂), h₂⟩ ↦
    ⟨y₁ = x₂, fun h ↦ ⟨(x₁, y₂), calc
      x₁ ≤ x₂ := h₁
      _ = y₁ := h.symm
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
