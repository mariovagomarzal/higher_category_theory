/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category

/-!
# Orders as single-sorted categories

This file define order-related instances of single-sorted categories.
-/

universe u

namespace Preorder

open HigherCategoryTheory

/-- The set of comparable pairs $\{(x, y) \mid x \leq y\}$ in a preorder forms a single-sorted
category, where composition corresponds to transitivity of the order relation. -/
instance instSingleSorted1CategoryOfProduct (α : Type u) [Preorder α] :
    SingleSortedNCategory 1 ({(x, y) : α × α | x ≤ y}) where
  sc := fun _ ⟨(y₁, _), h⟩ ↦ ⟨(y₁, y₁), le_refl y₁⟩
  tg := fun _ ⟨(_, x₂), h⟩ ↦ ⟨(x₂, x₂), le_refl x₂⟩
  pcomp := fun _ ⟨(y₁, y₂), h₂⟩ ⟨(x₁, x₂), h₁⟩ ↦
    ⟨y₁ = x₂, fun h ↦ ⟨(x₁, y₂), calc
      x₁ ≤ x₂ := h₁
      _ = y₁ := h.symm
      _ ≤ y₂ := h₂⟩⟩

end Preorder
