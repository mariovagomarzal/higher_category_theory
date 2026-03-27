/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category

/-!
# Orders as single-sorted categories

This file defines order-related instances of single-sorted categories.
-/

universe u

namespace Preorder.SingleSorted

open HigherCategoryTheory.SingleSorted

/-- The set of comparable pairs $\{(x, y) \mid x \leq y\}$ in a preorder. -/
abbrev LePairs (α : Type u) [Preorder α] := {(x, y) : α × α | x ≤ y}

/-- The set of comparable pairs in a preorder forms a single-sorted pre-category, where composition
corresponds to transitivity of the order relation. -/
instance instPreCategoryOfProduct (Index : Type) (α : Type u) [Preorder α] :
    PreCategory Index (LePairs α) where
  sc := fun _ ⟨(y₁, _), h⟩ ↦ ⟨(y₁, y₁), le_refl y₁⟩
  tg := fun _ ⟨(_, x₂), h⟩ ↦ ⟨(x₂, x₂), le_refl x₂⟩
  pcomp := fun _ ⟨(y₁, y₂), h₂⟩ ⟨(x₁, x₂), h₁⟩ ↦
    ⟨y₁ = x₂, fun h ↦ ⟨(x₁, y₂), calc
      x₁ ≤ x₂ := h₁
      _ = y₁ := h.symm
      _ ≤ y₂ := h₂⟩⟩

/-- Specialization of the preorder product pre-category instance to `NCategory 1`. -/
instance (priority := 1100) inst1CategoryOfProduct (α : Type u) [Preorder α] :
    NCategory 1 (LePairs α) :=
  PreCategory.lift

end Preorder.SingleSorted
