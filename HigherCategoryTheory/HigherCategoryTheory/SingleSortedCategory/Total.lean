/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
# The total category on pairs

This file defines a single-sorted category structure on the product type $\alpha \times \alpha$
for any type $\alpha$.
-/

universe u

namespace HigherCategoryTheory

/-- The product $\alpha \times \alpha$ is a single-sorted category where pairs $(x, y)$ represent
morphisms from $x$ to $y$. Two pairs $(y_1, y_2)$ and $(x_1, x_2)$ are composable when
$y_2 = x_1$, with their composite being $(y_1, x_2)$. -/
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
