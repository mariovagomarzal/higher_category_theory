/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Defs.SingleSortedCategory
import HigherCategoryTheory.SingleSorted.Defs.Cell

/-!
TODO: Comment.
-/

universe u

namespace HigherCategoryTheory

open SingleSortedCategory

/-- TODO: Comment. -/
class SingleSortedOmegaCategory (obj : Type u) extends SingleSortedCategory ℕ obj where
  /-- Every element is a k-cell for some `k : ℕ`. -/
  is_cell : ∀ f : obj, ∃ k : ℕ, cell k f

end HigherCategoryTheory
