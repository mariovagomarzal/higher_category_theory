/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Defs.SingleSortedCategory
import Mathlib.Order.Fin.Basic

/-!
TODO: Comment.
-/

universe u

namespace HigherCategoryTheory

/-- TODO: Comment. -/
abbrev SingleSortedNCategory (n : ℕ) (obj : Type u) :=
  SingleSortedCategory (Fin n) obj

end HigherCategoryTheory
