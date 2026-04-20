/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Order.TypeTags
import Mathlib.Data.Nat.Notation
import Mathlib.Order.Defs.PartialOrder

/-!
# Notation

This file defines notation and abbreviations used throughout the library.
-/

namespace HigherCategoryTheory

-- TODO: Instead of inheriting the docstring, explain the notation relating to `ℕ∞`.
/- In some contexts, we use `ℕ∞` for indexing the category structure dimension, i.e., we use the top
element of `ℕ∞` to represent $\omega$-categories and the finite elements to represent
$n$-categories. The following notation provides concise syntax for these two cases. -/

/-- Notation for the top element of an order with top (`Top.top`). In our context, it represents the
index of an $\omega$-category in `ℕ∞`. -/
scoped notation "ω" => Top.top

/-- Notation for the injection into a `WithTop` type (`WithTop.some`). In our context, it represents
the index of an $n$-category in `ℕ∞`. -/
scoped notation "fin" => WithTop.some

/-- Abbreviation for `Fin (n + 1)`, used as the index type for $n$-categories in the many-sorted
presentation. -/
abbrev FinSucc (n : ℕ) := Fin (n + 1)

/-- Notation for `lt_trans`, used to compose strict inequality proofs when passing index arguments
to source, target, or composition operations in the many-sorted presentation. In any other context,
prefer using `lt_trans` directly. -/
scoped infixr:100 "≫" => lt_trans

end HigherCategoryTheory
