/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Order.TypeTags
import Mathlib.Data.Nat.Notation
import Mathlib.Order.Defs.PartialOrder
-- import Mathlib.Order.Fin.Basic

/-!
# Notation

This file defines notation and abbreviations used throughout the library.
-/

universe u

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

/-- A family of types indexed by a preordered type, used as the carrier for many-sorted categories.
-/
abbrev TypeFamily (Index : Type) := Index → Type u

/-- A family of types indexed by `FinSucc n`, used as the carrier for many-sorted $n$-categories. -/
abbrev NTypeFamily (n : ℕ) := TypeFamily.{u} (FinSucc n)

/-- A family of types indexed by `ℕ`, used as the carrier for many-sorted $\omega$-categories. -/
abbrev OmegaTypeFamily := TypeFamily.{u} ℕ

/-- Notation for `lt_trans`, used to compose strict inequality proofs when passing index arguments
to source, target, or composition operations in the many-sorted presentation. In any other context,
prefer using `lt_trans` directly. -/
scoped infixr:100 "≫" => lt_trans

end HigherCategoryTheory
