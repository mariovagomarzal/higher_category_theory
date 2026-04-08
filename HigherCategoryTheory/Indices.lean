/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Order.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Basic

/-!
# Indices: types, operations, and notation

This file provides the foundational support for working with indices throughout the formalization.
Indices appear in both the single-sorted and many-sorted presentations of higher categories, where
they typically represent dimensions.

## Main definitions

* `IndexBelow k` — the subtype `{ j : Index // j < k }` of indices strictly below `k`.
-/

namespace HigherCategoryTheory

section ENat

/- In some contexts, we use `ℕ∞` for indexing the category structure dimension, i.e., we use the top
element of `ℕ∞` to represent $\omega$-categories and the finite elements to represent
$n$-categories. The following notation provides concise syntax for these two cases. -/
@[inherit_doc] notation "ω" => Top.top
@[inherit_doc] notation "fin" => WithTop.some

end ENat

section IndexBelow

variable {Index : Type} [Preorder Index]

/-- The subtype of indices strictly below `k` in a preorder. Used to represent dimension pairs
`(k, j)` with `j < k` in the many-sorted formalization of higher categories. -/
abbrev IndexBelow (k : Index) := { j : Index // j < k }

namespace IndexBelow

variable {k : Index} {j : IndexBelow k}

/-- The proof that `j` is strictly below `k`. -/
def isLt (j : IndexBelow k) : j < k := j.property

/-- Coercion allowing an index below `j : IndexBelow k` to be viewed as an index below `j.val`. This
enables working with nested dimension chains: given `i : IndexBelow j` where `j : IndexBelow k`, we
can coerce `i` to `IndexBelow j.val` to use it in operations parameterized by the underlying index
value. -/
instance coeIndexBelowVal : Coe (IndexBelow j) (IndexBelow j.val) where
  coe i := ⟨i, i.isLt⟩

end IndexBelow

end IndexBelow

end HigherCategoryTheory
