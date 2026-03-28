/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Order.Basic

/-!
# Index types for the many-sorted formalization

This file defines `IndexBelow`, a subtype of indices strictly below a given bound in a preorder.
In the many-sorted presentation of higher categories, each operation is parameterized by a pair of
dimensions `(k, j)` with `j < k`. `IndexBelow k` packages an index together with a proof that it
is strictly less than `k`, enforcing this constraint at the type level.

## Main definitions

* `IndexBelow k` — the subtype `{ j : Index // j < k }`.
* `IndexBelow.isLt` — extracts the proof that `j < k`.
* `IndexBelow.coeIndexBelowVal` — coercion from `IndexBelow j` to `IndexBelow j.val` when
  `j : IndexBelow k`, enabling nested dimension chains `i < j < k`.
-/

namespace HigherCategoryTheory

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

end HigherCategoryTheory
