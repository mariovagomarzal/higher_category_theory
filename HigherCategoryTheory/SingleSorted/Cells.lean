/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category

/-!
# Cells in single-sorted categories

When defining single-sorted categories, $k$-cells are defined using the source operation: a morphism
`f` is a $k$-cell if `sc k f = f`. This file shows that an equivalent characterization exists using
the target operation: `tg k f = f`.

Other properties about $k$-cells are also established in this file.

## Main results

* `cell_sc_iff_cell_tg`: The source-based and target-based definitions of $k$-cells are equivalent.
* `cells_sc_eq_cells_tg`: The sets of $k$-cells defined via source and target are equal.
-/

universe u

namespace HigherCategoryTheory

variable {index : Type} [LinearOrder index] {obj : Type u} [SingleSortedCategory index obj]

/-- A morphism `f` is a $k$-cell (via source) if `sc k f = f`. This is an abbreviation for `cell k
f`, the original definition of $k$-cells found in `Category.lean`. -/
abbrev cell_sc (k : index) (f : obj) := cell k f

/-- A morphism `f` is a $k$-cell (via target) if `tg k f = f`. -/
@[simp]
def cell_tg (k : index) (f : obj) : Prop :=
  tg k f = f

open PreSingleSortedCategory in
/--
The source-based and target-based definitions of $k$-cells are equivalent.

A morphism `f` satisfies `sc k f = f` if and only if it satisfies `tg k f = f`. This equivalence
relies on the idempotency axioms `tgk_sck_is_sck` and `sck_tgk_is_tgk`.
-/
theorem cell_sc_iff_cell_tg (k : index) (f : obj) :
    cell_sc k f ↔ cell_tg k f := by
  apply Iff.intro
  · intro sc_eq
    calc
      tg k f
      _ = tg k (sc k f) := by rw [sc_eq]
      _ = sc k f := tgk_sck_is_sck k f
      _ = f := sc_eq
  · intro tg_eq
    calc
      sc k f
      _ = sc k (tg k f) := by rw [tg_eq]
      _ = tg k f := sck_tgk_is_tgk k f
      _ = f := tg_eq

/-- The set of all $k$-cells using the source-based definition. This is an abbreviation for `cells k
obj`, the original definition of the set of $k$-cells found in `Category.lean`. -/
abbrev cells_sc (k : index) (obj : Type u) [SingleSortedCategory index obj] := cells k obj

/-- The set of all $k$-cells using the target-based definition. This set contains all morphisms `f`
satisfying `tg k f = f`. -/
@[simp]
def cells_tg (k : index) (obj : Type u) [SingleSortedCategory index obj] : Set obj :=
  {f : obj | cell_tg k f}

/--
The sets of $k$-cells defined via source and target are equal.

This theorem establishes that `cells_sc k obj = cells_tg k obj`, showing that both characterizations
of $k$-cells yield the same set. The proof follows from the pointwise equivalence
`cell_sc_iff_cell_tg`.
-/
theorem cells_sc_eq_cells_tg (k : index) (obj : Type u) [SingleSortedCategory index obj] :
    cells_sc k obj = cells_tg k obj := by
  ext f
  exact cell_sc_iff_cell_tg k f

end HigherCategoryTheory
