/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Defs.SingleSortedCategory

/-!
# Cells in single-sorted higher-order categories

This file defines the notion of $k$-cells in single-sorted categories.

In a single-sorted $n$-category or $\omega$-category, a morphism $f$ is called a **$k$-cell** if
it satisfies $\mathrm{sc}_k(f) = f$, or equivalently, $\mathrm{tg}_k(f) = f$.
-/

universe u

namespace HigherCategoryTheory

variable {index : Type} [LinearOrder index] {obj : Type u} [SingleSortedCategory index obj]

namespace SingleSortedCategory

open PreSingleSortedCategory

/-- A morphism `f` is a $k$-cell (via source) if `sc k f = f`. This means `f` behaves as an
identity at dimension $k$. -/
@[simp]
def cell_sc (k : index) (f : obj) : Prop :=
  sc k f = f

/-- A morphism `f` is a $k$-cell (via target) if `tg k f = f`. This means `f` behaves as an
identity at dimension $k$. -/
@[simp]
def cell_tg (k : index) (f : obj) : Prop :=
  tg k f = f

/-- TODO: Comment. -/
@[simp]
abbrev cell (k : index) (f : obj) : Prop :=
  cell_sc k f

/-- TODO: Comment. -/
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

/-- TODO: Comment. -/
@[simp]
def cells_sc (k : index) (obj : Type u) [SingleSortedCategory index obj] : Set obj :=
  {f : obj | cell_sc k f}

/-- TODO: Comment. -/
@[simp]
def cells_tg (k : index) (obj : Type u) [SingleSortedCategory index obj] : Set obj :=
  {f : obj | cell_tg k f}

/-- TODO: Comment. -/
theorem cell_sc_eq_cell_tg (k : index) :
    cells_sc k obj = cells_tg k obj := by
  ext f
  exact cell_sc_iff_cell_tg k f

/-- TODO: Comment. -/
@[simp]
abbrev cells (k : index) (obj : Type u) [SingleSortedCategory index obj] : Set obj :=
  cells_sc k obj

end SingleSortedCategory

end HigherCategoryTheory
