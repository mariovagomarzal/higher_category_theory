/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category
import HigherCategoryTheory.SingleSorted.Functor

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

universe u v

namespace HigherCategoryTheory.SingleSorted

variable {Index : Type} [Preorder Index] {C : Type u} [S : Category Index C]

/-- A morphism `f` is a $k$-cell (via source) if `sc k f = f`. This is an abbreviation for `cell k
f`, the original definition of $k$-cells found in `Category.lean`. -/
abbrev cell_sc (k : Index) (f : C) := cell k f

/-- A morphism `f` is a $k$-cell (via target) if `tg k f = f`. -/
@[simp]
def cell_tg (k : Index) (f : C) : Prop :=
  tg k f = f

/--
The source-based and target-based definitions of $k$-cells are equivalent.

A morphism `f` satisfies `sc k f = f` if and only if it satisfies `tg k f = f`. This equivalence
relies on the idempotency axioms `tgk_sck_eq_sck` and `sck_tgk_eq_tgk`.
-/
theorem cell_sc_iff_cell_tg (k : Index) (f : C) :
    cell_sc k f ↔ cell_tg k f := by
  apply Iff.intro
  · intro sc_eq
    calc
      tg k f
      _ = tg k (sc k f) := by rw [sc_eq]
      _ = sc k f := S.tgk_sck_eq_sck k f
      _ = f := sc_eq
  · intro tg_eq
    calc
      sc k f
      _ = sc k (tg k f) := by rw [tg_eq]
      _ = tg k f := S.sck_tgk_eq_tgk k f
      _ = f := tg_eq

/-- The set of all $k$-cells using the source-based definition. This is an abbreviation for `cells k
C`, the original definition of the set of $k$-cells found in `Category.lean`. -/
abbrev cells_sc (k : Index) (C : Type u) [Category Index C] := cells k C

/-- The set of all $k$-cells using the target-based definition. This set contains all morphisms `f`
satisfying `tg k f = f`. -/
@[simp]
def cells_tg (k : Index) (C : Type u) [Category Index C] : Set C :=
  {f : C | cell_tg k f}

/--
The sets of $k$-cells defined via source and target are equal.

This theorem establishes that `cells_sc k C = cells_tg k C`, showing that both characterizations
of $k$-cells yield the same set. The proof follows from the pointwise equivalence
`cell_sc_iff_cell_tg`.
-/
theorem cells_sc_eq_cells_tg (k : Index) (C : Type u) [Category Index C] :
    cells_sc k C = cells_tg k C := by
  ext f
  exact cell_sc_iff_cell_tg k f

/-! ## Properties of underlying categories

This section establishes lemmas showing that various operations preserve the property of being an
$m$-cell when working with lower-dimensional structure (where $k < m$). These results are essential
for defining underlying categories that restrict higher categories to specific dimensions.

### Main results

* `underlying_source_is_cell`: The source of any morphism at dimension $k$ is an $m$-cell when
  $k < m$.
* `underlying_target_is_cell`: The target of any morphism at dimension $k$ is an $m$-cell when
  $k < m$.
* `underlying_comp_is_cell`: The composition of two $m$-cells at dimension $k$ (where $k < m$) is
  again an $m$-cell.
* `underlying_functor_is_cell`: Functors preserve the property of being an $m$-cell.
-/
section Underlying

variable {k m : Index}

/-- The source of any morphism at dimension $k$ is an $m$-cell when $k < m$. -/
lemma underlying_source_is_cell (f : C) (k_lt_m : k < m) : cell m (sc k f) := by
  exact S.sck_scj_eq_scj f k_lt_m

/-- The target of any morphism at dimension $k$ is an $m$-cell when $k < m$. -/
lemma underlying_target_is_cell (f : C) (k_lt_m : k < m) : cell m (tg k f) := by
  have : tg m (tg k f) = tg k f := by
    exact S.tgk_tgj_eq_tgj f k_lt_m
  apply (cell_sc_iff_cell_tg m _).mpr
  exact this

/-- The composition of two $m$-cells at dimension $k$ (where $k < m$) is again an $m$-cell. -/
lemma underlying_comp_is_cell {f g : cells m C} (dom : (S.pcomp k g f).Dom) (k_lt_m : k < m)
    : cell m (S.comp k g f (S.pcomp_dom.mp dom)) := by
  calc
    sc m (S.comp k g f (S.pcomp_dom.mp dom))
    _ = _ := S.sck_compj_eq_compj_sck k_lt_m (S.pcomp_dom.mp dom)
    _ = _ := by apply congr_comp₁ f.property g.property

variable {D : Type v} [SD : Category Index D]

/-- Functors preserve the property of being an $m$-cell. If `f` is an $m$-cell in the source
category, then `F f` is an $m$-cell in the target category. -/
lemma underlying_functor_is_cell (F : Functor Index C D) (f : cells m C)
    : F f ∈ cells m D := by
  calc
    sc m (F f)
    _ = F (sc m f) := (F.map_sc_eq_sc_map m f).symm
    _ = F f := by rw [f.property]

end Underlying

end HigherCategoryTheory.SingleSorted
