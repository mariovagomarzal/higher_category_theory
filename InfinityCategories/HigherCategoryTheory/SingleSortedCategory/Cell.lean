/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
TODO: Document this file.
-/

universe u

namespace HigherCategoryTheory

namespace SingleSortedCategoryFamily

def id_sc {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) (f : Obj) : Prop :=
  sc k f = f

def id_tg {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) (f : Obj) : Prop :=
  tg k f = f

theorem id_sc_iff_id_tg {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) (f : Obj) :
    id_sc k f ↔ id_tg k f := by
  apply Iff.intro
  · intro sc_eq
    calc
      tg k f
      _ = tg k (sc k f) := congrArg (tg k) sc_eq.symm
      _ = sc k f := tg_sc_is_sc
      _ = f := sc_eq
  · intro tg_eq
    calc
      sc k f
      _ = sc k (tg k f) := congrArg (sc k) tg_eq.symm
      _ = tg k f := sc_tg_is_tg
      _ = f := tg_eq

def cell (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) : Set Obj :=
  {f : Obj | id_sc k f}

def cell_tg (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) : Set Obj :=
  {f : Obj | id_tg k f}

theorem cell_eq_cell_tg (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) :
    cell Obj k = cell_tg Obj k := by
  ext f
  exact id_sc_iff_id_tg k f

def is_discrete_at (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) : Prop :=
  ∀ f : Obj, f ∈ cell Obj k

def is_discrete_above (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) : Prop :=
  ∀ {f : Obj} {n : index}, n ≥ k → f ∈ cell Obj n

def is_discrete (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] : Prop :=
  ∀ {f : Obj} {k : index}, f ∈ cell Obj k

end SingleSortedCategoryFamily

namespace SingleSortedOmegaCategory

open SingleSortedCategoryFamily

theorem is_union_cells {Obj : Type u} [SingleSortedOmegaCategory Obj] :
    ∀ f : Obj, f ∈ ⋃ k : Nat, cell Obj k := by
  intro f
  simp
  exact has_cell f

def fromUnionCells {Obj : Type u} [SingleSorted2CategoryFamily Obj Nat]
    (union_cells : ∀ f : Obj, f ∈ ⋃ k : Nat, cell Obj k) :
    SingleSortedOmegaCategory Obj where
  has_cell := by
    intro f
    simp at union_cells
    exact union_cells f

def fromDiscreteAbove {Obj : Type u} (n : Nat)
    [S : SingleSorted2CategoryFamily Obj Nat]
    (discrete_above : is_discrete_above Obj n) :
    SingleSortedOmegaCategory Obj where
  has_cell := by
    intro f
    use n
    exact discrete_above (by rfl)

end SingleSortedOmegaCategory

end HigherCategoryTheory
