/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
# Cells in single-sorted higher-order categories

This file defines the notion of $k$-cells in single-sorted categories and related concepts including
discreteness properties.

In a single-sorted $n$-category or $\omega$-category, a morphism $f$ is called a **$k$-cell** if
it satisfies $\mathrm{sc}_k(f) = f$, or equivalently, $\mathrm{tg}_k(f) = f$. The set of all
$k$-cells is denoted $C_k$.

A category is **discrete** at dimension $k$ if every morphism is a $k$-cell, meaning there are
no non-identity morphisms at that dimension.

For $\omega$-categories, every morphism must be a $k$-cell for some $k \in \mathbb{N}$, which
means $C = \bigcup_{k \in \mathbb{N}} C_k$. This file provides constructors for
$\omega$-categories based on this union property and on discreteness conditions.
-/

universe u

namespace HigherCategoryTheory

namespace SingleSortedCategoryFamily

/-- A morphism `f` is a $k$-cell (via source) if `sc k f = f`. This means `f` behaves as an
identity at dimension $k$. -/
def id_sc {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) (f : Obj) : Prop :=
  sc k f = f

/-- A morphism `f` is a $k$-cell (via target) if `tg k f = f`. This means `f` behaves as an
identity at dimension $k$. -/
def id_tg {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) (f : Obj) : Prop :=
  tg k f = f

/-- The properties `id_sc k f` and `id_tg k f` are equivalent: a morphism is a $k$-cell via
source if and only if it is a $k$-cell via target. -/
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

/-- The set $C_k$ of all $k$-cells in `Obj`, defined as those morphisms `f` satisfying
`sc k f = f`. -/
def cell (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) : Set Obj :=
  {f : Obj | id_sc k f}

/-- The set of all $k$-cells in `Obj`, defined via the target operation as those morphisms `f`
satisfying `tg k f = f`. -/
def cell_tg (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) : Set Obj :=
  {f : Obj | id_tg k f}

/-- The source-based and target-based definitions of $k$-cells coincide: `cell Obj k = cell_tg
Obj k`. -/
theorem cell_eq_cell_tg (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) :
    cell Obj k = cell_tg Obj k := by
  ext f
  exact id_sc_iff_id_tg k f

/-- A category `Obj` is discrete at dimension $k$ if every morphism is a $k$-cell, meaning
there are no non-identity morphisms at dimension $k$. -/
def is_discrete_at (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) : Prop :=
  ∀ f : Obj, f ∈ cell Obj k

/-- A category `Obj` is discrete above dimension $k$ if for every dimension $n \geq k$, all
morphisms are $n$-cells. This means there are no non-identity morphisms at any dimension greater
than or equal to $k$. -/
def is_discrete_above (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] (k : index) : Prop :=
  ∀ {f : Obj} {n : index}, n ≥ k → f ∈ cell Obj n

/-- A category `Obj` is discrete if it is discrete at every dimension, meaning every morphism
is a $k$-cell for all $k$. This corresponds to a category with only identity morphisms. -/
def is_discrete (Obj : Type u) {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily Obj index] : Prop :=
  ∀ {f : Obj} {k : index}, f ∈ cell Obj k

end SingleSortedCategoryFamily

namespace SingleSortedOmegaCategory

open SingleSortedCategoryFamily

/-- In an $\omega$-category, every morphism `f` belongs to $C_k$ for some $k : \mathbb{N}$.
This is equivalent to the condition $C = \bigcup_{k \in \mathbb{N}} C_k$. -/
theorem is_union_cells {Obj : Type u} [SingleSortedOmegaCategory Obj] :
    ∀ f : Obj, f ∈ ⋃ k : Nat, cell Obj k := by
  intro f
  simp
  exact has_cell f

/-- Given a structure of `SingleSorted2CategoryFamily` on `Obj` (and index `Nat`), if `Obj` can be
expressed as the union of its $k$-cells, then we can construct a `SingleSortedOmegaCategory`
structure on `Obj` because the `has_cell` axiom is satisfied. -/
def fromUnionCells {Obj : Type u} [SingleSorted2CategoryFamily Obj Nat]
    (union_cells : ∀ f : Obj, f ∈ ⋃ k : Nat, cell Obj k) :
    SingleSortedOmegaCategory Obj where
  has_cell := by
    intro f
    simp at union_cells
    exact union_cells f

/--
Given a structure of `SingleSorted2CategoryFamily` on `Obj` and index `Nat` and, if there exists
a natural number `n` such that `Obj` is discrete above dimension `n`, then we can construct a
`SingleSortedOmegaCategory` structure on `Obj` since every morphism will be a $k$-cell for any
`k ≥ n`.
-/
def fromDiscreteAbove {Obj : Type u} [SingleSorted2CategoryFamily Obj Nat]
    (discrete_above : ∃ n : Nat, is_discrete_above Obj n) :
    SingleSortedOmegaCategory Obj where
  has_cell := by
    intro f
    rcases discrete_above with ⟨n, h_discrete⟩
    use n
    exact h_discrete (le_refl n)

end SingleSortedOmegaCategory

end HigherCategoryTheory
