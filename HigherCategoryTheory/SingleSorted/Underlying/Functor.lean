/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Cat
import HigherCategoryTheory.SingleSorted.Category
import HigherCategoryTheory.SingleSorted.Functor
import HigherCategoryTheory.SingleSorted.Cells
import HigherCategoryTheory.SingleSorted.Cat

/-!
# Underlying categories

This file defines the underlying $m$-category structure of an $n$-category (or $\omega$-category) by
restricting to $m$-cells, where $m < n$. This file also defines the underlying functor between the
underlying $m$-categories induced by a functor between $n$-categories (or $\omega$-categories).

## Main definitions

* `NCategory.underlying`: Given an $n$-category and $m < n$, constructs the underlying $m$-category
  whose objects are the $m$-cells of the original category.
* `OmegaCategory.underlying`: Given an $\omega$-category and $m \in \mathbb{N}$, constructs the
  underlying $m$-category.
* `NFunctor.underlying`: Restriction of a functor between $n$-categories to their underlying
  $m$-categories.
* `OmegaFunctor.underlying`: Restriction of a functor between $\omega$-categories to their
  underlying $m$-categories.

## Implementation notes

The `inherit_axiom` tactic is used extensively to prove that axioms of the underlying category
follow from the corresponding axioms of the full category. This tactic automates the common pattern
of unwrapping subtypes and applying the parent category's axioms.
-/

universe u v

namespace HigherCategoryTheory.SingleSorted

section Birestrictions

variable {Index : Type} [Preorder Index] {C : Type u} {D : Type v}
  [SC : Category Index C] [SD : Category Index D] {m : Index}

namespace Category

variable (k : Index) (k_lt_m : k < m)

/-- Birestriction of the source operation at dimension $k$ to $m$-cells. Maps an $m$-cell `f` to the
$m$-cell `sc k f`. -/
abbrev sc_birestriction : cells m C → cells m C :=
  fun f ↦ ⟨sc k f, by apply underlying_source_is_cell; assumption⟩

/-- Birestriction of the target operation at dimension $k$ to $m$-cells. Maps an $m$-cell `f` to the
$m$-cell `tg k f`. -/
abbrev tg_birestriction : cells m C → cells m C :=
  fun f ↦ ⟨tg k f, by apply underlying_target_is_cell; assumption⟩

/-- Birestriction of the partial composition at dimension $k$ to $m$-cells. Composes two $m$-cells
along dimension $k$, producing an $m$-cell when the composition is defined. -/
abbrev pcomp_birestriction : cells m C → cells m C →. cells m C :=
  fun g f ↦ {g.val ♯.[k] f.val with
    get dom := ⟨SC.comp k g f (SC.pcomp_dom.mp dom), by
      apply underlying_comp_is_cell dom; assumption⟩}

end Category

namespace Functor

/-- Birestriction of a functor's mapping to $m$-cells. Maps an $m$-cell `f` in `C` to the $m$-cell
`F f` in `D`. -/
abbrev map_birestriction (F : Functor Index C D) : cells m C → cells m D :=
  fun f ↦ ⟨F f, by apply underlying_functor_is_cell⟩

end Functor

end Birestrictions

-- TODO: Review this tactic for possible improvements.
/--
A tactic for proving axioms of underlying categories by inheritance from the parent category.

This tactic automates the common proof pattern where an axiom of an underlying category (whose
objects are $m$-cells) follows from the corresponding axiom of the full category. It introduces
variables, rewrites subtype equality to component equality, and applies the parent axiom with
simplification.
-/
macro (name := inherit_axiom) "inherit_axiom" axiom_name:ident : tactic =>
  `(tactic| (intros; rw [Subtype.mk.injEq]; try (apply $axiom_name <;> (simp at *; assumption))))

section Category

variable {n : ℕ} {C : Type u}

/--
Constructs the underlying $m$-category of an $n$-category by restricting to $m$-cells.

Given an $n$-category `S` and $m < n$, this produces an $m$-category whose objects are precisely the
$m$-cells of `S`. The source, target, and composition operations are inherited from `S`, with
dimensions reindexed to `Fin m`. All category axioms are inherited using the `inherit_axiom` tactic.
-/
@[simp]
def NCategory.underlying (S : NCategory n C) (m : Fin n) : NCategory m (cells m C) where
  sc k := S.sc_birestriction ⟨k, lt_trans k.isLt m.isLt⟩ k.isLt
  tg k := S.tg_birestriction ⟨k, lt_trans k.isLt m.isLt⟩ k.isLt
  pcomp k := S.pcomp_birestriction ⟨k, lt_trans k.isLt m.isLt⟩ k.isLt
  sck_sck_eq_sck := by inherit_axiom S.sck_sck_eq_sck
  tgk_sck_eq_sck := by inherit_axiom S.tgk_sck_eq_sck
  sck_tgk_eq_tgk := by inherit_axiom S.sck_tgk_eq_tgk
  tgk_tgk_eq_tgk := by inherit_axiom S.tgk_tgk_eq_tgk
  sck_compk_eq_sck := by inherit_axiom S.sck_compk_eq_sck
  tgk_compk_eq_tgk := by inherit_axiom S.tgk_compk_eq_tgk
  compk_sck_eq_id := by inherit_axiom S.compk_sck_eq_id
  compk_tgk_eq_id := by inherit_axiom S.compk_tgk_eq_id
  assoc := by inherit_axiom S.assoc
  sck_scj_eq_scj := by inherit_axiom S.sck_scj_eq_scj
  scj_sck_eq_scj := by inherit_axiom S.scj_sck_eq_scj
  scj_tgk_eq_scj := by inherit_axiom S.scj_tgk_eq_scj
  tgk_tgj_eq_tgj := by inherit_axiom S.tgk_tgj_eq_tgj
  tgj_tgk_eq_tgj := by inherit_axiom S.tgj_tgk_eq_tgj
  tgj_sck_eq_tgj := by inherit_axiom S.tgj_sck_eq_tgj
  sck_compj_eq_compj_sck := by inherit_axiom S.sck_compj_eq_compj_sck
  tgk_compj_eq_compj_tgk := by inherit_axiom S.tgk_compj_eq_compj_tgk
  interchange := by inherit_axiom S.interchange

/--
Constructs the underlying $m$-category of an $\omega$-category by restricting to $m$-cells.

This definition is analogous to `NCategory.underlying`, but applies to `OmegaCategory` objects.
-/
@[simp]
def OmegaCategory.underlying (S : OmegaCategory C) (m : ℕ) : NCategory m (cells m C) where
  sc k := S.sc_birestriction k k.isLt
  tg k := S.tg_birestriction k k.isLt
  pcomp k := S.pcomp_birestriction k k.isLt
  pcomp_dom := by inherit_axiom S.pcomp_dom
  sck_sck_eq_sck := by inherit_axiom S.sck_sck_eq_sck
  tgk_sck_eq_sck := by inherit_axiom S.tgk_sck_eq_sck
  sck_tgk_eq_tgk := by inherit_axiom S.sck_tgk_eq_tgk
  tgk_tgk_eq_tgk := by inherit_axiom S.tgk_tgk_eq_tgk
  sck_compk_eq_sck := by inherit_axiom S.sck_compk_eq_sck
  tgk_compk_eq_tgk := by inherit_axiom S.tgk_compk_eq_tgk
  compk_sck_eq_id := by inherit_axiom S.compk_sck_eq_id
  compk_tgk_eq_id := by inherit_axiom S.compk_tgk_eq_id
  assoc := by inherit_axiom S.assoc
  sck_scj_eq_scj := by inherit_axiom S.sck_scj_eq_scj
  scj_sck_eq_scj := by inherit_axiom S.scj_sck_eq_scj
  scj_tgk_eq_scj := by inherit_axiom S.scj_tgk_eq_scj
  tgk_tgj_eq_tgj := by inherit_axiom S.tgk_tgj_eq_tgj
  tgj_tgk_eq_tgj := by inherit_axiom S.tgj_tgk_eq_tgj
  tgj_sck_eq_tgj := by inherit_axiom S.tgj_sck_eq_tgj
  sck_compj_eq_compj_sck := by inherit_axiom S.sck_compj_eq_compj_sck
  tgk_compj_eq_compj_tgk := by inherit_axiom S.tgk_compj_eq_compj_tgk
  interchange := by inherit_axiom S.interchange

end Category

section Functor

variable {n : ℕ} {C : Type u} [nSC : NCategory n C] [ωSC : OmegaCategory C]
  {D : Type v} [nSD : NCategory n D] [ωSD : OmegaCategory D]

/--
Restricts a functor between $n$-categories to a functor between their underlying $m$-categories.
This is called the underlying $n$-functor.

Given a functor `F : C → D` between $n$-categories and $m < n$, this produces a functor between the
underlying $m$-categories `cells m C → cells m D`. The mapping and functoriality axioms are
inherited from `F` using the `inherit_axiom` tactic.
-/
@[simp]
def NFunctor.underlying (F : NFunctor n C D) (m : Fin n) :
    letI := nSC.underlying m
    letI := nSD.underlying m
    NFunctor m (cells m C) (cells m D) :=
  letI := nSC.underlying m
  letI := nSD.underlying m
  {
    map := F.map_birestriction
    map_sc_eq_sc_map := by inherit_axiom F.map_sc_eq_sc_map
    map_tg_eq_tg_map := by inherit_axiom F.map_tg_eq_tg_map
    map_comp_eq_comp_map := by inherit_axiom F.map_comp_eq_comp_map
  }

/-- Restricts a functor between $\omega$-categories to a functor between their underlying
$m$-categories. This is called the underlying $\omega$-functor.

This definition is analogous to `NFunctor.underlying`, but applies to
`OmegaFunctor` objects.
-/
@[simp]
def OmegaFunctor.underlying (F : OmegaFunctor C D) (m : ℕ) :
    letI := ωSC.underlying m
    letI := ωSD.underlying m
    NFunctor m (cells m C) (cells m D) :=
  letI := ωSC.underlying m
  letI := ωSD.underlying m
  {
    map := F.map_birestriction
    map_sc_eq_sc_map := by inherit_axiom F.map_sc_eq_sc_map
    map_tg_eq_tg_map := by inherit_axiom F.map_tg_eq_tg_map
    map_comp_eq_comp_map := by inherit_axiom F.map_comp_eq_comp_map
  }

end Functor

section UnderlyingFunctor

/-- The underlying $m$-category instance for the type of $m$-cells of an $n$-category. -/
instance {n : ℕ} {m : Fin n} {C : Type u} [S : NCategory n C] : NCategory m (cells m C) :=
  S.underlying m

open CategoryTheory in
/-- The underlying functor from the category of $n$-categories to the category of $m$-categories
(where $m < n$). Sends each $n$-category to its underlying $m$-category and each functor to its
restriction to $m$-cells. -/
@[simp]
def UnderlyingFunctor (n m : ℕ∞) (m_le_n : m ≤ n) : ICat.{u} n ⥤ ICat.{u} m :=
  match n, m with
  | fin n, fin m => by sorry
  | ω, fin m => by sorry
  | ω, ω => by sorry

end UnderlyingFunctor

end HigherCategoryTheory.SingleSorted
