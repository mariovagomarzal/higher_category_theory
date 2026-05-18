/-
Copyright (c) 2026 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Cat
import HigherCategoryTheory.ManySorted.Category
import HigherCategoryTheory.ManySorted.Functor
import HigherCategoryTheory.ManySorted.Cat

/-!
# Underlying categories

This file defines the underlying $m$-category structure of a many-sorted $n$-category (or
$\omega$-category) by restricting the type family to its first $m + 1$ types, where $m < n$. This
file also defines the underlying functor between the underlying $m$-categories induced by a functor
between many-sorted $n$-categories (or $\omega$-categories).

## Main definitions

* `NCategory.underlying`: Given a many-sorted $n$-category and $m < n$, constructs the underlying
  $m$-category on the restricted type family.
* `OmegaCategory.underlying`: Given a many-sorted $\omega$-category and $m \in \mathbb{N}$,
  constructs the underlying $m$-category.
* `NFunctor.underlying`: Restriction of a functor between many-sorted $n$-categories to their
  underlying $m$-categories.
* `OmegaFunctor.underlying`: Restriction of a functor between many-sorted $\omega$-categories to
  their underlying $m$-categories.
* `UnderlyingFunctor`: The functor from `ICat n` to `ICat m` sending each category and functor to
  its underlying lower-dimensional counterpart.
-/

universe u v

namespace HigherCategoryTheory.ManySorted

/-- The restriction of a `NTypeFamily n` to `NTypeFamily m` for `m < n` -/
abbrev NTypeFamily.underlying {n : ℕ} (C : NTypeFamily.{u} n) (m : Fin n) : NTypeFamily m :=
  fun k ↦ C ⟨k, by omega⟩

/-- The restriction of an `OmegaTypeFamily` to `NTypeFamily m` for any natural `m` -/
abbrev OmegaTypeFamily.underlying (C : OmegaTypeFamily.{u}) (m : ℕ) : NTypeFamily m :=
  fun k ↦ C k

section Category

variable {n : ℕ} {C : NTypeFamily.{u} n}

/--
Constructs the underlying $m$-category of a many-sorted $n$-category by restricting the type family.

Given a many-sorted $n$-category `S` and $m < n$, this produces a many-sorted $m$-category on the
restricted family. The source, target, identity, and composition operations are inherited from `S`,
with dimensions reindexed to `Fin m`. All category axioms are inherited from `S`.
-/
@[simp]
def NCategory.underlying (S : NCategory n C) (m : Fin n) :
    NCategory m (NTypeFamily.underlying C m) where
  sc j_lt_k f := S.sc j_lt_k f
  tg j_lt_k f := S.tg j_lt_k f
  idm j_lt_k f := S.idm j_lt_k f
  pcomp j_lt_k g f := S.pcomp j_lt_k g f
  sckj_compkj_eq_sckj := S.sckj_compkj_eq_sckj
  tgkj_compkj_eq_tgkj := S.tgkj_compkj_eq_tgkj
  compkj_idmkj_sckj_eq_id := fun j_lt_k => S.compkj_idmkj_sckj_eq_id j_lt_k
  compkj_tgkj_idmkj_eq_id := fun j_lt_k => S.compkj_tgkj_idmkj_eq_id j_lt_k
  assoc := S.assoc
  sckj_compki_eq_compji_sckj := fun sc_tg_ki_gf => S.sckj_compki_eq_compji_sckj sc_tg_ki_gf
  tgkj_compki_eq_compji_tgkj := fun sc_tg_ki_gf => S.tgkj_compki_eq_compji_tgkj sc_tg_ki_gf
  idmkj_compji_eq_compki_idmkj := S.idmkj_compji_eq_compki_idmkj
  interchange := by
    intros
    apply S.interchange <;> assumption

/--
Constructs the underlying $m$-category of a many-sorted $\omega$-category by restricting the type
family.

This definition is analogous to `NCategory.underlying`, but applies to `OmegaCategory` objects.
-/
@[simp]
def OmegaCategory.underlying {C : OmegaTypeFamily.{u}} (S : OmegaCategory C) (m : ℕ) :
    NCategory m (OmegaTypeFamily.underlying C m) where
  sc j_lt_k f := S.sc j_lt_k f
  tg j_lt_k f := S.tg j_lt_k f
  idm j_lt_k f := S.idm j_lt_k f
  pcomp j_lt_k g f := S.pcomp j_lt_k g f
  sckj_compkj_eq_sckj := S.sckj_compkj_eq_sckj
  tgkj_compkj_eq_tgkj := S.tgkj_compkj_eq_tgkj
  compkj_idmkj_sckj_eq_id := S.compkj_idmkj_sckj_eq_id
  compkj_tgkj_idmkj_eq_id := S.compkj_tgkj_idmkj_eq_id
  assoc := S.assoc
  sckj_compki_eq_compji_sckj := fun sc_tg_ki_gf => S.sckj_compki_eq_compji_sckj sc_tg_ki_gf
  tgkj_compki_eq_compji_tgkj := fun sc_tg_ki_gf => S.tgkj_compki_eq_compji_tgkj sc_tg_ki_gf
  idmkj_compji_eq_compki_idmkj := fun sc_tg_ji_gf => S.idmkj_compji_eq_compki_idmkj sc_tg_ji_gf
  interchange := by
    intros
    apply S.interchange <;> assumption

end Category

section Functor

variable {n : ℕ} {C : NTypeFamily.{u} n} [SC : NCategory n C]
  {D : NTypeFamily.{v} n} [SD : NCategory n D]

/--
Restricts a functor between many-sorted $n$-categories to a functor between their underlying
$m$-categories. This is called the underlying $n$-functor.

Given a functor `F` between many-sorted $n$-categories and $m < n$, this produces a functor between
the underlying $m$-categories. The mapping is inherited from `F`, restricted to dimensions at most
$m$. The functoriality axioms are inherited from `F`.
-/
@[simp]
def NFunctor.underlying (F : NFunctor n C D) (m : Fin n) :
    letI := SC.underlying m
    letI := SD.underlying m
    NFunctor m (NTypeFamily.underlying C m) (NTypeFamily.underlying D m) :=
  letI := SC.underlying m
  letI := SD.underlying m
  {
    map := fun k f ↦ F.map ⟨k, by omega⟩ f
    map_comp_eq_comp_map := F.map_comp_eq_comp_map
  }

/--
Restricts a functor between many-sorted $\omega$-categories to a functor between their underlying
$m$-categories. This is called the underlying $\omega$-functor.

This definition is analogous to `NFunctor.underlying`, but applies to `OmegaFunctor` objects.
-/
@[simp]
def OmegaFunctor.underlying {C : OmegaTypeFamily.{u}} {D : OmegaTypeFamily.{v}}
    [SC : OmegaCategory C] [SD : OmegaCategory D]
    (F : OmegaFunctor C D) (m : ℕ) :
    letI := SC.underlying m
    letI := SD.underlying m
    NFunctor m (OmegaTypeFamily.underlying C m) (OmegaTypeFamily.underlying D m) :=
  letI := SC.underlying m
  letI := SD.underlying m
  {
    map := fun k f ↦ F.map k f
    map_comp_eq_comp_map := F.map_comp_eq_comp_map
  }

end Functor

section UnderlyingFunctor

open CategoryTheory

/-- The underlying functor from the category of many-sorted $n$-categories to the category of
many-sorted $m$-categories for finite dimensions, where $m < n$. Sends each $n$-category to its
underlying $m$-category and each functor to its restriction to dimensions at most $m$. -/
def FinUnderlyingFunctor (n : ℕ) (m : Fin n) : ICat.{u} n ⥤ ICat.{u} m where
  obj C := letI := NCategory.underlying C.str m; Cat.of (NTypeFamily.underlying C m)
  map {C D} F := F.underlying m

/-- The underlying functor from the category of many-sorted $\omega$-categories to the category of
many-sorted $m$-categories. Sends each $\omega$-category to its underlying $m$-category and each
functor to its restriction to dimensions at most $m$. -/
def OmegaUnderlyingFunctor (m : ℕ) : ICat.{u} ω ⥤ ICat.{u} m where
  obj C := letI := OmegaCategory.underlying C.str m; Cat.of (OmegaTypeFamily.underlying C m)
  map {C D} F := F.underlying m

open CategoryTheory in
/-- The underlying functor from the category of many-sorted $n$-categories to the category of
many-sorted $m$-categories (where $m \leq n$). Sends each $n$-category to its underlying
$m$-category and each functor to its restriction to dimensions at most $m$. -/
@[simp]
def UnderlyingFunctor (n m : ℕ∞) (m_le_n : m ≤ n) : ICat.{u} n ⥤ ICat.{u} m :=
  match n, m with
  | fin n, fin m =>
    if h : m < n then
      FinUnderlyingFunctor n ⟨m, h⟩
    else by
      simp only [ENat.some_eq_coe, Nat.cast_le] at m_le_n
      have : m = n := m_le_n.eq_of_not_lt h
      rw [this]
      exact 𝟭 (ICat.{u} n)
  | ω, fin m => OmegaUnderlyingFunctor m
  | ω, ω => 𝟭 (ICat.{u} ω)

end UnderlyingFunctor

end HigherCategoryTheory.ManySorted
