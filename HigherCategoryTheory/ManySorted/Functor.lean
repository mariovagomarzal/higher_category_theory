/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.ManySorted.Category

/-!
# Functors between many-sorted categories

This file defines functors between many-sorted categories and establishes the basic categorical
structure of functor composition and identity.

A functor between many-sorted categories is a family of maps, one for each dimension, that
collectively preserve sources, targets, identities, and composition at each pair of dimensions.

## Main definitions

* `Functor`: A structure-preserving family of maps between many-sorted categories.
* `NFunctor`: Functors between many-sorted $n$-categories.
* `OmegaFunctor`: Functors between many-sorted $\omega$-categories.

## Notation

* `F.map k f`: Application of functor `F` to a `k`-morphism `f`.
* `G ⊚ F`: Composition of functors `G` and `F`.
* `idₘ C`: The identity functor on a many-sorted category `C`.
-/

universe u₁ u₂ u₃

namespace HigherCategoryTheory.ManySorted

/--
A functor between many-sorted categories.

A `Functor index C D` is a structure-preserving family of maps from a many-sorted category `C` to
a many-sorted category `D`. It consists of:
* A family of functions `map k : C k → D k` on morphisms at each dimension `k`.
* Proofs that the family preserves sources, targets, identities, and composition at each pair
  of dimensions.
-/
structure Functor (index : Type) [LinearOrder index] (C : index → Type u₁) (D : index → Type u₂)
    [Category index C] [Category index D] where
  /-- The underlying family of functions on morphisms. -/
  map : (k : index) → C k → D k
  /-- The map preserves sources at dimensions `(k, j)`. -/
  map_sc_eq_sc_map : ∀ {k j : index} (f : C k) (_ : j < k),
      map j (sc k j f) = sc k j (map k f) := by
    hcat_disch
  /-- The map preserves targets at dimensions `(k, j)`. -/
  map_tg_eq_tg_map : ∀ {k j : index} (f : C k) (_ : j < k),
      map j (tg k j f) = tg k j (map k f) := by
    hcat_disch
  /-- The map preserves identities at dimensions `(k, j)`. -/
  map_idm_eq_idm_map : ∀ {k j : index} (f : C j) (_ : j < k),
      map k (idm k j f) = idm k j (map j f) := by
    hcat_disch
  /-- If `g` and `f` are `(k, j)`-composable in `C`, then `F k g` and `F k f` are
  `(k, j)`-composable in `D`. This is an auxiliary method for `map_comp_eq_comp_map`. -/
  protected comp_map {k j : index} {f g : C k} (j_lt_k : j < k)
      (sc_tg_gf : sc_is_tg k j g f) :
      sc_is_tg k j (map k g) (map k f) := calc
    sc k j (map k g)
    _ = map j (sc k j g) := (map_sc_eq_sc_map g j_lt_k).symm
    _ = map j (tg k j f) := by rw [sc_tg_gf]
    _ = tg k j (map k f) := map_tg_eq_tg_map f j_lt_k
  /-- The map preserves composition at dimensions `(k, j)`. -/
  map_comp_eq_comp_map : ∀ {k j : index} {f g : C k} (j_lt_k : j < k)
      (sc_tg_gf : sc_is_tg k j g f),
      map k (g ♯[k,j] f ← sc_tg_gf) =
      (map k g) ♯[k,j] (map k f) ← (comp_map j_lt_k sc_tg_gf) := by
    hcat_disch

-- Use `Functor` axioms as simp lemmas.
open Functor in
attribute [simp] map_sc_eq_sc_map map_tg_eq_tg_map map_idm_eq_idm_map map_comp_eq_comp_map

namespace Functor

variable {index : Type} [LinearOrder index]
  {C : index → Type u₁} [Category index C]
  {D : index → Type u₂} [Category index D]
  {E : index → Type u₃} [Category index E]

/-- Composition of many-sorted functors. Given functors `F : C → D` and `G : D → E`, their
composite `G ⊚ F : C → E` is defined componentwise by `(G ⊚ F) k f = G k (F k f)`. -/
@[simp]
def comp (G : Functor index D E) (F : Functor index C D) :
    Functor index C E where
  map k f := G.map k (F.map k f)
  map_sc_eq_sc_map := by
    intro k j f j_lt_k
    calc
      G.map j (F.map j (sc k j f))
      _ = G.map j (sc k j (F.map k f)) := by rw [F.map_sc_eq_sc_map f j_lt_k]
      _ = sc k j (G.map k (F.map k f)) := G.map_sc_eq_sc_map (F.map k f) j_lt_k
  map_tg_eq_tg_map := by
    intro k j f j_lt_k
    calc
      G.map j (F.map j (tg k j f))
      _ = G.map j (tg k j (F.map k f)) := by rw [F.map_tg_eq_tg_map f j_lt_k]
      _ = tg k j (G.map k (F.map k f)) := G.map_tg_eq_tg_map (F.map k f) j_lt_k
  map_idm_eq_idm_map := by
    intro k j f j_lt_k
    calc
      G.map k (F.map k (idm k j f))
      _ = G.map k (idm k j (F.map j f)) := by rw [F.map_idm_eq_idm_map f j_lt_k]
      _ = idm k j (G.map j (F.map j f)) := G.map_idm_eq_idm_map (F.map j f) j_lt_k
  map_comp_eq_comp_map := by
    intro k j f g j_lt_k sc_tg_gf
    calc
      G.map k (F.map k (g ♯[k,j] f ← sc_tg_gf))
      _ = G.map k ((F.map k g) ♯[k,j] (F.map k f) ← F.comp_map j_lt_k sc_tg_gf) := by
        rw [F.map_comp_eq_comp_map j_lt_k sc_tg_gf]
      _ = (G.map k (F.map k g)) ♯[k,j] (G.map k (F.map k f)) ←
        G.comp_map j_lt_k (F.comp_map j_lt_k sc_tg_gf) :=
        G.map_comp_eq_comp_map j_lt_k (F.comp_map j_lt_k sc_tg_gf)

@[inherit_doc] scoped[HigherCategoryTheory.ManySorted] infixr:100 " ⊚ " => Functor.comp

/-- The identity functor on a many-sorted category `C`. It maps each morphism to itself and
trivially preserves all structure. -/
@[simp]
def id (C : index → Type u₁) [Category index C] : Functor index C C where
  map _ f := f

@[inherit_doc] scoped[HigherCategoryTheory.ManySorted] notation "idₘ" => Functor.id

end Functor

/-- A functor between many-sorted $n$-categories. -/
abbrev NFunctor (n : ℕ)
    (C : FinSucc n → Type u₁) [NCategory n C]
    (D : FinSucc n → Type u₂) [NCategory n D] :=
  Functor (FinSucc n) C D

/-- A functor between many-sorted $\omega$-categories. -/
abbrev OmegaFunctor
    (C : ℕ → Type u₁) [OmegaCategory C]
    (D : ℕ → Type u₂) [OmegaCategory D] :=
  Functor ℕ C D

end HigherCategoryTheory.ManySorted
