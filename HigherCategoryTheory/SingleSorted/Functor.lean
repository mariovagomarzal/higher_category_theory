/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category

/-!
# Functors between single-sorted categories

This file defines functors between single-sorted categories and establishes the basic categorical
structure of functor composition and identity.

A functor between single-sorted categories is a structure-preserving map that uniformly respects
sources, targets, and composition at all dimensions. Unlike traditional category theory where
functors act on objects and morphisms separately, in the single-sorted presentation a functor is
simply a function on the underlying type that preserves the structure.

## Main definitions

* `Functor`: A structure-preserving map between single-sorted categories, consisting of
  a function that preserves sources, targets, and composition at each dimension.
* `NFunctor`: Functors between single-sorted $n$-categories.
* `OmegaFunctor`: Functors between single-sorted $\omega$-categories.

## Notation

* `F f`: Application of functor `F` to morphism `f` (via coercion from `F.map f`).
* `G ⊚ F`: Composition of functors `G` and `F`.
* `idₛ C`: The identity functor on a single-sorted category `C`.
-/

universe u₁ u₂ u₃

namespace HigherCategoryTheory.SingleSorted

/--
A functor between single-sorted categories.

A `Functor Index C D` is a structure-preserving map from a single-sorted category `C` to
a single-sorted category `D`. It consists of:
* A function `map : C → D` on morphisms.
* Proofs that `map` preserves sources, targets, and composition at each dimension.
-/
structure Functor (Index : Type) [Preorder Index] (C : Type u₁) [Category Index C]
    (D : Type u₂) [Category Index D] where
  /-- The underlying function on morphisms. -/
  map : C → D
  /-- The map preserves sources. -/
  map_sc_eq_sc_map : ∀ (k : Index) (f : C), map (sc k f) = sc k (map f) := by hcat_disch
  /-- The map preserves targets. -/
  map_tg_eq_tg_map : ∀ (k : Index) (f : C), map (tg k f) = tg k (map f) := by hcat_disch
  /-- If `g` and `f` are composable in `C`, then `F g` and `F f` are composable in `D`. This is an
  auxiliary method for defining `map_comp_eq_comp_map`. -/
  protected comp_map {k : Index} {f g : C} (sc_tg_gf : sc_is_tg k g f) :
      sc_is_tg k (map g) (map f) := calc
    sc k (map g)
    _ = map (sc k g) := (map_sc_eq_sc_map k g).symm
    _ = map (tg k f) := by rw [sc_tg_gf]
    _ = tg k (map f) := map_tg_eq_tg_map k f
  /-- The map preserves composition. -/
  map_comp_eq_comp_map : ∀ {k : Index} {f g : C} (sc_tg_gf : sc_is_tg k g f),
      map (g ♯[k] f ← sc_tg_gf) = (map g) ♯[k] (map f) ← (comp_map sc_tg_gf) := by
    hcat_disch

-- Use `Functor` axioms as simp lemmas.
open Functor in
attribute [simp] map_sc_eq_sc_map map_tg_eq_tg_map map_comp_eq_comp_map

namespace Functor

variable {Index : Type} [Preorder Index]
  {C : Type u₁} [Category Index C]
  {D : Type u₂} [Category Index D]
  {E : Type u₃} [Category Index E]

/-- Coercion allowing us to write `F f` instead of `F.map f` for the action of a functor `F` on a
morphism `f`. -/
instance : CoeFun (Functor Index C D) fun _ ↦ C → D := ⟨fun F ↦ F.map⟩

attribute [coe] Functor.map

/-- Composition of functors. Given functors `F : C → D` and `G : D → E`, their composite `G ⊚ F : C
→ E` is defined by `(G ⊚ F) f = G (F f)`. This operation preserves all the required functor
properties. -/
@[simp]
def comp (G : Functor Index D E) (F : Functor Index C D) :
    Functor Index C E where
  map f := G (F f)
  map_sc_eq_sc_map := by
    intro k f
    calc
      G (F (sc k f))
      _ = G (sc k (F f)) := by rw [F.map_sc_eq_sc_map k f]
      _ = sc k (G (F f)) := G.map_sc_eq_sc_map k (F f)
  map_tg_eq_tg_map := by
    intro k f
    calc
      G (F (tg k f))
      _ = G (tg k (F f)) := by rw [F.map_tg_eq_tg_map k f]
      _ = tg k (G (F f)) := G.map_tg_eq_tg_map k (F f)
  map_comp_eq_comp_map := by
    intro k f g sc_tg_gf
    calc
      G (F (g ♯[k] f ← sc_tg_gf))
      _ = G ((F g) ♯[k] (F f) ← F.comp_map sc_tg_gf) := by rw [F.map_comp_eq_comp_map sc_tg_gf]
      _ = (G (F g)) ♯[k] (G (F f)) ← G.comp_map (F.comp_map sc_tg_gf) :=
        G.map_comp_eq_comp_map (F.comp_map sc_tg_gf)

@[inherit_doc] scoped[HigherCategoryTheory.SingleSorted] infixr:100 " ⊚ " => Functor.comp

/-- The identity functor on a single-sorted category `C`. It maps each morphism to itself and
trivially preserves all structure. -/
@[simp]
def id (C : Type u₁) [Category Index C] : Functor Index C C where
  map f := f

@[inherit_doc] scoped[HigherCategoryTheory.SingleSorted] notation "idₛ" => Functor.id

end Functor

/-- A functor between single-sorted $n$-categories. -/
abbrev NFunctor (n : ℕ)
    (C : Type u₁) [NCategory n C]
    (D : Type u₂) [NCategory n D] :=
  Functor (Fin n) C D

/-- A functor between single-sorted $\omega$-categories. -/
abbrev OmegaFunctor
    (C : Type u₁) [OmegaCategory C]
    (D : Type u₂) [OmegaCategory D] :=
  Functor ℕ C D

end HigherCategoryTheory.SingleSorted
