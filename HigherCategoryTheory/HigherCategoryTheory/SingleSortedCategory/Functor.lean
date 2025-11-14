/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
# Functors between single-sorted categories

This file defines the notion of functor between single-sorted categories, along with
the operations of functor composition and the identity functor. Functors between single-sorted
(1, 2, $n$, and ω) categories are referred to as single-sorted (1, 2, $n$, and ω) functors,
respectively.

## Notation

* `G ⊚ F`: Composition of functors `G` and `F`.
* `idₛ`: The identity functor.

## Implementation notes

The type class `CoeFun` allows treating a `F : SingleSortedFunctorFamily index C D` as a function,
writing `F f` instead of `F.map f` for the action of `F` on a morphism `f`.

Each single-sorted functor type is defined as an abbreviation of the more general
`SingleSortedFunctorFamily`, which is parameterized by the type of index used to define the
single-sorted category structure. This allows reusing the same definition and operations
for functors between single-sorted categories of different dimensions.
-/

universe u₁ u₂ u₃

namespace HigherCategoryTheory

/-- A `SingleSortedFunctorFamily` from `C` to `D` (both indexed by `index`) is a mapping that
preserves the single-sorted category structure. -/
@[ext]
structure SingleSortedFunctorFamily (index : Type) [NatIndex index]
    (C : Type u₁) (D : Type u₂)
    [SingleSortedCategoryStruct index C]
    [SingleSortedCategoryStruct index D] where
  /-- The underlying function on morphisms. -/
  map : C → D
  /-- The map preserves sources: `F (sc k f) = sc k (F f)`. -/
  map_sc_is_sc_map : ∀ (k : index) (f : C), map (sc k f) = sc k (map f)
  /-- The map preserves targets: `F (tg k f) = tg k (F f)`. -/
  map_tg_is_tg_map : ∀ (k : index) (f : C), map (tg k f) = tg k (map f)
  /-- If `g` and `f` are composable in `C`, then `F g` and `F f` are composable in `D`. An
  auxiliary method for defining `map_comp_is_comp_map`. -/
  comp_map {k : index} {f g : C} (comp_gf : sc_is_tg k g f) :
      sc_is_tg k (map g) (map f) := calc
    sc k (map g)
    _ = map (sc k g) := (map_sc_is_sc_map _ _).symm
    _ = map (tg k f) := congrArg map comp_gf
    _ = tg k (map f) := map_tg_is_tg_map _ _
  /-- The map preserves composition: `F (g ♯[k] f) = (F g) ♯[k] (F f)`. -/
  map_comp_is_comp_map : ∀ {k : index} {f g : C} (comp_gf : sc_is_tg k g f),
    map (g ♯[k] f ← comp_gf) = (map g) ♯[k] (map f) ← (comp_map comp_gf)

/-- Coercion allowing us to write `F f` instead of `F.map f` for the action of a functor `F`
on a morphism `f`. -/
instance CoeFun.instSingleSortedFunctorFamily {index : Type} [NatIndex index]
    {C : Type u₁} {D : Type u₂}
    [SingleSortedCategoryStruct index C]
    [SingleSortedCategoryStruct index D] :
    CoeFun (SingleSortedFunctorFamily index C D) fun _ ↦ C → D :=
  ⟨fun F ↦ F.map⟩

namespace SingleSortedFunctorFamily

/--
Composition of functors. Given functors `F : C → D` and `G : D → E`, their composite
`G ⊚ F : C → E` is defined by `(G ⊚ F) f = G (F f)`.

This operation preserves all the required functor properties: it preserves sources, targets,
and composition at each dimension.
-/
def comp {index : Type} [NatIndex index]
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [SingleSortedCategoryStruct index C]
    [SingleSortedCategoryStruct index D]
    [SingleSortedCategoryStruct index E]
    (G : SingleSortedFunctorFamily index D E)
    (F : SingleSortedFunctorFamily index C D) :
    SingleSortedFunctorFamily index C E where
  map := G ∘ F
  map_sc_is_sc_map := by
    intro k f
    calc
      (G ∘ F) (sc k f)
      _ = G (F (sc k f)) := rfl
      _ = G (sc k (F f)) := congrArg G (F.map_sc_is_sc_map _ _)
      _ = sc k (G (F f)) := G.map_sc_is_sc_map _ _
  map_tg_is_tg_map := by
    intro k f
    calc
      (G ∘ F) (tg k f)
      _ = G (F (tg k f)) := rfl
      _ = G (tg k (F f)) := congrArg G (F.map_tg_is_tg_map _ _)
      _ = tg k (G (F f)) := G.map_tg_is_tg_map _ _
  map_comp_is_comp_map := by
    intro k f g comp_gf
    calc
      (G ∘ F) (g ♯[k] f ← comp_gf)
      _ = G (F (g ♯[k] f ← comp_gf)) := rfl
      _ = G ((F g) ♯[k] (F f) ← (F.comp_map comp_gf)) :=
        congrArg G (F.map_comp_is_comp_map comp_gf)
      _ = (G (F g)) ♯[k] (G (F f)) ← (G.comp_map (F.comp_map comp_gf)) :=
        G.map_comp_is_comp_map (F.comp_map comp_gf)

@[inherit_doc]
scoped[HigherCategoryTheory] infixr:80 " ⊚ " => SingleSortedFunctorFamily.comp

/-- The identity functor on a single-sorted category `C`. It maps each morphism to itself and
trivially preserves all structure. -/
def id {index : Type} [NatIndex index]
    {C : Type u₁}
    [SingleSortedCategoryStruct index C] :
    SingleSortedFunctorFamily index C C where
  map := fun x ↦ x
  map_sc_is_sc_map _ _ := rfl
  map_tg_is_tg_map _ _ := rfl
  map_comp_is_comp_map _ := rfl

@[inherit_doc]
scoped[HigherCategoryTheory] notation "idₛ" => SingleSortedFunctorFamily.id

end SingleSortedFunctorFamily

/-- A `SingleSortedFunctor` is a functor between single-sorted categories. -/
abbrev SingleSortedFunctor (C : Type u₁) (D : Type u₂)
    [SingleSortedCategory C]
    [SingleSortedCategory D] :=
  SingleSortedFunctorFamily (Fin 1) C D

/-- A `SingleSorted2Functor` is a functor between single-sorted 2-categories. -/
abbrev SingleSorted2Functor (C : Type u₁) (D : Type u₂)
    [SingleSorted2Category C]
    [SingleSorted2Category D] :=
  SingleSortedFunctorFamily (Fin 2) C D

/-- A `SingleSortedNFunctor` is a functor between single-sorted $n$-categories. -/
abbrev SingleSortedNFunctor (n : ℕ) (C : Type u₁) (D : Type u₂)
    [SingleSortedNCategory n C]
    [SingleSortedNCategory n D] :=
  SingleSortedFunctorFamily (Fin n) C D

/-- A `SingleSortedOmegaFunctor` is a functor between single-sorted $\omega$-categories. -/
abbrev SingleSortedOmegaFunctor (C : Type u₁) (D : Type u₂)
    [SingleSortedOmegaCategory C]
    [SingleSortedOmegaCategory D] :=
  SingleSortedFunctorFamily ℕ C D

end HigherCategoryTheory
