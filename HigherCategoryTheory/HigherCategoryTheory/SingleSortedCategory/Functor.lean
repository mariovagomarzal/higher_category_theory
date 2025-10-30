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
* `idₛₛ`: The identity functor.

## Implementation notes

The type class `CoeFun` allows treating a `F : SingleSortedFunctorFamily C D index` as a function,
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
structure SingleSortedFunctorFamily (C : Type u₁) (D : Type u₂)
    (index : Type) [NatIndex index]
    [SingleSortedCategoryStruct C index]
    [SingleSortedCategoryStruct D index] where
  /-- The underlying function on morphisms. -/
  map : C → D
  /-- The map preserves sources: `F (sc i f) = sc i (F f)`. -/
  map_sc_is_sc_map : ∀ (i : index) (f : C), map (sc i f) = sc i (map f)
  /-- The map preserves targets: `F (tg i f) = tg i (F f)`. -/
  map_tg_is_tg_map : ∀ (i : index) (f : C), map (tg i f) = tg i (map f)
  /-- If `g` and `f` are composable in `C`, then `F g` and `F f` are composable in `D`. An
  auxiliary method for defining `map_comp_is_comp_map`. -/
  comp_map {i : index} {f g : C} (comp_gf : sc_is_tg i g f) :
      sc_is_tg i (map g) (map f) := calc
    sc i (map g)
    _ = map (sc i g) := (map_sc_is_sc_map _ _).symm
    _ = map (tg i f) := congrArg map comp_gf
    _ = tg i (map f) := map_tg_is_tg_map _ _
  /-- The map preserves composition: `F (g ♯[i] f) = (F g) ♯[i] (F f)`. -/
  map_comp_is_comp_map : ∀ {i : index} {f g : C} (comp_gf : sc_is_tg i g f),
    map (g ♯[i] f ← comp_gf) = (map g) ♯[i] (map f) ← (comp_map comp_gf)

namespace SingleSortedFunctorFamily

/-- Coercion allowing us to write `F f` instead of `F.map f` for the action of a functor `F`
on a morphism `f`. -/
instance {C : Type u₁} {D : Type u₂} {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct C index]
    [SingleSortedCategoryStruct D index] :
    CoeFun (SingleSortedFunctorFamily C D index) (fun _ => C → D) :=
  ⟨fun F ↦ F.map⟩

/-- Composition of functors. Given functors `F : C → D` and `G : D → E`, their composite
`G ⊚ F : C → E` is defined by `(G ⊚ F) f = G (F f)`.

This operation preserves all the required functor properties: it preserves sources, targets,
and composition at each dimension. -/
def comp {C : Type u₁} {D : Type u₂} {E : Type u₃}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct C index]
    [SingleSortedCategoryStruct D index]
    [SingleSortedCategoryStruct E index]
    (G : SingleSortedFunctorFamily D E index)
    (F : SingleSortedFunctorFamily C D index) :
    SingleSortedFunctorFamily C E index where
  map := G ∘ F
  map_sc_is_sc_map := by
    intro i f
    calc
      (G ∘ F) (sc i f)
      _ = G (F (sc i f)) := rfl
      _ = G (sc i (F f)) := congrArg G (F.map_sc_is_sc_map _ _)
      _ = sc i (G (F f)) := G.map_sc_is_sc_map _ _
  map_tg_is_tg_map := by
    intro i f
    calc
      (G ∘ F) (tg i f)
      _ = G (F (tg i f)) := rfl
      _ = G (tg i (F f)) := congrArg G (F.map_tg_is_tg_map _ _)
      _ = tg i (G (F f)) := G.map_tg_is_tg_map _ _
  map_comp_is_comp_map := by
    intro i f g comp_gf
    calc
      (G ∘ F) (g ♯[i] f ← comp_gf)
      _ = G (F (g ♯[i] f ← comp_gf)) := rfl
      _ = G ((F g) ♯[i] (F f) ← (F.comp_map comp_gf)) :=
        congrArg G (F.map_comp_is_comp_map comp_gf)
      _ = (G (F g)) ♯[i] (G (F f)) ← (G.comp_map (F.comp_map comp_gf)) :=
        G.map_comp_is_comp_map (F.comp_map comp_gf)

/-- The identity functor on a single-sorted category `C`. It maps each morphism to itself and
trivially preserves all structure. -/
def id {C : Type u₁}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct C index] :
    SingleSortedFunctorFamily C C index where
  map := fun x ↦ x
  map_sc_is_sc_map _ _ := rfl
  map_tg_is_tg_map _ _ := rfl
  map_comp_is_comp_map _ := rfl

end SingleSortedFunctorFamily

scoped infixr:80 " ⊚ " => SingleSortedFunctorFamily.comp
scoped notation "idₛₛ" => SingleSortedFunctorFamily.id

/-- A `SingleSortedFunctor` is a functor between single-sorted categories. -/
abbrev SingleSortedFunctor (C : Type u₁) (D : Type u₂)
    [SingleSortedCategory C]
    [SingleSortedCategory D] :=
  SingleSortedFunctorFamily C D (Fin 1)

/-- A `SingleSorted2Functor` is a functor between single-sorted 2-categories. -/
abbrev SingleSorted2Functor (C : Type u₁) (D : Type u₂)
    [SingleSorted2Category C]
    [SingleSorted2Category D] :=
  SingleSortedFunctorFamily C D (Fin 2)

/-- A `SingleSortedNFunctor` is a functor between single-sorted $n$-categories. -/
abbrev SingleSortedNFunctor (C : Type u₁) (D : Type u₂) (n : Nat)
    [SingleSortedNCategory C n]
    [SingleSortedNCategory D n] :=
  SingleSortedFunctorFamily C D (Fin n)

/-- A `SingleSortedOmegaFunctor` is a functor between single-sorted $\omega$-categories. -/
abbrev SingleSortedOmegaFunctor (C : Type u₁) (D : Type u₂)
    [SingleSortedOmegaCategory C]
    [SingleSortedOmegaCategory D] :=
  SingleSortedFunctorFamily C D Nat

end HigherCategoryTheory
