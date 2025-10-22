/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
TODO: Document the file.
-/

universe u v

namespace HigherCategoryTheory

structure SingleSortedFunctorFamily (C : Type u) (D : Type v)
    (index : Type) [NatIndex index]
    [SingleSortedCategoryFamily C index]
    [SingleSortedCategoryFamily D index] where
  map : C → D
  map_sc_is_sc_map : ∀ {i : index} {f : C}, map (sc i f) = sc i (map f)
  map_tg_is_tg_map : ∀ {i : index} {f : C}, map (tg i f) = tg i (map f)
  comp_map {i : index} {f g : C} (comp_gf : sc_is_tg i g f) :
    sc_is_tg i (map g) (map f) := by sorry
  map_comp_is_comp_map : ∀ {i : index} {f g : C} (comp_gf : sc_is_tg i g f),
    map (g ♯[i] f ← comp_gf) = (map g) ♯[i] (map f) ← (comp_map comp_gf)

@[ext]
structure SingleSortedFunctor (C : Type u) (D : Type v)
    [SingleSortedCategory C]
    [SingleSortedCategory D]
    extends SingleSortedFunctorFamily C D (Fin 1)

@[ext]
structure SingleSorted2Functor (C : Type u) (D : Type v)
    [SingleSorted2Category C]
    [SingleSorted2Category D]
    extends SingleSortedFunctorFamily C D (Fin 2)

@[ext]
structure SingleSortedNFunctor (C : Type u) (D : Type v) (n : Nat)
    [SingleSortedNCategory C n]
    [SingleSortedNCategory D n]
    extends SingleSortedFunctorFamily C D (Fin n)

@[ext]
structure SingleSortedOmegaFunctor (C : Type u) (D : Type v)
    [SingleSortedOmegaCategory C]
    [SingleSortedOmegaCategory D]
    extends SingleSortedFunctorFamily C D Nat

-- TODO: Define composition and identity functors, and prove the functor laws.
namespace SingleSortedFunctorFamily

def comp := Empty

def id := Empty

theorem assoc : True := by sorry

theorem id_left : True := by sorry

theorem id_right : True := by sorry

end SingleSortedFunctorFamily

end HigherCategoryTheory
