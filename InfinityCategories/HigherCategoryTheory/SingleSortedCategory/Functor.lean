/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
TODO: Document the file.
-/

universe u v w

namespace HigherCategoryTheory

structure SingleSortedFunctorFamily (C : Type u) (D : Type v)
    (index : Type) [NatIndex index]
    [SingleSortedCategoryFamily C index]
    [SingleSortedCategoryFamily D index] where
  map : C → D
  map_sc_is_sc_map : ∀ {i : index} {f : C}, map (sc i f) = sc i (map f)
  map_tg_is_tg_map : ∀ {i : index} {f : C}, map (tg i f) = tg i (map f)
  comp_map {i : index} {f g : C} (comp_gf : sc_is_tg i g f) :
      sc_is_tg i (map g) (map f) := calc
    sc i (map g)
    _ = map (sc i g) := map_sc_is_sc_map.symm
    _ = map (tg i f) := congrArg map comp_gf
    _ = tg i (map f) := map_tg_is_tg_map
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

namespace SingleSortedFunctorFamily

def comp {C : Type u} {D : Type v} {E : Type w}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily C index]
    [SingleSortedCategoryFamily D index]
    [SingleSortedCategoryFamily E index]
    (F : SingleSortedFunctorFamily C D index)
    (G : SingleSortedFunctorFamily D E index) :
    SingleSortedFunctorFamily C E index where
  map := G.map ∘ F.map
  map_sc_is_sc_map := by sorry
  map_tg_is_tg_map := by sorry
  map_comp_is_comp_map := by sorry

def id {C : Type u}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily C index] :
    SingleSortedFunctorFamily C C index where
  map := fun x => x
  map_sc_is_sc_map := by intros; rfl
  map_tg_is_tg_map := by intros; rfl
  map_comp_is_comp_map := by intros; rfl

theorem assoc {C : Type u} {D : Type v} {E : Type w} {F : Type u}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily C index]
    [SingleSortedCategoryFamily D index]
    [SingleSortedCategoryFamily E index]
    [SingleSortedCategoryFamily F index]
    (F1 : SingleSortedFunctorFamily C D index)
    (F2 : SingleSortedFunctorFamily D E index)
    (F3 : SingleSortedFunctorFamily E F index) :
    comp (comp F1 F2) F3 = comp F1 (comp F2 F3) := by sorry

theorem id_left {C : Type u} {D : Type v}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily C index]
    [SingleSortedCategoryFamily D index]
    (F : SingleSortedFunctorFamily C D index) :
    comp (id) F = F := by sorry

theorem id_right {C : Type u} {D : Type v}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryFamily C index]
    [SingleSortedCategoryFamily D index]
    (F : SingleSortedFunctorFamily C D index) :
    comp F (id) = F := by sorry

end SingleSortedFunctorFamily

end HigherCategoryTheory
