/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
TODO: Document the file.
-/

universe u₁ u₂ u₃

namespace HigherCategoryTheory

@[ext]
structure SingleSortedFunctorFamily (C : Type u₁) (D : Type u₂)
    (index : Type) [NatIndex index]
    [SingleSortedCategoryStruct C index]
    [SingleSortedCategoryStruct D index] where
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

namespace SingleSortedFunctorFamily

instance {C : Type u₁} {D : Type u₂} {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct C index]
    [SingleSortedCategoryStruct D index] :
    CoeFun (SingleSortedFunctorFamily C D index) (fun _ => C → D) :=
  ⟨fun F ↦ F.map⟩

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
      _ = G (sc i (F f)) := congrArg G (F.map_sc_is_sc_map)
      _ = sc i (G (F f)) := G.map_sc_is_sc_map
  map_tg_is_tg_map := by
    intro i f
    calc
      (G ∘ F) (tg i f)
      _ = G (F (tg i f)) := rfl
      _ = G (tg i (F f)) := congrArg G (F.map_tg_is_tg_map)
      _ = tg i (G (F f)) := G.map_tg_is_tg_map
  map_comp_is_comp_map := by
    intro i f g comp_gf
    calc
      (G ∘ F) (g ♯[i] f ← comp_gf)
      _ = G (F (g ♯[i] f ← comp_gf)) := rfl
      _ = G ((F g) ♯[i] (F f) ← (F.comp_map comp_gf)) :=
        congrArg G (F.map_comp_is_comp_map comp_gf)
      _ = (G (F g)) ♯[i] (G (F f)) ← (G.comp_map (F.comp_map comp_gf)) :=
        G.map_comp_is_comp_map (F.comp_map comp_gf)

def id {C : Type u₁}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct C index] :
    SingleSortedFunctorFamily C C index where
  map := fun x ↦ x
  map_sc_is_sc_map := rfl
  map_tg_is_tg_map := rfl
  map_comp_is_comp_map _ := rfl

end SingleSortedFunctorFamily

scoped infixr:80 " ⊚ " => SingleSortedFunctorFamily.comp
scoped notation "idₛₛ" => SingleSortedFunctorFamily.id

theorem assoc {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₁}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct C index]
    [SingleSortedCategoryStruct D index]
    [SingleSortedCategoryStruct E index]
    [SingleSortedCategoryStruct F index]
    (F₁ : SingleSortedFunctorFamily C D index)
    (F₂ : SingleSortedFunctorFamily D E index)
    (F₃ : SingleSortedFunctorFamily E F index) :
    F₃ ⊚ F₂ ⊚ F₁ = (F₃ ⊚ F₂) ⊚ F₁ := rfl

theorem id_left {C : Type u₁} {D : Type u₂}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct C index]
    [SingleSortedCategoryStruct D index]
    (F : SingleSortedFunctorFamily C D index) :
    idₛₛ ⊚ F = F := rfl

theorem id_right {C : Type u₁} {D : Type u₂}
    {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct C index]
    [SingleSortedCategoryStruct D index]
    (F : SingleSortedFunctorFamily C D index) :
    F ⊚ idₛₛ = F := rfl

structure SingleSortedFunctor (C : Type u₁) (D : Type u₂)
    [SingleSortedCategory C]
    [SingleSortedCategory D]
    extends SingleSortedFunctorFamily C D (Fin 1)

structure SingleSorted2Functor (C : Type u₁) (D : Type u₂)
    [SingleSorted2Category C]
    [SingleSorted2Category D]
    extends SingleSortedFunctorFamily C D (Fin 2)

structure SingleSortedNFunctor (C : Type u₁) (D : Type u₂) (n : Nat)
    [SingleSortedNCategory C n]
    [SingleSortedNCategory D n]
    extends SingleSortedFunctorFamily C D (Fin n)

structure SingleSortedOmegaFunctor (C : Type u₁) (D : Type u₂)
    [SingleSortedOmegaCategory C]
    [SingleSortedOmegaCategory D]
    extends SingleSortedFunctorFamily C D Nat

end HigherCategoryTheory
