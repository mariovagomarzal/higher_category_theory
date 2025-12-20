/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Order.Category.NonemptyFinLinOrd
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Cones
import HigherCategoryTheory.SingleSorted.Category
import HigherCategoryTheory.SingleSorted.Functor
import HigherCategoryTheory.SingleSorted.Cat
import HigherCategoryTheory.SingleSorted.Underlying.Basic

/-! TODO: Comment. -/

universe u v

namespace HigherCategoryTheory

open CategoryTheory

variable {n : ℕ} {obj : Type u} [S : SingleSortedNCategory n obj]

-- TODO: Maybe move this to the 'Basic' module of 'Underlying'.
/-- TODO: Comment. -/
instance {m : Fin n} : SingleSortedNCategory m (cells m obj) := S.underlying m

/-- TODO: Comment. -/
def UnderlyingFunctor (n : ℕ) (m : Fin n) : SingleSortedNCat n ⥤ SingleSortedNCat m where
  obj C := StructureFamily.of (cells m C)
  map {C D} F := F.underlying m

/-- TODO: Comment. -/
def UnderlyingCone : ℕᵒᵖ ⥤ Cat where
  obj n := Cat.of (SingleSortedNCat n.unop)
  map {n m} f :=
    if h_mn : m.unop = n.unop then
      h_mn ▸ 𝟭 (SingleSortedNCat m.unop)
    else
      UnderlyingFunctor n.unop ⟨m.unop, Nat.lt_of_le_of_ne f.unop.le h_mn⟩
  map_comp := by
    intro n m k f g
    by_cases h_mn : m.unop = n.unop
    · by_cases h_km : k.unop = m.unop
      · simp [h_mn, h_km]
        -- Goal is `𝟙 k = (𝟙 m) ≫ (𝟙 k)
        sorry
      · -- We have to get `k < m` from `k != m` and `g`
        sorry
    · by_cases h_km : k.unop = m.unop
      · -- We have to get `m < n` from `m != n` and `f`
        sorry
      · -- We have to get `k < m` and `m < n` from `k != m`, `m != n`, `f` and `g`
        sorry

end HigherCategoryTheory
