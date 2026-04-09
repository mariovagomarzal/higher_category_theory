/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Order.Category.NonemptyFinLinOrd
import HigherCategoryTheory.SingleSorted.Underlying.Functor

/-! **Important note**: This file is still work in progress. -/

universe u v

namespace HigherCategoryTheory.SingleSorted

-- TODO: Remove this definition when the original `UnderlyingFunctor` definition is ready to be used
-- in the definition of `UnderlyingConeFunctor`.
open CategoryTheory in
def UnderlyingFunctor' (n : ℕ) (m : Fin n) : NCat n ⥤ NCat m where
  obj C := Cat.of (cells m C)
  map {C D} F := F.underlying m

open CategoryTheory in
/-- TODO: Comment. -/
def UnderlyingConeFunctor : ℕᵒᵖ ⥤ CategoryTheory.Cat where
  obj n := CategoryTheory.Cat.of (NCat n.unop)
  -- TODO: Use `UnderlyingFunctor` from `HigherCategoryTheory.SingleSorted.Underlying.Functor` when
  -- ready to define the map on morphisms.
  map {n m} f :=
    if h_mn : m.unop = n.unop then
      eqToHom (by rw [h_mn])
    else
      CategoryTheory.Functor.toCatHom
        (UnderlyingFunctor' n.unop ⟨m.unop, Nat.lt_of_le_of_ne f.unop.le h_mn⟩)
  map_comp := by
    intro n m k f g
    have n_ge_m : n.unop ≥ m.unop := f.unop.le
    have m_ge_k : m.unop ≥ k.unop := g.unop.le
    -- We proceed by case analysis, trying the `omega` tactic first to discharge the cases where a
    -- contradiction arises from the inequalities between `n`, `m` and `k`.
    split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> (try omega)
    · simp
    · sorry -- A rewrite and a simp should do it.
    · sorry -- A rewrite and a simp should do it.
    · sorry -- The main case, where $n > m > k$.

end HigherCategoryTheory.SingleSorted
